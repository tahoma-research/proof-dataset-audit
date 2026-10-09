import json
import shutil
import tomllib

import pytest
from helpers import PY, REPO, in_unit, legs_spec, write_policy

pytestmark = [pytest.mark.integration, pytest.mark.slow]

SCRIPT = """
import json, os, shutil, sys
from datetime import date, timedelta
from pathlib import Path
from ledger import REPO, aggregate, confine, constants, envbuild, gatefile, legs, policy
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
spec = json.loads(Path(sys.argv[2]).read_text())
Path(spec["logs"]).mkdir(parents=True, exist_ok=True)
(tmp := pol.root / "tmp" / Path(spec["logs"]).parent.name).mkdir(parents=True, exist_ok=True)
os.environ["TMPDIR"] = str(tmp)
consts = constants.load(REPO)
consts.published["status"]["legacy"] = "environment-unavailable"  # pin only: the D+43 cut needs no legacy leg
run = legs.prepare(pol, consts, Path(spec["work"]), Path(spec["results"]), Path(spec["logs"]), ("pin",))
pairs = [pair for pair, _, _ in spec["cases"]]
legs.pass1(run, pairs, ceiling_s=1e9)
d0 = date(2026, 11, 2)
gatefile.append(pol, "d0", "met", "operator", "pin commit", d0)
states = [aggregate.step(run, pairs, d0 + timedelta(days=day), eb_s=600, mb_s=60, e_s=600, m_s=60)
          for day in (44, 45, 46)]
walks = {}
for constant in ("helperC", "Nat.add", "orphan"):
    call = envbuild.lake(pol, consts, "pin", run.trees["pin"].toolchain, pol.root / "env/pin", "env",
                         str(run.trees["pin"].audit), "walk", "--module", "Aggregate", "--constant", constant,
                         "--members-file", str(run.results / "membership.txt"))
    walks[constant] = json.loads(confine.run(**call | {"writes": [], "timeout_s": 600}).output.splitlines()[-1])
print(json.dumps({"states": states, "progress": run.progress.data, "walks": walks, "gates": gatefile.rows(pol),
                  "replay": (Path(spec["logs"]) / "aggregate-replay.log").read_text()}))
shutil.rmtree(tmp)
"""
PAIRS = {  # each compiles alone; e's def collides with d's inside the aggregate, s plants an Init/ shadowing the
    # toolchain's when built in the aggregate, and f leaves g in its namespace
    "a": "theorem a__p0 (x : ℝ) (h : 0 < x) : 0 < x + 1 := by\n  exact add_pos h one_pos\n",
    "b": "def helperC : ℕ := 1\ntheorem b__p0 : helperC = 1 := by\n  rfl\n",
    "c": "def orphan : ℕ := 3\ntheorem c__p0 : (2:ℕ) + 2 = 4 := by\n  norm_num\n",
    "d": "def dup : ℕ := 1\ntheorem d__p0 : dup = 1 := by\n  rfl\n",
    "e": "def dup : ℕ := 2\ntheorem e__p0 : dup = 2 := by\n  rfl\n",
    "s": "open Lean Elab Command in\nrun_cmd do\n  if (← getMainModule) == `Aggregate then\n"
         "    IO.FS.createDirAll \".lake/build/lib/lean/Init\"\ntheorem s__p0 : True := trivial\n",
    "f": "theorem f__p0 (n : ℕ) : n + 0 = n := by\n  simp\nnamespace Leak\n",
    "g": "theorem g__p0 : (1:ℕ) = 1 := rfl\n",
}


def test_fresh_v_prints_replaying_line(dev_root, tmp_path):
    """Constructed pairs under the dev overlay, pass 1 at the pin, then three D+44 nights in a user unit. The first
    builds the aggregate with `lake --no-cache build Aggregate`; the pair that fails only there, an error inside
    its line range, is removed as harness-error. The second builds the other seven; the pair whose theorem the
    namespace left open by the one before it renamed is missing from the aggregate's audit, and is removed as
    harness-error too. The third builds the other six, the cross-pass comparison finds no mismatch, and
    `leanchecker -v --fresh` exits 0 printing its replaying line: replay-returned. The Init/ one member plants under
    the build output each night is removed and recorded. The dependency walk over the built aggregate attributes a
    helper to the member using it, and refuses an imported constant and one no member reaches."""
    # covers: test_built_with_lake_build
    header = tomllib.loads((dev_root / "dev-overlay.toml").read_text())["header"]
    args, scratch = legs_spec(dev_root, tmp_path, [(f"{k}__p0", header + text, None, {}) for k, text in PAIRS.items()])
    (scratch / "public/gates").mkdir(parents=True)
    shutil.copy(REPO / "templates/GATES.md.tmpl", scratch / "public/gates/GATES.md")
    write_policy(args[0], dev_root, public_tree=str(scratch / "public"))
    try:
        ran = in_unit(PY, "-c", SCRIPT, *args, env={"LEDGER_DEV_ROOT": dev_root}, timeout=3600)
        assert ran.code == 0, ran.err[-3000:]
        out = json.loads(ran.out)
        agg = out["progress"]["aggregate"]
        assert out["states"] == ["build-pending", "build-pending", "replay-returned"] and agg["reruns_used"] == 2
        elab, missing = sorted(out["progress"]["harness_overrides"].values(), key=lambda o: o["source"])
        assert elab["source"] == "aggregate-elab" and "dup" in elab["detail"]
        assert (missing["source"], missing["detail"]) == ("crosspass-d44", "elaboration")
        assert [r["cause"] for r in agg["removals"]] == ["harness-error"] * 2 and "replay_overrides" not in out["progress"]
        members = (scratch / "results/membership.txt").read_text().splitlines()
        assert members[0].startswith("# members=6 ")
        assert members[1:] == ["a__p0", "b__p0", "c__p0", "d__p0", "s__p0", "f__p0"]
        assert agg["last_build"]["planted"] == ["lib/lean/Init"]
        assert not (dev_root / "env/pin/.lake/build/lib/lean/Init").exists()
        assert "replaying Aggregate with --fresh" in out["replay"] and agg["last_replay"]["exit"] == 0
        assert agg["last_replay"]["max_rss_kb"] > 0
        assert out["walks"] == {"helperC": {"member": "b__p0"}, "Nat.add": {"member": None, "reason": "imported"},
                                "orphan": {"member": None, "reason": "none"}}
        assert [row[1:3] for row in out["gates"]] == [["d0", "met"], ["d43", "met"]]
    finally:
        shutil.rmtree(scratch)
