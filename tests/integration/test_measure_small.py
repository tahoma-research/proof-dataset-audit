import json
import shutil
import tomllib
from pathlib import Path

import pytest
from helpers import PY, REPO, in_unit, legs_spec, write_policy

pytestmark = [pytest.mark.integration, pytest.mark.slow]

SCRIPT = """
import dataclasses, json, os, shutil, sys
from datetime import date
from pathlib import Path
from ledger import REPO, confine, constants, gatefile, measure, policy, preflight
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
spec = json.loads(Path(sys.argv[2]).read_text())
Path(spec["logs"]).mkdir(parents=True, exist_ok=True)
(tmp := pol.root / "tmp" / Path(spec["logs"]).parent.name).mkdir(parents=True, exist_ok=True)
os.environ["TMPDIR"] = str(tmp)
preflight.CHECKS = ()  # the command's run lock and host floors, not this measurement's
consts = dataclasses.replace(constants.load(REPO), repo=Path(spec["code"]))  # the outcome writes there
for gate, verdict in (("legacy-cache-probe", "serves"), ("legacy-collector", "elaborates")):  # no legacy probe here
    gatefile.append(pol, gate, verdict, "pipeline", "recorded", date(2026, 11, 16))
found = measure.d14(pol, consts, Path(spec["work"]), Path(spec["results"]), Path(spec["logs"]), date(2026, 11, 16))
print(json.dumps({"found": found, "gates": gatefile.rows(pol),
                  "files": sorted(path.name for path in (pol.root / measure.DIR).iterdir())}))
shutil.rmtree(tmp)
"""
PAIRS = {  # two compile clean under the dev overlay; the third fails to elaborate
    "a": "theorem a__p0 (x : ℝ) (h : 0 < x) : 0 < x + 1 := by\n  exact add_pos h one_pos\n",
    "b": "theorem b__p0 : (2:ℕ) + 2 = 4 := by\n  norm_num\n",
    "c": "theorem c__p0 : (1:ℕ) = 2 := by\n  rfl\n",
}


def test_dry_run_small_target_all_figures_one_outcome(dev_root, tmp_path):
    """07 § C9 done-bar 3, in a user unit under the dev overlay: the D+14 measurement over three constructed pairs,
    against the small-target pin tree. The proof-1b fixture's replay is timed, inside its 4-hour line; the serial
    pilot attempts all three pairs; the baseline aggregate (the toy alone) and the pilot aggregate (the toy and the
    two clean pairs) are built and replayed to completion, so every figure is measured and one outcome is written,
    to a scratch gate file and a copy of the constants; the development root's own gate file is never written."""
    header = tomllib.loads((dev_root / "dev-overlay.toml").read_text())["header"]
    args, scratch = legs_spec(dev_root, tmp_path, [(f"{k}__p0", header + text, None, {}) for k, text in PAIRS.items()])
    (scratch / "public/gates").mkdir(parents=True)
    shutil.copy(REPO / "templates/GATES.md.tmpl", scratch / "public/gates/GATES.md")
    for rel in ("recipe", "classifier"):  # the run reads both through the constants' repo
        shutil.copytree(REPO / rel, scratch / "code" / rel)
    spec = json.loads(args[1].read_text()) | {"code": str(scratch / "code")}
    Path(spec["work"], "assembled.jsonl").write_text("".join(json.dumps(pair) + "\n" for pair, _, _ in spec["cases"]))
    args[1].write_text(json.dumps(spec))
    write_policy(args[0], dev_root, public_tree=str(scratch / "public"))
    real = dev_root / "gates/GATES.md"
    before = real.read_bytes() if real.exists() else None
    made = [dev_root / rel for rel in ("fixtures-src/proof1b", "fixtures-run/proof1b", "fixtures-run/env/proof1b",
                                       "fixtures-run/tmp/proof1b")]
    shutil.copytree(REPO / "fixtures/proof1b", made[0])  # as stage copies it beside the public tree
    try:
        ran = in_unit(PY, "-c", SCRIPT, *args, env={"LEDGER_DEV_ROOT": dev_root}, timeout=3600)
        assert ran.code == 0, ran.err[-3000:]
        out = json.loads(ran.out)
        found = out["found"]
        assert found["outcome"] in {"replay-unavailable", "cap-reset", "rescope", "default"}
        assert found["M"] == 2 and found["label"] == "extrapolated"
        assert all(found[key] is not None for key in ("S", "E", "T", "m", "P", "Eb", "Tb", "mb", "B")), found
        assert out["files"] == ["baseline.json", "pairs.json", "pilot.json", "projection.json", "proof1b.json"]
        assert 0 < json.loads((dev_root / "measure/d14/proof1b.json").read_text())["timing_s"] < 4 * 3600
        rows = [tuple(row[1:3]) for row in out["gates"]][2:]
        assert rows == [("rescope", f"cut_n={found['N']}")] * bool(found["N"]) + [("d14-outcome", found["outcome"]),
                                                                                   ("d14", "met")]
        assert (real.read_bytes() if real.exists() else None) == before
    finally:
        for path in (scratch, *made):
            if path.exists():
                shutil.rmtree(path)
        if (measured := dev_root / "measure/d14").exists():
            shutil.rmtree(measured)
