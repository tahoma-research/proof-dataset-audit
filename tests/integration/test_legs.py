import json
import os
import re
import shutil
import subprocess
import time
import tomllib
from pathlib import Path

import pytest
from helpers import LEGS, PY, in_unit, legs_spec, run_legs, unit_setenv

from ledger import confine, diagnostics

pytestmark = pytest.mark.integration

PLANT = ("open Lean Elab in\nrun_elab withOptions (debug.skipKernelTC.set · true) <| addDecl (.thmDecl { name := "
         "`planted_false, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })\n"
         "theorem plant__p0 : False := by\n  exact planted_false\n")
# A theorem the compile adds unchecked and the replay must check: a sum of 300 powers, each a kernel big-number
# computation; the replay is killed long before it ends.
RESIDUE = sum(pow(b, 16000000, 13) for b in range(3, 303)) % 13
SLOW = ("open Lean in\nrun_elab do\n  let sum := (List.range 300).foldl (fun acc b => mkApp2 (mkConst ``Nat.add) acc "
        "(mkApp2 (mkConst ``Nat.pow) (mkNatLit (b + 3)) (mkNatLit 16000000))) (mkNatLit 0)\n  let type := mkApp3 "
        f"(mkConst ``Eq [1]) (mkConst ``Nat) (mkApp2 (mkConst ``Nat.mod) sum (mkNatLit 13)) (mkNatLit {RESIDUE})\n"
        "  withOptions (debug.skipKernelTC.set · true) <| addDecl (.thmDecl { name := `slowReplay, levelParams := [], "
        f"type, value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit {RESIDUE}) }})\n"
        "theorem slow__p0 : True := by\n  trivial\n")
# An unknown identifier, after a message that prints the tree's absolute path, which the leg rewrites.
UNKNOWN = "#eval IO.currentDir\ntheorem unknown__p0 : (1:ℕ) = 1 := by\n  exact no_such_lemma\n"
ACCEPTED = "theorem accepted__p0 (x : ℝ) (h : 0 < x) : 0 < x + 1 := by\n  exact add_pos h one_pos\n"
# Elaboration that writes over the accepted pair's olean, which the pin leg before it compiled into the tree.
CLOBBER = ('#eval IO.FS.writeFile ".lake/build/lib/lean/Pairs/accepted__p0.olean" ""\n'
           "theorem clobber__p0 : True := trivial\n")
# How a pair finds its own scratch directory: from the run's TMPDIR, its own text's sha256, the environment and the
# attempt, since its read of /proc/self/cmdline fails (only the call's first process, Lake, may read its own).
SCRATCH = ('#eval show IO Unit from do\n'
           '  let sha := (← IO.Process.output { cmd := "sha256sum", args := #["Pairs/NAME__p0.lean"] })'
           '.stdout.take 64\n'
           '  let dir := System.FilePath.mk (← IO.getEnv "TMPDIR").get! / s!"{sha}.pin.1"\n')
# Elaboration that replaces the compile's /usr/bin/time report with a FIFO.
FIFO = (SCRATCH.replace("NAME", "fifo") + '  IO.FS.removeFile (dir / "time")\n'
        '  discard <| IO.Process.run { cmd := "mkfifo", args := #[(dir / "time").toString] }\n'
        "theorem fifo__p0 : True := trivial\n")
# Elaboration that grows the compile's /usr/bin/time report to a 1 TiB sparse file.
SPARSE = (SCRATCH.replace("NAME", "sparse")
          + '  discard <| IO.Process.run { cmd := "truncate", args := #["-s", "1T", (dir / "time").toString] }\n'
          "theorem sparse__p0 : True := trivial\n")
# Elaboration that changes the mode of the tree's Pairs/, of its own scratch directory and of CANARY, a file outside
# its writes, and CANARY's modification time, printing each command's exit status.
META = (SCRATCH.replace("NAME", "meta")
        + '  for (label, cmd, args) in [("pairs", "chmod", #["555", ".lake/build/lib/lean/Pairs"]),\n'
        '      ("scratch", "chmod", #["000", dir.toString]), ("canary", "chmod", #["640", "CANARY"]),\n'
        '      ("utime", "touch", #["-m", "-d", "@0", "CANARY"])] do\n'
        '    IO.println s!"META-{label} {(← IO.Process.output { cmd, args }).exitCode}"\n'
        "theorem meta__p0 : True := trivial\n")
# Elaboration that starts a process writing 512 MiB to the compile's own output, the pipe to the orchestrator, which
# Lean's capture of #eval output never sees. It is larger than the orchestrator's own peak without it (about 350 MB,
# while legs.prepare hashes the toolchain), so that holding it would show in the peak.
FLOOD = ('#eval show IO Unit from do\n'
         '  let child ← IO.Process.spawn { cmd := "sh", args := #["-c", "yes | head -c 512M"] }\n'
         '  discard <| child.wait\n'
         "theorem flood__p0 : True := trivial\n")
# Elaboration that reads SECRET, a file outside the call's read allowlist, as it would the operator's ~/.ssh.
READ = '#eval show IO Unit from do IO.println (← IO.FS.readFile "SECRET")\ntheorem read__p0 : True := trivial\n'
CASES = [  # (case, body, env, limit overrides; "rss": the compile also measured by /usr/bin/time -v)
    ("accepted", ACCEPTED, "pin", {"rss": True}),
    ("accepted", ACCEPTED, "legacy", {}),
    ("clobber", CLOBBER, "pin", {}),
    ("unknown", UNKNOWN, "pin", {}),
    ("unknown", UNKNOWN, "legacy", {}),
    ("spin", "theorem spin__p0 : True := by\n  sleep 600000\n  trivial\n", "pin", {"per_pair_wall_clock_s": 5}),
    ("heavy", "theorem heavy__p0 : (1:ℕ) = 1 := by\n  rfl\n", "pin", {"leg_memory_max_mb": 150}),
    ("plant", PLANT, "pin", {}),
    ("slow", SLOW, "pin", {"per_pair_wall_clock_s": 20}),
    ("fifo", FIFO, "pin", {"rss": True}),
    ("sparse", SPARSE, "pin", {"rss": True}),
    ("meta", META, "pin", {}),
    ("read", READ, "pin", {}),
    ("next", "theorem next__p0 : True := trivial\n", "pin", {}),
]
LEG = {  # spec 04 section 6, with each step's resource facts and the audit's per-declaration timings
    "schema", "pair_id", "pair_sha256", "env", "recipe_id", "code_commit", "classifier_version", "attempt", "limits",
    "refusal", "path_residue", "provenance", "compile", "replay", "audit", "outcome", "table_row", "terminal",
    "dev_overlay"}
STEP = {"exit", "killed", "oom_kill", "wall_s", "peak_mem_kb", "output_truncated"}


def canary(dev_root: Path) -> Path:
    return dev_root / "runs" / f"meta-canary-{os.getpid()}"


def secret(dev_root: Path) -> Path:
    return dev_root / "runs" / f"read-canary-{os.getpid()}"


def header(dev_root: Path) -> str:
    return tomllib.loads((dev_root / "dev-overlay.toml").read_text())["header"]


@pytest.fixture(scope="module")
def ran(tmp_path_factory):
    """Every case run as one leg in the development environment; legs by (case, env), and the results directory."""
    if not os.environ.get("LEDGER_DEV_ROOT"):
        pytest.skip("LEDGER_DEV_ROOT is unset: integration tests need the development environment")
    dev_root = Path(os.environ["LEDGER_DEV_ROOT"])
    canary(dev_root).write_text("")
    canary(dev_root).chmod(0o600)
    os.utime(canary(dev_root), (10**9, 10**9))
    secret(dev_root).write_text("read-canary-zq")
    cases = [(f"{case}__p0", header(dev_root) + body.replace("CANARY", str(canary(dev_root)))
              .replace("SECRET", str(secret(dev_root))), env, limits) for case, body, env, limits in CASES]
    legs, scratch = run_legs(dev_root, tmp_path_factory.mktemp("legs"), cases)
    yield {(leg["pair_id"].removesuffix("__p0"), leg["env"]): leg for leg in legs}, scratch / "results", dev_root
    shutil.rmtree(scratch)
    canary(dev_root).unlink()
    secret(dev_root).unlink()


def test_accepted(ran):
    """A clean pair is accepted at the pin (compile, replay, audit) and at the declared revision (compile, audit),
    both outcomes kept, the legacy one compiled into the legacy output root, .lake/build/lib, whose directory
    the leg created and where the legacy audit found the module. Each result has exactly the leg file's fields,
    every step's exit, output, wall-clock and peak, the worker count and ceiling, and marks itself dev-only."""
    # covers: test_both_environments_outcomes_in_record, test_legacy_output_root_is_lib, test_output_dir_created
    # covers: test_record_carries_exit_output_wall_workers_ceiling, test_records_marked_dev
    legs, results, dev_root = ran
    pin, legacy = legs["accepted", "pin"], legs["accepted", "legacy"]
    assert (pin["outcome"], legacy["outcome"]) == ("accepted", "accepted")
    assert pin["replay"]["output"] == "replaying Pairs.accepted__p0\n" and legacy["replay"] is None
    assert pin["compile"].pop("max_rss_kb") > 0  # /usr/bin/time -v, as the D+14 pilot measures
    assert (dev_root / "env/legacy/.lake/build/lib/Pairs/accepted__p0.olean").exists()
    assert [d["name"] for d in legacy["audit"]["decls"]] == ["accepted__p0"]
    for leg in (pin, legacy):
        assert set(leg) == LEG and leg["dev_overlay"] is True and leg["terminal"] is True
        steps = [leg[s] for s in ("compile", "replay", "audit") if leg[s]]
        assert all(STEP <= set(s) and s["exit"] == 0 and s["wall_s"] > 0 and s["peak_mem_kb"] > 0 for s in steps)
        assert leg["limits"]["worker_count"] >= 1 and leg["limits"]["memory_ceiling_mb"] == 12288
        assert "diagnostics" in leg["compile"] and "stderr" in leg["audit"]
    progress = json.loads((results / "progress.json").read_text())["legs"][pin["pair_sha256"]]
    assert {env: (p["terminal"], p["leg"]) for env, p in progress.items()} == {
        env: (True, f"legs/{pin['pair_sha256'][7:]}.{env}.1.json") for env in ("pin", "legacy")}


def test_pair_cannot_overwrite_another_pairs_olean(ran):
    """A pair whose elaboration writes over another pair's olean fails to: its compile writes only its own scratch
    directory, so the other pair's olean is still the one its own compile wrote."""
    legs, _, dev_root = ran
    assert "permission denied" in legs["clobber", "pin"]["compile"]["diagnostics"]
    assert (dev_root / "env/pin/.lake/build/lib/lean/Pairs/accepted__p0.olean").stat().st_size > 0


def test_pair_cannot_change_metadata(ran):
    """A pair's code changes no file's mode or timestamps (Landlock mediates neither): its chmod of the tree's
    Pairs/, of its own scratch directory and of a file outside its writes, and its utime of that file, all fail;
    its leg is terminal, and the next pair compiles into Pairs/ as before."""
    legs, _, dev_root = ran
    leg, pairs = legs["meta", "pin"], dev_root / "env/pin/.lake/build/lib/lean/Pairs"
    assert re.findall(r"META-(\w+) (\d+)", leg["compile"]["diagnostics"]) == [
        ("pairs", "1"), ("scratch", "1"), ("canary", "1"), ("utime", "1")]
    assert (leg["outcome"], leg["terminal"]) == ("accepted", True)
    assert pairs.stat().st_mode & 0o200 and (pairs / "next__p0.olean").stat().st_size > 0
    assert (canary(dev_root).stat().st_mode & 0o7777, canary(dev_root).stat().st_mtime) == (0o600, 10**9)
    assert legs["next", "pin"]["outcome"] == "accepted"


def test_pair_cannot_read_outside_its_allowlist(ran):
    """A pair's code reads only the system's files, the toolchain, its tree, the audit executable and its scratch
    directory: its read of a file elsewhere fails, its leg is elab-error, and the next pair is accepted as before."""
    legs = ran[0]
    leg = legs["read", "pin"]
    assert "permission denied" in leg["compile"]["diagnostics"] and "read-canary-zq" not in json.dumps(leg)
    assert leg["outcome"] == "elab-error" and legs["next", "pin"]["outcome"] == "accepted"


def test_no_absolute_path_in_leg_files(ran):
    """No leg file carries an absolute path: every step's output is rewritten relative to the root, the tree's
    own path printed by a pair included."""
    files = list((ran[1] / "legs").glob("*.json"))
    assert len(files) == len(CASES) and not any(diagnostics.rewrite_paths(f.read_text(), [])[1] for f in files)
    assert '{ toString := "." }' in ran[0]["unknown", "pin"]["compile"]["diagnostics"]


@pytest.mark.parametrize("env", ["pin", "legacy"])
def test_elab_error(ran, env):
    """An unknown identifier fails the compile as elab-error, by each toolchain's own diagnostic shape."""
    leg = ran[0]["unknown", env]
    assert (leg["outcome"], leg["table_row"], leg["replay"], leg["audit"]) == ("elab-error", f"{env}.error", None, None)


def test_wallclock_kill_is_timeout_not_rejection(ran):
    """A compile still running at the 5 s test limit is killed with its scope: timeout-wall-clock, terminal."""
    leg = ran[0]["spin", "pin"]
    assert (leg["outcome"], leg["table_row"], leg["compile"]["killed"]) == ("timeout-wall-clock", "any.wallclock",
                                                                            "wall-clock")
    assert 5 <= leg["compile"]["wall_s"] < 30 and leg["terminal"] is True


def test_oom_is_resource_not_rejection(ran):
    """Under a 150 MB ceiling, below what any Mathlib import needs, the compile is killed by the scope's memory
    limit, read from memory.events: oom, retryable."""
    leg = ran[0]["heavy", "pin"]
    assert (leg["outcome"], leg["table_row"], leg["compile"]["killed"]) == ("oom", "any.oom", "oom")
    assert leg["compile"]["oom_kill"] > 0 and leg["terminal"] is False


def test_plant_is_replay_reject(ran):
    """A constant added without the kernel's check compiles with exit 0; the pair's own replay rejects it,
    naming it."""
    leg = ran[0]["plant", "pin"]
    assert leg["compile"]["exit"] == 0 and leg["replay"]["rejected_constant"] == "planted_false"
    assert (leg["outcome"], leg["table_row"], leg["audit"]) == ("replay-reject", "pin.replay.reject", None)


def test_replay_wallclock_kill_is_timeout(ran):
    """A replay still running at the per-pair limit is killed: timeout-wall-clock from the replay row."""
    leg = ran[0]["slow", "pin"]
    assert leg["compile"]["exit"] == 0 and leg["replay"]["killed"] == "wall-clock"
    assert (leg["outcome"], leg["table_row"]) == ("timeout-wall-clock", "pin.replay.wallclock")


def test_scratch_outputs_checked(ran, dev_root, tmp_path):
    """The orchestrator trusts nothing the compile left in the pair's scratch directory. A proof that ends the
    compile with exit 0 before its olean is written gets a terminal harness leg (any.output_missing) in each
    environment, and pass 1 goes on to the next pair; a timing report replaced by a FIFO reads as no maximum
    resident set, without blocking, and one grown to a 1 TiB sparse file is read no further than 64 KiB."""
    fifo = ran[0]["fifo", "pin"]
    assert (fifo["outcome"], fifo["compile"]["max_rss_kb"]) == ("accepted", None)
    assert (ran[0]["sparse", "pin"]["outcome"], ran[0]["sparse", "pin"]["terminal"]) == ("accepted", True)
    cases = [(f"{name}__p0", f"{header(dev_root)}theorem {name}__p0 : True := by\n{body}  trivial\n", None, {})
             for name, body in (("exit0", "  run_tac (IO.Process.exit 0 : IO Unit)\n"), ("after", ""))]
    args, scratch = legs_spec(dev_root, tmp_path, cases, pass1=True)
    try:
        assert in_unit(PY, "-c", LEGS, *args, env={"LEDGER_DEV_ROOT": dev_root}, timeout=1800).code == 0
        progress = json.loads((scratch / "results/progress.json").read_text())["legs"]
        legs = [json.loads((scratch / "results" / leg["leg"]).read_text()) for pair in progress.values()
                for leg in pair.values()]
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
    assert {(leg["pair_id"], leg["env"]): (leg["outcome"], leg["table_row"], leg["terminal"]) for leg in legs} == {
        ("exit0__p0", "pin"): ("harness", "any.output_missing", True),
        ("exit0__p0", "legacy"): ("harness", "any.output_missing", True),
        ("after__p0", "pin"): ("accepted", "any.accepted", True),
        ("after__p0", "legacy"): ("accepted", "any.accepted", True)}


def test_output_flood_is_bounded(dev_root, tmp_path):
    """A pair whose compile floods its output (a process it starts writes 512 MiB to the pipe to the orchestrator)
    gets a terminal leg whose diagnostics and log hold the first 4 MiB alone, marked truncated; the orchestrator, in
    a unit capped at 1 GiB, peaks below the flood's own size; and the next pair runs."""
    cases = [(f"{name}__p0", header(dev_root) + body, "pin", {})
             for name, body in (("flood", FLOOD), ("after", "theorem after__p0 : True := trivial\n"))]
    args, scratch = legs_spec(dev_root, tmp_path, cases)
    peak = "\nimport resource\nprint(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)\n"  # kB
    try:
        run = in_unit(PY, "-c", LEGS + peak, *args, env={"LEDGER_DEV_ROOT": dev_root}, timeout=1800,
                      flags=("--property=MemoryMax=1G", "--property=MemorySwapMax=0"))
        assert run.code == 0, run.err[-3000:]
        *lines, peak_kb = run.out.splitlines()
        flood, after = map(json.loads, lines)
        log = (scratch / "logs" / f"{flood['pair_sha256'][7:]}.pin.1.compile.log").stat().st_size
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
    assert (flood["outcome"], flood["terminal"], flood["compile"]["output_truncated"]) == ("accepted", True, True)
    assert log == confine.OUTPUT_MAX and len(flood["compile"]["diagnostics"]) <= confine.OUTPUT_MAX
    assert int(peak_kb) < 512 << 10, peak_kb
    assert (after["outcome"], after["compile"]["output_truncated"]) == ("accepted", False)


def test_kill_restart_no_recheck_no_double_count(dev_root, tmp_path):
    """Pass 1 over a 20-pair sample, in a user unit, killed with SIGKILL mid-run and started again: no leg
    finished before the kill runs again, each leg under way at the kill counts that attempt, every pair ends with
    one terminal leg per environment, and no scope of the killed run survives it."""
    # covers: test_completed_appears_once, test_attempt_counted_at_start
    cases = [(f"r{i}__p0", f"{header(dev_root)}theorem r{i}__p0 : ({i}:ℕ) + 1 = {i + 1} := by\n  rfl\n", None, {})
             for i in range(20)]
    args, scratch = legs_spec(dev_root, tmp_path, cases, pass1=True)
    unit, progress = f"ledger-test-pass1-{os.getpid()}", scratch / "results/progress.json"
    try:
        subprocess.run(["systemd-run", "--user", "--quiet", "--collect", f"--unit={unit}",
                        *unit_setenv({"LEDGER_DEV_ROOT": dev_root}), PY, "-c", LEGS, *map(str, args)], check=True)

        def legs() -> dict:
            return json.loads(progress.read_text())["legs"] if progress.exists() else {}
        deadline = time.monotonic() + 300
        while not (sum(leg["terminal"] for pair in legs().values() for leg in pair.values()) >= 6
                   and any(not leg["terminal"] for pair in legs().values() for leg in pair.values())):
            assert time.monotonic() < deadline, "pass 1 made no progress"
            time.sleep(0.1)
        subprocess.run(["systemctl", "--user", "kill", "--signal=KILL", f"{unit}.service"], check=True)
        while subprocess.run(["systemctl", "--user", "is-active", f"{unit}.service"], capture_output=True).returncode == 0:
            time.sleep(0.1)
        before = legs()
        deadline = time.monotonic() + 10  # the scopes stop with the unit they are bound to
        while subprocess.run(["systemctl", "--user", "list-units", "--plain", "--no-legend",
                              confine.scope_name(dev_root, "*")], capture_output=True, text=True).stdout.strip():
            assert time.monotonic() < deadline, "a scope of the killed run survived it"
            time.sleep(0.1)
        assert in_unit(PY, "-c", LEGS, *args, env={"LEDGER_DEV_ROOT": dev_root}, timeout=1800).code == 0
        after = legs()
        assert len(after) == 20 and all(set(pair) == {"pin", "legacy"} for pair in after.values())
        for sha, pair in after.items():
            for env, leg in pair.items():
                was = before.get(sha, {}).get(env)
                expected = was["attempts"] if was and was["terminal"] else (was["attempts"] if was else 0) + 1
                assert (leg["attempts"], leg["terminal"]) == (expected, True), (sha, env, was, leg)
                assert leg["leg"] == f"legs/{sha[7:]}.{env}.{expected}.json"
        assert any(not leg["terminal"] for pair in before.values() for leg in pair.values())
    finally:
        subprocess.run(["systemctl", "--user", "stop", f"{unit}.service"], capture_output=True)
        shutil.rmtree(scratch, ignore_errors=True)
