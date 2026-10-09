import dataclasses
import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

from ledger import confine, diagnostics, envbuild, legs
from ledger.types import LedgerStop

OOM = {"exit": -9, "killed": "oom", "oom_kill": 1}
WALL = {"exit": -9, "killed": "wall-clock", "peak_mem_kb": 2000}


@pytest.mark.parametrize("env, step, answer, row", [
    ("pin", "replay", OOM, "pin.replay.oom"),
    ("legacy", "audit", OOM, "any.audit.oom"),
    ("pin", "audit", WALL, "any.audit.wallclock"),
], ids=["test_replay_oom_is_resource", "test_audit_oom_is_resource", "test_audit_wallclock_is_timeout"])
def test_killed_step(legs_run, env, step, answer, row):
    """A replay or audit killed by the leg's memory ceiling is oom, and one killed at the per-pair limit is
    timeout-wall-clock, never a rejection; every Lake call in the pin's tree starts `lake --no-cache` and none in
    the legacy tree does."""
    run, pairs, lean = legs_run(1)
    lean.answers[step] = answer
    leg = legs.run_leg(run, pairs[0], env)
    assert (leg["outcome"], leg["table_row"]) == ("oom" if answer is OOM else "timeout-wall-clock", row)
    assert leg[step]["killed"] == answer["killed"] and leg["terminal"] is (answer is WALL)
    lake = [(cmd, cwd) for _, cmd, cwd in lean.calls if cmd[0].endswith("/lake")]
    assert lake and all((cmd[1] == "--no-cache") == (cwd.name == "pin") for cmd, cwd in lake)


def test_pin_leg_refused_on_cache_provenance(legs_run, root):
    """A pin leg runs only in a tree whose artifact set is the one its passed build from source recorded: an
    olean replaced since (as a cache download would) or no passed build report refuses the run. Under the
    stop-loss the seeded tree's legs run, labelled cache-seeded."""
    run, pairs, _ = legs_run(1, ("pin",), status={"stop_loss": True})
    assert legs.run_leg(run, pairs[0], "pin")["provenance"] == "cache-seeded"
    run, pairs, _ = legs_run(1, ("pin",))
    assert legs.run_leg(run, pairs[0], "pin")["provenance"] == "from-source"
    (root / "env/pin/.lake/packages/mathlib/Mathlib.olean").write_text("downloaded")
    with pytest.raises(LedgerStop, match="not the one its passed build recorded"):
        legs.prepare(run.pol, run.consts, run.work, run.results, run.logs, ("pin",))
    (root / "measure/build-pin.json").unlink()
    with pytest.raises(LedgerStop, match="no passed build report"):
        legs.prepare(run.pol, run.consts, run.work, run.results, run.logs, ("pin",))


def test_container_leg_peak_is_largest_process(legs_run):
    """On the host a leg's compile peak is its scope's, labelled cgroup; under a container policy, where it comes from
    wait4, it is labelled largest-process."""
    run, pairs, _ = legs_run(2, ("pin",))
    assert legs.run_leg(run, pairs[0], "pin")["compile"]["peak_mem_source"] == "cgroup"
    container = dataclasses.replace(run, pol=dataclasses.replace(run.pol, kind="container"))
    assert legs.run_leg(container, pairs[1], "pin")["compile"]["peak_mem_source"] == "largest-process"


@pytest.mark.parametrize("change", [lambda audit: audit.write_text("rebuilt"), lambda audit: audit.unlink()],
                         ids=["replaced", "absent"])
def test_audit_executable_is_the_built_one(legs_run, root, change):
    """No leg runs unless the audit executable is the one the environment's passed build recorded: one replaced
    or removed since stops the run, rather than failing every leg's audit as harness."""
    run, _, _ = legs_run(1, ("legacy",))
    change(root / "env/audit-legacy" / envbuild.AUDIT_BIN)
    with pytest.raises(LedgerStop, match="ledger-audit is not the executable"):
        legs.prepare(run.pol, run.consts, run.work, run.results, run.logs, ("legacy",))


def test_pass1_stops_dispatching_after_a_leg_raises(legs_run, monkeypatch):
    """Once a leg's call fails (here with an OSError, not a LedgerStop), pass 1 starts no further pair, so a
    failure every pair would meet spends one attempt, not one per pair of the draw."""
    run, pairs, _ = legs_run(3, ("pin",))
    started = []

    def failing(cmd, **kwargs):
        started.append(cmd[-1])
        raise OSError("every call fails")
    monkeypatch.setattr(confine, "run", failing)
    with pytest.raises(LedgerStop, match="every call fails"):
        legs.pass1(dataclasses.replace(run, workers=1), pairs, ceiling_s=1e9)
    assert started == ["Pairs/p0__p0.lean"]


@pytest.mark.parametrize("damage, error", [
    (lambda root: shutil.rmtree(root / "tmp/r"), "FileNotFoundError"),
    (lambda root: (root / "env/pin/Pairs").chmod(0o555), "PermissionError"),
], ids=["tmpdir_missing", "pairs_unwritable"])
def test_orchestrator_failure_stops_pass1(legs_run, root, damage, error):
    """An error in the orchestrator's own setup, which every pair would meet (the run's TMPDIR gone, the tree's
    Pairs/ unwritable), is no pair's result: pass 1 stops with LedgerStop at the first leg, before any call, and
    no leg is written terminal."""
    run, pairs, lean = legs_run(3, ("pin",))
    (root / "env/pin/Pairs").mkdir()
    damage(root)
    try:
        with pytest.raises(LedgerStop, match=error):
            legs.pass1(dataclasses.replace(run, workers=1), pairs, ceiling_s=1e9)
    finally:
        (root / "env/pin/Pairs").chmod(0o755)
    saved = json.loads((run.results / "progress.json").read_text())["legs"]
    assert [step for step, _, _ in lean.calls] == ["git"] and not any((run.results / "legs").iterdir())
    assert [(leg["attempts"], leg["terminal"]) for pair in saved.values() for leg in pair.values()] == [(1, False)]


def test_truncated_output_recorded(legs_run):
    """Whether a step's output passed confine.run's bound is in that step's record."""
    run, pairs, lean = legs_run(1, ("pin",))
    lean.answers["compile"] = {"output_truncated": True}
    leg = legs.run_leg(run, pairs[0], "pin")
    assert [leg[step]["output_truncated"] for step in ("compile", "replay", "audit")] == [True, False, False]


def test_path_residue_is_harness(legs_run):
    """A host path left in a step's output after rewriting is withheld from the leg file and makes the leg
    harness, by its table row, without stopping the run."""
    run, pairs, lean = legs_run(1, ("pin",))
    lean.answers["compile"] = {"output": "error at /mnt/example/x.lean"}
    leg = legs.run_leg(run, pairs[0], "pin")
    assert (leg["outcome"], leg["table_row"], leg["path_residue"]) == ("harness", "any.path_residue", True)
    assert not diagnostics.rewrite_paths(json.dumps(leg), [])[1]


def test_pass1_stops_on_worst_case_W(legs_run, root):
    """A pair starts only while the time elapsed plus its worst case (the per-pair limit for each step its legs
    still take: 5 for both legs) fits the ceiling; past it the run starts nothing more, and every leg that
    finished is in the progress file on disk when it returns, the truncation's cause beside it."""
    # covers: test_truncated_run_flushes_before_lock_release
    run, pairs, lean = legs_run(3, limits={"per_pair_wall_clock_s": 100})
    ticks = iter([0, 0, 250])
    cause = legs.pass1(dataclasses.replace(run, workers=1), pairs, ceiling_s=700, clock=lambda: next(ticks))
    assert cause.startswith("run-truncated: 250 s elapsed and p1__p0's worst case of 500 s")
    saved = json.loads((root / "results/progress.json").read_text())["legs"]
    assert list(saved) == [pairs[0]["pair_sha256"]] and all(leg["terminal"] for leg in saved[pairs[0]["pair_sha256"]].values())


def test_serial_pilot_25h_line_pairs_attempted(legs_run, root):
    """The D+14 pilot runs the pin leg alone, pair by pair, and stops at the pair boundary where its compile and
    replay wall-clocks reach 25 hours; the pairs attempted are recorded as the pilot, and each compile carries
    /usr/bin/time -v's maximum resident set beside the scope's peak. A pilot stopped after two pairs and started
    again runs neither again, and keeps its sum and its list."""
    run, pairs, lean = legs_run(5, ("pin",))
    lean.answers["compile"] = {"wall_s": 7 * 3600.0}
    first = legs.serial_pilot(run, pairs[:2])
    attempted = first + legs.serial_pilot(run, pairs)
    assert [leg["pair_sha256"] for leg in attempted] == [p["pair_sha256"] for p in pairs[:4]]
    assert json.loads((root / "results/progress.json").read_text())["d14_pilot"] == {
        "attempted": [p["pair_sha256"] for p in pairs[:4]], "spent_s": 4 * (7 * 3600.0 + 1.0), "line_reached": True}
    assert {(leg["env"], leg["compile"]["max_rss_kb"], leg["limits"]["worker_count"]) for leg in attempted} == {("pin", 4242, 1)}


def test_scratch_left_unreadable_or_huge(legs_run, monkeypatch):
    """Nothing a compile leaves in its scratch directory stops a run. A scratch directory left unreadable
    (mode 000) after exit 0 is output_missing, terminal, and pass 1 goes on; after a retryable outcome the next
    attempt compiles in a fresh scratch directory. A timing report grown to a 1 TiB sparse file, its report past
    the first 64 KiB, is read no further (max_rss_kb null), and the pilot goes on."""
    run, pairs, lean = legs_run(5, ("pin",))
    run, locked = dataclasses.replace(run, workers=1), []
    lean.answers["compile"] = [{}, OOM, {}, {}, {}, {}]

    def compile_then(cmd, **kwargs):
        proc, name = lean(cmd, **kwargs), cmd[-1].removeprefix("Pairs/").removesuffix("__p0.lean")
        if name in ("p0", "p1") and (scratch := Path(cmd[cmd.index("-i") - 1]).parent).name.endswith(".1"):
            locked.append(scratch)  # the first attempt's
            scratch.chmod(0)
        if name == "p3":
            (timing := Path(cmd[cmd.index("-o") + 1])).write_bytes(bytes(64 * 1024) + timing.read_bytes())
            os.truncate(timing, 1 << 40)
        return proc
    monkeypatch.setattr(confine, "run", compile_then)
    legs.pass1(run, pairs[:3], ceiling_s=1e9)
    legs.pass1(run, pairs[:3], ceiling_s=1e9)
    pilot = legs.serial_pilot(run, pairs[3:])
    for path in locked:  # so that pytest can remove them
        path.chmod(0o700)
    saved = json.loads((run.results / "progress.json").read_text())["legs"]
    outcomes = [json.loads((run.results / saved[p["pair_sha256"]]["pin"]["leg"]).read_text()) for p in pairs[:3]]
    assert [(leg["outcome"], leg["table_row"], leg["attempt"], leg["terminal"]) for leg in outcomes] == [
        ("harness", "any.output_missing", 1, True), ("accepted", "any.accepted", 2, True),
        ("accepted", "any.accepted", 1, True)]
    assert [(leg["outcome"], leg["compile"]["max_rss_kb"]) for leg in pilot] == [("accepted", None), ("accepted", 4242)]


def test_no_pair_aborts_the_pilot(legs_run, monkeypatch):
    """No single pair aborts the pilot. A timing report the pair recreates with mode 000, or
    rewrites with a maximum resident set too long for int(), reads as no maximum resident set; a leg whose own
    result processing raises (here an audit line that is not JSON) is terminal harness, the error its diagnostic;
    and the next pair runs."""
    run, pairs, lean = legs_run(4, ("pin",))
    lean.answers["audit"] = [{}, {"output": "{\n"}, {}, {}]

    def compile_then(cmd, **kwargs):
        proc = lean(cmd, **kwargs)
        if cmd[-1] == "Pairs/p0__p0.lean":
            subprocess.run(["sh", "-c", 'rm -f "$1/time" && umask 777 && : > "$1/time"', "sh",
                            Path(cmd[cmd.index("-o") + 1]).parent], check=True)
        if cmd[-1] == "Pairs/p2__p0.lean":
            Path(cmd[cmd.index("-o") + 1]).write_text(f"\tMaximum resident set size (kbytes): {'9' * 5000}\n")
        return proc
    monkeypatch.setattr(confine, "run", compile_then)
    pilot = legs.serial_pilot(run, pairs)
    assert [(leg["outcome"], leg["table_row"], leg["terminal"], leg["compile"]["max_rss_kb"]) for leg in pilot] == [
        ("accepted", "any.accepted", True, None), ("harness", None, True, 4242), ("accepted", "any.accepted", True, None),
        ("accepted", "any.accepted", True, 4242)]
    assert pilot[1]["diagnostic"].startswith("JSONDecodeError: ")
