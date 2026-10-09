import json
import time
from datetime import date, timedelta
from types import SimpleNamespace

import pytest

from ledger import confine, gatefile, legs, modes, rebuild
from ledger.types import LedgerStop

TODAY = date(2026, 12, 2)
OOM = {"exit": -9, "killed": "oom", "oom_kill": 1}  # a leg step killed by its memory ceiling: retryable


@pytest.fixture
def pilot(leg_results, root, monkeypatch):
    """A D+14 pilot of three pairs, each pin leg accepted, in trees as legs_run builds them, the D+14 build's
    wall-clock 1000 s and the frozen per-pair limit 100 s; a later run's TMPDIR; and every fetch and build answered as
    FakeLean answers them."""
    def make(**published):
        run, _, pairs = leg_results([{"pin": {}}] * 3, limits={"per_pair_wall_clock_s": 100}, **published)
        run.progress.pilot([pair["pair_sha256"] for pair in pairs], 0.0, False)
        (root / "work/assembled.jsonl").write_text("".join(json.dumps(pair) + "\n" for pair in pairs))
        tree = run.consts.tree("pin")
        report = root / "measure" / f"build-{tree}.json"
        report.write_text(json.dumps(json.loads(report.read_text()) | {"wall_s": 1000.0}))
        (tmp := root / "tmp/rebuild-night").mkdir()
        monkeypatch.setenv("TMPDIR", str(tmp))
        confine.run.olean = f"{tree} as built"  # what the D+14 build left: the rebuilt set matches it by default
        return SimpleNamespace(run=run, pairs=pairs, lean=confine.run)
    return make


def attempt(world, start: float | None = None) -> str:
    """One attempt over the pilot's run of legs, its unit started at `start`, by default now."""
    return rebuild.attempt(world.run, TODAY, time.monotonic() if start is None else start)


def lines(world) -> list:
    return [row[1:] for row in gatefile.rows(world.run.pol)]


def recorded(world) -> dict:
    """The progress file as the attempts left it."""
    return json.loads(world.run.progress.path.read_text())


@pytest.mark.parametrize("olean, compile, result", [
    ("pin as built", {}, "pass"),
    ("built otherwise", {}, "artifact-divergent-outcome-match"),
    ("pin as built", {"exit": 1, "output": "error: unsolved goals"}, "fail"),
], ids=["test_outcome_hash_decides", "test_artifact_divergence_with_matching_outcomes_passes_no_retry",
        "test_outcome_mismatch_fails_attempt"])
def test_attempt_result(pilot, root, olean, compile, result):
    """The rebuilt tree's outcome hash over the pilot pairs decides: equal to the main tree's, the attempt passes, and
    with a divergent artifact set it passes too, with a note naming the diverging oleans, their package and the
    recipe input it comes from, and no retry follows; a different outcome fails the attempt. Each is recorded in the
    progress file, then as its gate line."""
    # covers: test_divergence_note_names_components
    world = pilot()
    world.lean.olean, world.lean.answers = olean, {"compile": compile}
    assert attempt(world) == result
    assert recorded(world)["rebuild"]["attempts"] == [{"n": 1, "date": "2026-12-02", "result": result}]
    gate, verdict, _, reason = lines(world)[0]
    assert (gate, verdict) == ("d30-attempt-1", result) and ("diverged" in reason) == (olean != "pin as built")
    note = root / "measure/d30/divergence-1.md"
    assert note.exists() == (olean != "pin as built")
    if note.exists():
        mathlib = next(p for p in json.loads((world.run.consts.repo / "recipe/pin/lake-manifest.json").read_text())[
            "packages"] if p["name"] == "mathlib")
        text = note.read_text()
        assert f"- mathlib: {mathlib['url']} at {mathlib['rev']}\n" in text
        assert "- .lake/packages/mathlib/Mathlib.olean\n" in text
        assert lines(world)[1][:2] == ("d30-divergence-note", "written")
        assert not modes.rebuild_night(31, recorded(world))


def test_allowance_uses_reopened_figures(pilot):
    """The allowance is 1.5 times the D+14 build plus each pilot pin leg's compile, replay and audit wall-clocks: a leg
    reopened and run again counts its re-run's, one reopened and not yet run again the frozen limit itself, once."""
    world = pilot()
    first, second, third = (pair["pair_sha256"] for pair in world.pairs)
    world.run.progress.reopen({first: {"reason": "over-frozen-limit", "date": "2026-11-23"}, second: None})
    world.lean.answers = {step: {"wall_s": 5.0} for step in ("compile", "replay", "audit")}
    legs.run_leg(world.run, world.pairs[1], "pin")
    limit = world.run.consts.published["limits"]["per_pair_wall_clock_s"]
    assert rebuild.allowance(world.run.pol, world.run.consts, world.run.progress) == 1500 + limit + 15 + 3


def test_one_deadline_from_the_unit_start(pilot):
    """The attempt's deadline is its unit's start plus the allowance, a margin before systemd's: the fetch and the
    audit project's and the tree's builds share what remains of the build part, 1.5 times the D+14 build from the
    start, and a re-run whose pairs no longer fit before the deadline fails the attempt, its line written."""
    world = pilot()
    assert attempt(world, time.monotonic() - 1400) == "fail"
    bounded = [kwargs["timeout_s"] for (step, _, cwd), kwargs in zip(world.lean.calls, world.lean.kwargs)
               if cwd.name in ("rebuild", "audit-rebuild") and (kwargs.get("net") or step == "build")]
    assert len(bounded) == 3 and all(0 < timeout <= 100 for timeout in bounded)
    assert lines(world)[0][3].startswith("the 50-pair re-run: run-truncated")


@pytest.mark.parametrize("error", [LedgerStop("a leg's harness stopped"), KeyError("legs")],
                         ids=["test_stop_fails_attempt", "test_error_raised_after_line"])
def test_every_attempt_ends_with_its_line(pilot, monkeypatch, error):
    """An attempt is recorded failed while it runs, so one its unit kills is counted; whatever raises in it, it ends
    failed in the progress file and its d30-attempt line names the cause; the pipeline's own stop is the attempt's
    failure, and any other error is raised once the line is written."""
    world = pilot()

    def raises(*_):
        assert recorded(world)["rebuild"]["attempts"] == [{"n": 1, "date": "2026-12-02", "result": "fail"}]  # running
        raise error
    monkeypatch.setattr(legs, "complete", raises)
    if isinstance(error, LedgerStop):
        assert attempt(world) == "fail"
    else:
        with pytest.raises(KeyError):
            attempt(world)
    assert recorded(world)["rebuild"]["attempts"][0]["result"] == "fail"
    assert lines(world)[0][:2] == ("d30-attempt-1", "fail") and str(error) in lines(world)[0][3]


def test_rerun_retries_retryable_outcomes(pilot):
    """A re-run leg killed by its memory ceiling is retried to the attempt bound, as pass 1 retries one, so a night's
    load does not decide the attempt."""
    world = pilot()
    world.lean.answers = {"replay": [OOM, {}, {}, {}]}
    assert attempt(world) == "pass"


def test_three_failures_not_a_kill(pilot):
    """Three failed attempts write three failed attempt lines and no kill, and pass 1 takes the next night."""
    world = pilot()
    world.lean.answers = {"build": {"exit": 1}}
    assert [attempt(world) for _ in range(3)] == ["fail"] * 3
    assert [row[:2] for row in lines(world)] == [(f"d30-attempt-{n}", "fail") for n in (1, 2, 3)]
    d0 = TODAY - timedelta(days=32)
    assert modes.action(d0 + timedelta(days=33), d0, recorded(world)).mode == "pass1"


def test_lake_cache_nonempty_refuses(pilot, root):
    """A Lake artifact cache holding anything refuses the build: the attempt fails and nothing is built."""
    world = pilot()
    (root / "xdg-cache/lake").mkdir(parents=True)
    (root / "xdg-cache/lake/planted").touch()
    assert attempt(world) == "fail"
    assert "the cache is not empty" in lines(world)[0][3]
    assert not any(step == "build" for step, _, _ in world.lean.calls[-10:])


def test_rebuild_uses_seeded_recipe_under_stop_loss(pilot, root):
    """Under the stop-loss the rebuild fetches the seeded recipe, its dependency layers by the cache's get, with
    network, and builds it in env/rebuild, its artifact set held to the one the seeded build recorded at D+14."""
    world = pilot(status={"stop_loss": True})
    assert attempt(world) == "pass"
    calls = [(cmd, cwd, kwargs) for (_, cmd, cwd), kwargs in zip(world.lean.calls, world.lean.kwargs)]
    tree = root / "env/rebuild"
    assert any(cmd[-3:] == ["exe", "cache", "get"] and cwd == tree and kwargs["net"] for cmd, cwd, kwargs in calls)
    assert any(cmd[-3:] == ["build", "Mathlib", "Aesop"] and cwd == tree for cmd, cwd, _ in calls)
