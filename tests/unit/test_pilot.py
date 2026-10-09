"""The D+21 pilot: the first 30 pairs end to end under the frozen constants, their pin legs a rehearsal of D+14's;
route one; the fit check against the pass-1 nights; nothing end to end; the pilot replay in its own unit; and the
single permitted re-scope."""

import dataclasses
import hashlib
import json
from datetime import date

import pytest
from helpers import REPO, hold_lock

from ledger import aggregate, cli, confine, constants, freeze, gatefile, legs, pilot, policy, preflight
from ledger.types import LedgerStop

TODAY = date(2026, 11, 23)
TABLE = "sha256:" + hashlib.sha256((REPO / "classifier/table-v1.toml").read_bytes()).hexdigest()
FROZEN = {"classifier": {"status": "frozen", "table_sha256": TABLE}, "limits": {"per_pair_limit_status": "frozen"}}
ERROR = {"exit": 1, "output": "Pairs/p.lean:2:2: error: unknown identifier\n"}
OOM = {"exit": -9, "killed": "oom", "oom_kill": 1}


def clock(elapsed: float):
    """The pilot's clock: its pass takes `elapsed` seconds."""
    return iter([0.0, elapsed]).__next__


@pytest.fixture
def draw(legs_run, root, code_repo, monkeypatch):
    """A draw of `n` pairs and a run over it in `envs`, under the frozen constants of a committed copy of the recipe,
    where a cut is written, their freeze lines recorded, with one worker, so that FakeLean answers the legs in draw order, pin then legacy; the
    first `d14` pairs carry accepted D+14 pilot pin legs, as the D+14 measurement recorded them. Returns the run, the
    pairs and the FakeLean."""
    monkeypatch.setattr(preflight, "headroom", lambda *_: 1)

    def make(n: int, d14: int = 0, envs=("pin", "legacy"), **published):
        run, pairs, lean = legs_run(n, envs, **{table: FROZEN.get(table, {}) | published.get(table, {})
                                                for table in FROZEN.keys() | published.keys()})
        run = dataclasses.replace(run, consts=dataclasses.replace(run.consts, repo=code_repo))
        for gate in freeze.LINES:
            gatefile.append(run.pol, gate, "frozen", "pipeline", "test", TODAY)
        for pair in pairs:  # each declaring its own pair, as the aggregate requires
            (run.work / "pairs" / f"{pair['pair_id']}.lean").write_text(
                f"{run.consts.published['assembly']['header']}theorem {pair['pair_id']} : True := by\n  trivial\n")
        for pair in pairs[:d14]:
            legs.run_leg(run, pair, "pin")
        run.progress.pilot([pair["pair_sha256"] for pair in pairs[:d14]], 0.0, False)
        (root / "measure/d14").mkdir(parents=True)
        (root / "measure/d14/pairs.json").write_text(json.dumps(
            [{"pair_id": pair["pair_id"], "outcome": "accepted"} for pair in pairs[:d14]]))
        return run, pairs, lean
    return make


def lines(run, gate: str) -> list[tuple[str, str]]:
    return [(row[2], row[4]) for row in gatefile.rows(run.pol) if row[1] == gate]


def cut_n(code_repo) -> int:
    return constants.load(code_repo).published["sampling"]["cut_n"]


def test_rehearsal_mismatch_is_harness_error_and_failed_pilot(draw, code_repo, tmp_path):
    """A pilot pin leg rehearsing D+14's to another outcome makes the pair harness-error (d21-rehearsal) and fails
    the pilot, routed as nothing end to end, the re-scope; a leg reopened at the freeze runs again with no match
    required. The pilot refuses to run before the freeze lines are recorded."""
    # covers: test_reopened_leg_excepted_from_rehearsal
    run, pairs, lean = draw(30, d14=3)
    run.progress.reopen({pairs[1]["pair_sha256"]: {"reason": "over-frozen-limit", "date": "2026-11-23"}})
    (tmp_path / "gates").mkdir()
    (tmp_path / "gates/GATES.md").touch()
    with pytest.raises(LedgerStop, match="freeze first"):
        pilot.d21(dataclasses.replace(run, pol=dataclasses.replace(run.pol, values=run.pol.values | {
            "public_tree": str(tmp_path)})), pairs, TODAY)
    lean.answers = {"compile": [ERROR, {}, ERROR, {}] + [{}] * 56}  # pairs 0 and 1 at the pin, then the rest
    report = pilot.d21(run, pairs, TODAY, clock(30 * 60.0))
    overrides = run.progress.data["harness_overrides"]
    assert [(o["source"], o["detail"]) for o in overrides.values()] == [
        ("d21-rehearsal", "pin accepted at D+14, elab-error at D+21")]
    assert list(overrides) == [pairs[0]["pair_sha256"]]
    assert report.verdict == "rescope" and "rehearsal mismatch: 1 pairs harness-error" in report.reason
    assert lines(run, "rescope") == [("cut_n=30", "d21: rehearsal mismatch: 1 pairs harness-error")]
    assert lines(run, "d21-pilot") == [("rescope", report.reason)] and cut_n(code_repo) == 30


def test_rehearsal_reruns_leg_at_bound_once(draw, monkeypatch):
    """A rehearsed pin leg gets a fresh allowance of attempts, so one whose D+14 run took every attempt runs again;
    and a pilot restarted after its pass reopens no leg a second time, and, its pass's figure unsaved and its own
    pass starting nothing, refuses rather than cost a pair at nothing."""
    run, pairs, lean = draw(30, d14=1)
    sha, real = pairs[0]["pair_sha256"], legs.pass1
    run.progress.data["legs"][sha]["pin"]["attempts"] = 3

    def died(*args):
        real(*args)
        raise LedgerStop("the run died")
    monkeypatch.setattr(legs, "pass1", died)
    with pytest.raises(LedgerStop, match="died"):
        pilot.d21(run, pairs, TODAY, clock(60.0))
    monkeypatch.setattr(legs, "pass1", real)
    with pytest.raises(LedgerStop, match="no per-pair cost"):
        pilot.d21(run, pairs, TODAY, clock(60.0))
    assert run.progress.attempts(sha, "pin") == 4 and run.progress.data["legs"][sha]["pin"]["leg"] == (
        f"legs/{sha.removeprefix('sha256:')}.pin.4.json")


def test_per_pair_cost_over_pairs_run(draw):
    """The per-pair cost is the pass's wall-clock over the pairs it ran: where the ceiling stops pairs starting, over
    those that started alone. Ten pairs need their legacy leg alone, whose worst case fits the ceiling; the next needs
    both, whose worst case does not."""
    run, pairs, lean = draw(30, limits={"per_pair_wall_clock_s": 20_000})
    for pair in pairs[:10]:
        legs.run_leg(run, pair, "pin")
    assert "complete=10; per_pair_s=10.0;" in pilot.d21(run, pairs, TODAY, clock(100.0)).reason


@pytest.mark.parametrize("environment", [20, 19], ids=["test_route_one_20_of_30", "test_route_one_19_of_30_not_fired"])
def test_route_one(draw, environment):
    """20 or more of the 30 pilot pairs in an environment class (here failing at the pin, checking at the declared
    revision: environment-mismatch) write route-one; 19 do not."""
    run, pairs, lean = draw(30)
    lean.answers = {"compile": [answer for i in range(30) for answer in (ERROR if i < environment else {}, {})]}
    assert pilot.d21(run, pairs, TODAY, clock(60.0)).verdict == "met"
    assert lines(run, "route-one") == [("skew framing invoked",
                                        "20 of 30 pilot pairs in an environment class")] * (environment == 20)


@pytest.mark.parametrize("rescoped", [False, True], ids=["test_fit_check_rescope_N", "test_second_rescope_is_kill"])
def test_fit_check(draw, root, code_repo, monkeypatch, rescoped):
    """The pilot's parallel-amortised per-pair cost times the rest of the sample must fit the 21 pass-1 nights at 14
    hours each: 10 pairs at 4,000,000 s over 30 do not, so the sample is cut to the 30 complete and the 7 more that
    fit, N = 37. Where the single re-scope is spent already, that is the kill, and nothing is cut. A pilot that died
    after its pass, before its writes, is restarted to the same verdict: its pass starts nothing, and the cost is the
    one saved. After the pilot's re-scope, the pilot replay killed under the cap is the kill."""
    run, pairs, lean = draw(40)
    if rescoped:
        gatefile.append(run.pol, "rescope", "cut_n=40", "pipeline", "d14: rescope", TODAY)
    real = aggregate._write

    def died(*args):
        monkeypatch.setattr(aggregate, "_write", real)
        raise LedgerStop("the run died")
    monkeypatch.setattr(aggregate, "_write", died)
    with pytest.raises(LedgerStop, match="died"):
        pilot.d21(run, pairs, TODAY, clock(4_000_000.0))
    report = pilot.d21(run, pairs, TODAY, clock(1.0))
    fit = "the fit check: 10 pairs at 133333 s each over 1058400 s"
    if rescoped:
        assert report.verdict == "kill" and lines(run, "kill") == [("a second re-scope", f"d21: {fit}; N=37")]
        assert cut_n(code_repo) == 0
    else:
        assert report.verdict == "rescope" and lines(run, "rescope") == [("cut_n=37", f"d21: {fit}")]
        assert cut_n(code_repo) == 37
        (root / "measure/d14/projection.json").write_text(json.dumps({"E": 1000.0, "m": 50.0}))
        lean.answers = {"replay": {"exit": -9, "killed": "wall-clock"}}
        assert pilot.d21_replay(run, pairs, TODAY) == "kill" and lines(run, "kill")[0][0] == "a second re-scope"


def test_nothing_end_to_end_rescope(draw, code_repo, monkeypatch):
    """With no pilot pair complete in both environments, the sample is cut to what the measured per-pair cost fits
    into the pass-1 nights: 30 pairs over 900,000 s, so 35. A pilot that died after the re-scope was written and
    before its d21-pilot line completes them on restart, never counting its own rescope line as an earlier one."""
    run, pairs, lean = draw(40)
    lean.answers = {"compile": OOM}  # retried on a later night, so no leg is terminal
    real = gatefile.append

    def died(pol, gate, *args):
        if gate == "d21-pilot":
            raise LedgerStop("the run died")
        real(pol, gate, *args)
    monkeypatch.setattr(gatefile, "append", died)
    with pytest.raises(LedgerStop, match="died"):
        pilot.d21(run, pairs, TODAY, clock(900_000.0))
    monkeypatch.setattr(gatefile, "append", real)
    assert pilot.d21(run, pairs, TODAY, clock(1.0)).verdict == "rescope"
    assert lines(run, "rescope")[0][0] == "cut_n=35" and "nothing end to end" in lines(run, "rescope")[0][1]
    assert cut_n(code_repo) == 35 and lines(run, "kill") == [] and lines(run, "d21-pilot")[0][0] == "rescope"


def test_fit_check_night_count_21_less_skipped(make_policy, root):
    """The pass-1 nights are 21, less the D+22 night a failed D+21 proof's repeat takes, and less each skipped
    night: a nightly run finding the lock held, as by the pilot replay still running at the D+22 trigger, records
    one."""
    # covers: test_replay_holding_lock_is_skipped_night
    pol = policy.load(make_policy())
    assert pilot.nights(pol) == 21
    gatefile.append(pol, "d21-proof-2", "fail", "pipeline", "planted_sorry__p0: reproduced", TODAY)
    assert pilot.nights(pol) == 20
    (run := root / "runs/night").mkdir(parents=True)
    with hold_lock(root) as replay:
        assert cli.contended(pol, run, "nightly", str(replay.pid), "test", {}) == 0
    assert pilot.nights(pol) == 19


def test_pilot_replay_overrun_rescope_N(draw, root, code_repo):
    """The pilot replay killed under the cap in force is the re-scope, N = floor((cap - E) / m) with D+14's E and m:
    floor((43200 - 1000) / 50) = 844. Run again, it finds its re-scope recorded and makes nothing more."""
    run, pairs, lean = draw(30, envs=("pin",))
    legs.pass1(run, pairs, 1e9)
    (root / "measure/d14/projection.json").write_text(json.dumps({"E": 1000.0, "m": 50.0}))
    lean.answers = {"replay": {"exit": -9, "killed": "wall-clock"}}
    assert pilot.d21_replay(run, pairs, TODAY) == "rescope"
    assert lines(run, "rescope") == [("cut_n=844", "d21: the pilot replay was killed (wall-clock) under the cap of "
                                                   "43200 s")] and cut_n(code_repo) == 844
    assert pilot.d21_replay(run, pairs, TODAY) == "rescope" and lines(run, "kill") == []


def test_replay_flag_runs_replay_only(draw, root, make_policy, monkeypatch):
    """`ledger pilot d21 --replay` runs the pilot replay alone, in its own unit: the aggregate over the pilot's
    clean pairs built and replayed with --fresh, and no leg."""
    run, pairs, lean = draw(3, envs=("pin",))
    legs.pass1(run, pairs, 1e9)
    (root / "work/assembled.jsonl").write_text("".join(json.dumps(pair) + "\n" for pair in pairs))
    monkeypatch.setattr(confine, "apply_fs", lambda pol: None)  # in place of the one that would confine this test
    monkeypatch.setattr(preflight, "CHECKS", ())
    calls = len(lean.calls)
    assert cli.main(["pilot", "d21", "--replay", "--policy", str(make_policy())]) == 0
    assert [step for step, _, _ in lean.calls[calls:]] == ["git", "build", "replay"]
