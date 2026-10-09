import json

import pytest

from ledger import legs, progress
from ledger.types import LedgerStop

OOM = {"exit": -9, "killed": "oom", "oom_kill": 1}
WALL = {"exit": -9, "killed": "wall-clock"}


def saved(root) -> dict:
    return json.loads((root / "results/progress.json").read_text())["legs"]


def test_attempt_counted_at_start(legs_run, root):
    """An attempt is on disk before the leg's first command runs, so an attempt whose run was killed still
    counts: the next run makes it attempt 2, and a leg whose three attempts were all killed is not started a
    fourth time but written terminal as unclassified. A progress file kept for another draw is refused."""
    run, pairs, lean = legs_run(2, ("pin",))
    sha, killer = pairs[0]["pair_sha256"], pairs[1]["pair_sha256"]
    run.progress.start_attempt(sha, "pin")
    assert saved(root) == {sha: {"pin": {"attempts": 1, "terminal": False, "leg": None}}}
    for _ in range(3):
        run.progress.start_attempt(killer, "pin")
    run, pairs, lean = legs_run(2, ("pin",))
    legs.pass1(run, pairs, ceiling_s=1e9)
    assert saved(root)[sha]["pin"] == {"attempts": 2, "terminal": True, "leg": f"legs/{sha[7:]}.pin.2.json"}
    assert saved(root)[killer]["pin"] == {"attempts": 3, "terminal": True, "leg": f"legs/{killer[7:]}.pin.3.json"}
    killed = json.loads((root / "results" / saved(root)[killer]["pin"]["leg"]).read_text())
    assert (killed["outcome"], killed["diagnostic"]) == ("unclassified", "no outcome: run killed")
    assert {cmd[-1] for step, cmd, _ in lean.calls if step == "compile"} == {"Pairs/p0__p0.lean"}
    with pytest.raises(LedgerStop, match="progress of sample"):
        progress.load(root / "results/progress.json", "sha256:" + "f" * 64)


@pytest.mark.parametrize("answer, attempts", [(WALL, 1), (OOM, 3)],
                         ids=["test_timed_out_terminal", "test_resource_exhausted_retried_to_bound"])
def test_terminal_or_retried(legs_run, root, answer, attempts):
    """A timed-out leg is terminal at once and never attempted again; a resource-exhausted one is retried by
    later runs up to the attempt bound of 3, then written terminal with that count, and no further."""
    run, pairs, lean = legs_run(1, ("pin",))
    lean.answers["compile"] = answer
    for _ in range(4):
        legs.pass1(run, pairs, ceiling_s=1e9)
    assert sum(step == "compile" for step, _, _ in lean.calls) == attempts
    leg = saved(root)[pairs[0]["pair_sha256"]]["pin"]
    assert (leg["attempts"], leg["terminal"]) == (attempts, True)


def test_leg_at_bound_keeps_its_outcome(legs_run, root):
    """A leg at the attempt bound whose attempts had an outcome (oom twice, then a run killed during the third)
    runs no command and is made terminal with its latest outcome, in that attempt's own result file; the pilot
    does not count that attempt's wall-clock twice."""
    run, pairs, lean = legs_run(1, ("pin",))
    sha = pairs[0]["pair_sha256"]
    lean.answers["compile"] = OOM
    for _ in range(2):
        legs.serial_pilot(run, pairs)
    run.progress.start_attempt(sha, "pin")
    legs.serial_pilot(run, pairs)
    assert sum(step == "compile" for step, _, _ in lean.calls) == 2
    assert saved(root)[sha]["pin"] == {"attempts": 3, "terminal": True, "leg": f"legs/{sha[7:]}.pin.2.json"}
    assert json.loads((root / "results/progress.json").read_text())["d14_pilot"]["spent_s"] == 2.0
    leg = json.loads((root / "results" / saved(root)[sha]["pin"]["leg"]).read_text())
    assert (leg["outcome"], leg["attempt"], leg["terminal"]) == ("oom", 2, True)


def test_pin_only_pair_gets_legacy_leg_not_rerun(legs_run, root):
    """Pairs whose pin leg alone was taken (the D+14 pilot) get their legacy leg from the next run with both
    environments, without re-running the pin; once every required leg is terminal a pair is skipped."""
    # covers: test_all_terminal_skipped
    run, pairs, lean = legs_run(2, ("pin",))
    legs.pass1(run, pairs, ceiling_s=1e9)
    run, pairs, lean = legs_run(2)
    lean.calls.clear()
    legs.pass1(run, pairs, ceiling_s=1e9)
    assert {cwd.name for step, _, cwd in lean.calls if step != "git"} == {"legacy"}
    assert all(leg["attempts"] == 1 and leg["terminal"] for pair in saved(root).values() for leg in pair.values())
    lean.calls.clear()
    legs.pass1(run, pairs, ceiling_s=1e9)
    assert lean.calls == []
