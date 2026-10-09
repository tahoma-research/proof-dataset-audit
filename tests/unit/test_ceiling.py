import functools
import hashlib
import json
import re
from datetime import date, timedelta

import pytest
from helpers import COMMIT

from ledger import cli, confine, constants, gatefile, legs, preflight, progress

FIELDS = ("command", "mode", "result", "needs the operator", "attempted", "leg outcomes",
          "classes of the pairs completed", "pass 1", "skipped", "ceiling", "host at start", "host at end",
          "confinement", "code_commit", "recipe_ids")
OOM = {"exit": -9, "killed": "oom", "oom_kill": 1}
ELAB = {"exit": 1, "output": "Pairs/x.lean:3:2: error: unsolved goals"}
MISMATCH = ("environment-mismatch: the proof checks under the legacy toolchain it declares, not the pin's; version "
            "skew, not a fault of this host")
RETRY = ("1 pair left to retry (1 with pin oom on attempt 1 of 3; oom is the leg's own memory ceiling, not the host "
         "running out of memory)")
TRUNCATED = "run-truncated: 30 s elapsed and {}'s worst case of 100 s"
LEFT = "2 pairs not reached before the run ceiling"
WEIGH = ("no: nothing needs you today; the classes not reproduced so far are results for you to weigh on the notice "
         "day")
D21 = date.today() - timedelta(days=4)  # the D+21 pilot's day, on a D+25 night


@pytest.mark.parametrize("cut_n, answers, replayed, ceiling, ending", [
    (0, {}, False, TRUNCATED, (
        "accepted 2",
        "1 pair\n  - passed: reproduced 1 (1 with pin accepted and legacy accepted)\n  - not reproduced: none",
        "1 of 3 pairs complete", LEFT, f"no: {LEFT}; pass 1 picks up what is left on its next night")),
    (1, {"compile": [ELAB, {}]}, False, "not reached", (
        "accepted 1, elab-error 1",
        "1 pair\n  - passed: none\n  - not reproduced: environment-mismatch 1 (1 with pin elab-error and legacy "
        f"accepted)\n    - {MISMATCH}", "1 of 1 pairs complete", "nothing", WEIGH)),
    (1, {}, D21, "not reached", (
        "accepted 2",
        "1 pair\n  - passed: none\n  - not reproduced: rejected-by-replay 1 (1 with pin accepted and legacy accepted, "
        f"the class decided on {D21} by the D+21 pilot's replay, before tonight's run, which only completed the legs)",
        "1 of 1 pairs complete", "nothing", WEIGH)),
    (0, {"replay": OOM}, False, TRUNCATED, (
        "accepted 1, oom 1", "none", f"0 of 3 pairs complete; {RETRY}", LEFT,
        f"no: {LEFT} and 1 pair left to retry; pass 1 picks up what is left on its next night"))],
    ids=["truncated", "cut_in_force", "replay_override", "truncated_retry"])
def test_stops_at_pair_boundary_writes_truncated(legs_run, root, make_policy, monkeypatch, cut_n, answers,
                                                 replayed, ceiling, ending):
    """A nightly run on a pass-1 night, its ceiling 120 s and the per-pair limit 20 s: the first pair's two legs, a
    worst case of 100 s, start at 10 s; at 30 s the second's would pass the ceiling, so the run stops at that pair
    boundary with the first pair's legs on disk in the progress file, and its report, at most 40 lines, has every
    field: the mode chosen, run-truncated and why, the legs it ran by outcome, the pair it completed by class with
    the success class apart, pass 1's progress over the sample, the pairs not reached and why, and why that needs no
    operator. With a cut of one pair in force, that pair is the sample and the night completes it, its class given
    with its legs' outcomes and a gloss under the class, and the report says the class not reproduced waits for the
    notice day; a pair the D+21 pilot's replay rejected days before the night says what decided its class, on which
    day, and that the night only completed its legs; when the first pair's pin leg ends oom, a retryable outcome, the
    pair is left to retry and the report gives the attempt, counted from the leg's reopening at the freeze, the bound
    and what oom means. The progress file takes the skipped nights the gate file records, a holder it could not read
    without a PID."""
    # covers: test_run_report_fields
    run, pairs, lean = legs_run(3, limits={"per_pair_wall_clock_s": 20, "run_ceiling_s": 120},
                                sampling={"cut_n": cut_n})
    lean.answers |= answers
    draw = [{"i": p["i"], "pair_id": p["pair_id"], "decl": p["pair_id"].removesuffix("__p0"), "k": 0,
             "position": p["i"], "split": "lean_workbook", "element_sha256": f"sha256:{p['i']:064x}"} for p in pairs]
    (root / "work/sample.json").write_text(json.dumps({"draw": draw}))
    (root / "work/assembled.jsonl").write_text("".join(json.dumps(p | {"element_sha256": d["element_sha256"]}) + "\n"
                                                       for p, d in zip(pairs, draw)))
    prior = progress.load(root / "results/progress.json",
                          "sha256:" + hashlib.sha256((root / "work/sample.json").read_bytes()).hexdigest())
    prior.start_attempt(pairs[0]["pair_sha256"], "pin")  # the D+14 pilot's, its leg reopened at the freeze
    prior.reopen({pairs[0]["pair_sha256"]: None})
    today = date.today()
    if replayed:  # as the D+21 pilot's replay records a rejection on that day
        prior.remove({pairs[0]["pair_sha256"]: {"source": "d21-pilot", "constant": "x"}}, "rejected-by-replay",
                     replayed)
    pol = run.pol
    gatefile.append(pol, "d0", "met", "operator", "pin commit", today - timedelta(days=25))
    gatefile.append(pol, "skipped-night", "skipped", "pipeline", "lock held by pid unknown; cause=lock",
                    today - timedelta(days=1))
    gatefile.append(pol, "skipped-night", "skipped", "pipeline", "lock held by pid 4242; cause=d30-rebuild", today)
    ticks = iter([0, 10, 30])
    monkeypatch.setattr(legs, "pass1", functools.partial(legs.pass1, clock=lambda: next(ticks)))
    monkeypatch.setattr(confine, "apply_fs", lambda pol: None)  # in place of the one that would confine this test
    monkeypatch.setattr(preflight, "CHECKS", ())
    monkeypatch.setattr(constants, "load", lambda repo: run.consts)
    assert cli.main(["nightly", "--policy", str(make_policy())]) == 0
    prog = json.loads((root / "results/progress.json").read_text())
    assert [sorted(prog["legs"].get(p["pair_sha256"], {})) for p in pairs] == [["legacy", "pin"], [], []]
    assert prog["skipped_nights"] == [{"date": (today - timedelta(days=1)).isoformat(), "cause": "lock"},
                                      {"date": today.isoformat(), "holder_pid": 4242, "cause": "d30-rebuild"}]
    report = next(root.glob("runs/*/report.md")).read_text()
    found = dict(re.findall(r"^- ([^:]+): (.*(?:\n +- .*)*)", report, re.M))
    assert len(report.splitlines()) <= 40 and tuple(found) == FIELDS
    assert found["mode"] == "pass1, D+25: a pass-1 night" and found["result"] == "exit 0"
    assert found["ceiling"].startswith(ceiling.format(pairs[1]["pair_id"]))
    assert found["attempted"] == "legs 2 (legacy 1, pin 1), pairs 1"
    assert (found["leg outcomes"], found["classes of the pairs completed"], found["pass 1"], found["skipped"],
            found["needs the operator"]) == ending
    assert found["code_commit"] == COMMIT
