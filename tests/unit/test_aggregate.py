import dataclasses
import hashlib
import json
import os
import re
import tomllib
from datetime import date, timedelta
from pathlib import Path

import pytest
from helpers import REPO

from ledger import aggregate, constants, gatefile, legs, progress
from ledger.types import LedgerStop

HEADER = constants.load(REPO).published["assembly"]["header"]
D0 = date(2026, 11, 2)
CEILING = {"replay_cap_s": 50400}  # the cap equal to the ceiling: no replay fits after other work that night
STAMP = r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ"  # an override's `at`, UTC to the second
D14 = {"eb_s": 60, "mb_s": 1, "e_s": 600, "m_s": 10}  # D+14's build and replay figures
AGG_MB = constants.load(REPO).published["limits"]["agg_memory_max_mb"]


def rejected(constant: str) -> dict:
    return {"exit": 1, "output": f"replaying Aggregate with --fresh\nuncaught exception: while replaying declaration "
                                 f"'{constant}':\n(kernel) declaration type mismatch\n"}


def theorem(name: str) -> str:
    return f"{HEADER}theorem {name} : True := by\n  trivial\n"


@pytest.fixture
def night(legs_run, code_repo):
    """n pairs whose pin and legacy legs ran, the pin compile of those in `failed` failing, each pair text the
    published header over its own theorem, and D+0 recorded. Returns (run, pairs, lean), the constants a copy."""
    def make(n, failed=(), **published):
        run, pairs, lean = legs_run(n, **published)
        run = dataclasses.replace(run, consts=dataclasses.replace(run.consts, repo=code_repo))
        for pair in pairs:
            (run.work / "pairs" / f"{pair['pair_id']}.lean").write_text(theorem(pair["pair_id"]))
            for env in ("pin", "legacy"):
                fails = env == "pin" and pair["i"] in failed
                lean.answers["compile"] = {"exit": 1, "output": "Pairs/x.lean:2:8: error: unknown x"} if fails else {}
                legs.run_leg(run, pair, env)
        for kept in (lean.answers, lean.calls, lean.kwargs):
            kept.clear()
        gatefile.append(run.pol, "d0", "met", "operator", "pin commit", D0)
        return run, pairs, lean
    return make


def step(run, pairs, day: int, **d14) -> str:
    return aggregate.step(run, pairs, D0 + timedelta(days=day), **D14 | d14)


def steps(lean) -> list[str]:
    return [s for s, _, _ in lean.calls]


def gates(run) -> list[tuple[str, str]]:
    return [(row[1], row[2]) for row in gatefile.rows(run.pol) if row[1] != "d0"]


def overrides(run, pairs) -> dict:
    """pair_id -> the source of its override, of either kind."""
    ids = {pair["pair_sha256"]: pair["pair_id"] for pair in pairs}
    return {ids[sha]: o["source"] for kind in ("replay_overrides", "harness_overrides")
            for sha, o in run.progress.data.get(kind, {}).items()}


def membership(run) -> list[str]:
    return (run.results / "membership.txt").read_text().splitlines()


def test_decl_count_equals_membership():
    """The aggregate is the header once, byte for byte the pairs' own, then each member's declaration text in
    order, one blank line between members; each member's line range is recorded."""
    # covers: test_exactly_one_header_byte_identical
    two_lines = HEADER + "theorem b__p1 :\n    True := by\n  trivial\n"
    text, ranges = aggregate.assemble([("a__p0", theorem("a__p0")), ("b__p1", two_lines)], HEADER)
    assert text == HEADER + "theorem a__p0 : True := by\n  trivial\n\ntheorem b__p1 :\n    True := by\n  trivial\n"
    assert ranges == {"a__p0": (5, 6), "b__p1": (8, 10)}


@pytest.mark.parametrize("texts, reason", [
    ([("a__p0", theorem("a__p0")), ("a__p0", theorem("a__p0"))], "unique"),
    ([("a__p0", theorem("a__p0") + theorem("c__p0").replace("c__p0", "c"))], "import"),
    ([("a__p0", HEADER + "import Pairs.b__p0\n" + theorem("a__p0").removeprefix(HEADER))], "import"),
    ([("a__p0", theorem("a__p0").removeprefix(HEADER))], "header"),
    ([("a__p0", theorem("b__p0"))], "declare"),
], ids=["test_names_unique", "test_second_header_fails", "test_no_import_of_pair_module", "header-differs",
        "declares-another"])
def test_assembly_refused(texts, reason):
    """No aggregate is assembled with a name twice, a second header or any import below the first, a pair text
    whose header is not the aggregate's, or a pair text that does not declare its own pair."""
    with pytest.raises(LedgerStop, match=reason):
        aggregate.assemble(texts, HEADER)


@pytest.mark.parametrize("constant, walked, member", [
    ("b__p1", None, "b__p1"),
    ("_private.Aggregate.0.b__p1._proof_1", None, "b__p1"),
    ("b__p1._proof_3", None, "b__p1"),
    ("_auxLemma.4", "a__p0", "a__p0"),
    ("b__p10._proof_3", None, None),
], ids=["test_prefix_attribution", "test_private_prefix_stripped", "test_proof_n_to_parent", "test_walk_attribution",
        "unresolved"])
def test_attribute(constant, walked, member):
    """A rejected constant belongs to the member whose name it is or extends by whole components, after any
    _private prefix is stripped; only otherwise is the dependency walk asked, with the constant as named."""
    asked = []
    assert aggregate.attribute(constant, ["a__p0", "b__p1"], lambda c: asked.append(c) or walked) == member
    assert asked == ([constant] if walked or not member else [])


def test_failed_pass1_absent_classified_counted(night):
    """D+44 with pass 1 complete: the d43 line is met; the aggregate is built with `lake --no-cache build Aggregate`
    in the pin tree from the pairs that compiled cleanly, listed in membership.txt; a pair that failed pass 1 is
    absent from it, keeps its pass-1 outcome and gets no override; the replay returns and the check is done."""
    # covers: test_built_with_lake_build
    run, pairs, lean = night(3, failed={1})
    assert step(run, pairs, 44) == "replay-returned"
    build = [(cmd, cwd) for s, cmd, cwd in lean.calls if s == "build"]
    assert [cmd[1:] for cmd, _ in build] == [["--no-cache", "build", "Aggregate"]] and build[0][1].name == "pin"
    digest = hashlib.sha256(b"p0__p0\np2__p0\n").hexdigest()
    assert membership(run) == [f"# members=2 sha256={digest}", "p0__p0", "p2__p0"]
    assert run.progress.aggregate()["membership_sha256"] == f"sha256:{digest}"
    assert "p1__p0" not in (run.pol.root / "env/pin/Aggregate.lean").read_text()
    pin = run.progress.data["legs"][pairs[1]["pair_sha256"]]["pin"]["leg"]
    assert json.loads((run.results / pin).read_text())["outcome"] == "elab-error" and overrides(run, pairs) == {}
    assert gates(run) == [("d43", "met")] and steps(lean) == ["build", "audit", "replay"]
    assert "--skip-missing" in next(cmd for s, cmd, _ in lean.calls if s == "audit")


AUDIT = "".join(json.dumps({"name": f"p{i}__p0", "axioms_collector": [], "axioms_walk": [], "type_hash": str(i % 2 + 1),
                            "type_pp": "True"}) + "\n" for i in range(3))


@pytest.mark.parametrize("start, published, answers, end, removed, called", [
    ("build-pending", {"limits": CEILING}, {}, ("replay-pending", 0), {}, ["build", "audit"]),
    ("build-pending", {"status": {"independent_check": "replay-unavailable"}}, {},
     ("replay-unavailable", 0), {}, ["build", "audit"]),
    ("build-pending", {}, {"build": {"exit": 1, "output": f"error: Aggregate.lean:8:2: unknown {'ℕ' * 999}\n"}},
     ("build-pending", 1), {"p1__p0": "aggregate-elab"}, ["build"]),
    ("rejected-rerun-pending", {"limits": CEILING}, {}, ("replay-pending", 1), {}, ["build", "audit"]),
    ("rejected-rerun-pending", {}, {"audit": {"output": AUDIT}}, ("build-pending", 2), {"p1__p0": "crosspass-d44"},
     ["build", "audit"]),
    ("rejected-rerun-pending", {}, {"build": {"exit": -9, "killed": "wall-clock"}}, ("build-pending", 2), {},
     ["build"]),
], ids=["test_state_build_pending_built", "test_state_build_pending_built_unavailable",
        "test_state_build_pending_removed", "test_state_rejected_rerun_pending_built",
        "test_state_rejected_rerun_pending_removed", "test_state_rejected_rerun_pending_cut"])
def test_build_states(night, start, published, answers, end, removed, called):
    """A build-pending or rejected-rerun-pending night builds over the current members and runs the cross-pass
    comparison. Clean, it is replay-pending, or replay-unavailable on that branch, and a replay that does not fit
    what remains of the ceiling waits. A member whose lines hold an elaboration error, or whose observables differ
    from pass 1's, is removed as harness-error, the batch fails with no replay, and the next night rebuilds as a
    re-run, its override's detail the first KiB of the error. A rebuild over its budget is over the cap, a cut the
    next night carries out as a re-run."""
    # covers: test_elab_error_attributed_by_line_range, test_mismatch_is_harness_error_and_failed_run
    run, pairs, lean = night(3, **published)
    run.progress.aggregate().update(state=start, reruns_used=int(start == "rejected-rerun-pending"))
    lean.answers.update(answers)
    assert step(run, pairs, 45) == end[0] and run.progress.aggregate()["reruns_used"] == end[1]
    assert overrides(run, pairs) == removed and steps(lean) == called
    assert [r["cause"] for r in run.progress.aggregate()["removals"]] == ["harness-error"] * len(removed)
    assert all(len(o["detail"].encode()) <= 1024 for o in run.progress.data.get("harness_overrides", {}).values())


def test_replay_crash_resumes(night, monkeypatch):
    """A replay starts only after replay-running is on disk; a run that dies during it leaves that state, which the
    next night's run, holding the lock, takes as replay-pending and replays first, with no build; a replay that
    returns with no rejection is replay-returned."""
    # covers: test_state_replay_pending_started, test_state_replay_running_resumed, test_state_replay_running_returned
    run, pairs, lean = night(2, limits=CEILING)
    assert step(run, pairs, 44) == "replay-pending"

    def dies(*args, **kwargs):
        raise SystemExit("killed")
    monkeypatch.setattr(aggregate.confine, "run", dies)
    with pytest.raises(SystemExit):
        step(run, pairs, 45)
    monkeypatch.setattr(aggregate.confine, "run", lean)
    lean.calls.clear()
    assert json.loads(run.progress.path.read_text())["aggregate"]["state"] == "replay-running"
    assert step(run, pairs, 45) == "replay-returned" and steps(lean) == ["replay"]


def test_replay_without_fresh_line_stops(night):
    """A replay that exits 0 without the line saying it replayed the aggregate with --fresh stops the run."""
    run, pairs, lean = night(1)
    lean.answers["replay"] = {"output": "replaying Aggregate\n"}
    with pytest.raises(LedgerStop, match="replaying Aggregate with --fresh"):
        step(run, pairs, 44)


def test_member_rejection_is_rejected_by_replay_and_removed(night):
    """A --fresh rejection of a member's auxiliary constant, its primed name read whole, makes that member
    rejected-by-replay (never a cross-pass harness error) and removes it; the next night rebuilds without it and
    replays, as a re-run."""
    # covers: test_state_replay_running_rejected, test_fresh_verdict_not_a_crosspass_observable
    run, pairs, lean = night(3)
    lean.answers["replay"] = rejected("p1__p0.helper'")
    assert step(run, pairs, 44) == "rejected-rerun-pending"
    sha = pairs[1]["pair_sha256"]
    (override,) = run.progress.data["replay_overrides"].values()
    assert list(run.progress.data["replay_overrides"]) == [sha] and re.fullmatch(STAMP, override["at"])
    assert override | {"at": None} == {"source": "d44", "constant": "p1__p0.helper'", "date": "2026-12-16", "at": None}
    assert "harness_overrides" not in run.progress.data
    agg = run.progress.aggregate()
    assert agg["removals"] == [{"pair_sha256": sha, "cause": "rejected-by-replay", "date": "2026-12-16"}]
    lean.answers.clear()
    assert step(run, pairs, 45) == "replay-returned" and membership(run)[1:] == ["p0__p0", "p2__p0"]
    assert agg["reruns_used"] == 1 and agg["extension"] == "unspent"


WALKED = rejected("_auxLemma.2")
KILLED = {"exit": -9, "killed": "wall-clock"}
OOM = {"exit": -9, "killed": "oom", "oom_kill": 1}
UNRESOLVED = "a rejection resolving to no pair: "


@pytest.mark.parametrize("answers, cause", [
    ({"build": {"exit": 1, "output": "error: Aggregate.lean:2:0: unknown namespace 'X'\nerror: build failed\n"}},
     "a build error outside every member"),
    ({"build": {"exit": 1, "output": "error: build failed\n"}}, "a build error outside every member"),
    ({"build": {"exit": 1, "output": "error: Aggregate.lean:5:0: x\n", "output_truncated": True}},
     "build output truncated"),
    ({"build": KILLED}, "the build passed its budget of 93 s"),
    ({"build": OOM}, "the build passed its memory cap (oom)"),
    ({"audit": OOM}, "the aggregate's audit was killed (oom)"),
    ({"audit": {"exit": 1, "output": ""}}, "the aggregate's audit exited 1"),
    ({"replay": WALKED, "walk": {"output": '{"member": null, "reason": "tie"}\n'}}, f"{UNRESOLVED}_auxLemma.2"),
    ({"replay": WALKED, "walk": {"output": '{"member": null, "reason": "imported"}\n'}}, f"{UNRESOLVED}_auxLemma.2"),
    ({"replay": WALKED, "walk": OOM}, f"{UNRESOLVED}_auxLemma.2; the dependency walk was killed (oom)"),
    ({"replay": WALKED, "walk": {"exit": 1, "output": ""}}, f"{UNRESOLVED}_auxLemma.2; the dependency walk exited 1"),
    ({"replay": {"exit": 1, "output": "replaying Aggregate with --fresh\nINTERNAL PANIC: out of memory\n"}},
     f"{UNRESOLVED}no constant named"),
    ({"replay": KILLED}, "the replay was killed (wall-clock) under the cap of 43200 s"),
], ids=["test_error_outside_members_is_run_harness_error", "build-error-unlocated", "build-output-truncated",
        "build-over-budget", "build-oom", "audit-oom", "audit-failed",
        "test_unresolved_is_run_harness_error_not_distributed", "walk-imported", "walk-oom", "walk-failed",
        "no-constant", "replay-over-cap"])
def test_over_the_cap(night, answers, cause):
    """A build error outside every member, a build failure naming no line or whose output was cut short, passing
    its budget B (D+14's, the member count in place of the sample size) or its memory cap, the aggregate's audit
    over its memory cap or failing, a rejection resolving to no pair (a tie, an imported constant, a walk over its
    memory cap or failing, or no constant named) and a replay killed at the cap are a harness error of the run,
    never distributed: no member is overridden or removed, and the run is over the cap with that cause, which is
    the kill once the re-scope is spent, and the next night runs nothing. The build, the audit, the walk and the
    replay, with no replay floor set yet, run under agg_memory_max_mb; every call as proof code runs,
    changing no file's metadata and reading only the system's files, the toolchain and the pin's tree."""
    run, pairs, lean = night(2)
    gatefile.append(run.pol, "rescope", "cut_n=2", "pipeline", "d21", D0 + timedelta(days=21))
    lean.answers.update(answers)
    step(run, pairs, 44)
    assert gates(run)[-1] == ("kill", "over the cap") and gatefile.rows(run.pol)[-1][4].startswith(f"{cause};")
    assert overrides(run, pairs) == {} and run.progress.aggregate()["removals"] == []
    build = next(kwargs for s, kwargs in zip(steps(lean), lean.kwargs) if s == "build")
    assert build["timeout_s"] == 1.5 * (60 + 1 * 2)
    assert all(cmd[1:3] in (["--no-cache", "build"], ["--no-cache", "env"]) for _, cmd, _ in lean.calls)
    assert {kwargs["memory_max_mb"] for kwargs in lean.kwargs} == {AGG_MB}
    assert all(kwargs["no_meta"] and run.pol.root / "env/pin" in kwargs["reads"] for kwargs in lean.kwargs)
    lean.calls.clear()
    step(run, pairs, 45)
    assert steps(lean) == []


@pytest.mark.parametrize("answers, d14, failed, cut", [
    ({"replay": KILLED}, {"e_s": 43000, "m_s": 100}, (), 2),
    ({"build": KILLED}, {"eb_s": 33400, "mb_s": 100}, (), 2),
    ({"replay": KILLED}, {"m_s": 0}, (), None),
    ({"replay": KILLED}, {"e_s": 43150, "m_s": 100}, (), None),
    ({"build": KILLED}, {"mb_s": 0}, (), None),
    ({"replay": KILLED}, {"m_s": 10000}, (), 4),
    ({"replay": KILLED}, {"m_s": 14200}, (1,), 4),
], ids=["test_state_replay_running_cut", "test_state_build_pending_cut", "replay-m-zero", "replay-n-below-1",
        "build-mb-zero", "replay-no-shrink", "replay-no-shrink-failed-pair"])
def test_over_the_cap_cut(night, answers, d14, failed, cut):
    """Over the cap with the re-scope unspent and a re-run left, the pair count is cut to what the measurement
    supports: for a replay N = floor((cap in force - E) / m), for a build the largest N whose B fits the ceiling,
    E, m, Eb and mb D+14's. The cut is written as the re-scope and to cut_n, and counts as a re-run that the next
    night carries out over the first N pairs of the draw. An N below 1, or m = 0, is the kill, and no cut. An N not
    below the members built (fewer than the pairs where one failed pass 1) keeps every pair, cut_n the sample's
    length: one retry, as the rescope line says."""
    run, pairs, lean = night(4, failed=failed)
    lean.answers.update(answers)
    state = step(run, pairs, 44, **d14)
    written = tomllib.loads((run.consts.repo / "recipe/constants.toml").read_text())["sampling"]["cut_n"]
    if cut is None:
        assert gates(run)[-1] == ("kill", "over the cap, no cut fits") and written == 0
        return
    assert gates(run) == [("d43", "met"), ("rescope", f"cut_n={cut}")] and written == cut
    assert ("members: every pair kept, one retry" in gatefile.rows(run.pol)[-1][4]) == (cut == 4)
    assert state == "build-pending" and run.progress.aggregate()["reruns_used"] == 1
    lean.answers.clear()
    run = dataclasses.replace(run, consts=constants.load(run.consts.repo))  # the next night's run reads it
    assert step(run, pairs, 45, **d14) == "replay-returned"
    assert membership(run)[1:] == [f"p{i}__p0" for i in range(cut) if i not in failed]


@pytest.mark.parametrize("constant, shown", [
    ("x|y" + "w" * 400, "x_y" + "w" * 197),
    ("«/home/example/.ssh/id»", "[withheld]"),
    ("Mathlib.DENYLISTED-term-zq.x", "[withheld]"),
], ids=["pipe-long", "path", "privacy-sweep"])
def test_untrusted_constant_sanitized_in_gate_lines(night, constant, shown):
    """A rejected constant that resolves to no pair is named in the rescope line through the gate writer's
    sanitizer, | replaced, cut to fit and withheld if the gate writer would refuse it, for a path or an address
    or for anything its privacy sweep finds: the run goes on."""
    run, pairs, lean = night(2)
    lean.answers["replay"] = rejected(constant)
    assert step(run, pairs, 44) == "build-pending"
    assert gatefile.rows(run.pol)[-1][1] == "rescope" and f"no pair: {shown};" in gatefile.rows(run.pol)[-1][4]


@pytest.mark.parametrize("dies_at, state, answers, d14, written", [
    ("rescope", {}, {"replay": KILLED}, {"e_s": 43000, "m_s": 100}, [("d43", "met"), ("rescope", "cut_n=2")]),
    ("kill", {"state": "replay-pending", "reruns_used": 2}, {"replay": rejected("p0__p0")}, {},
     [("d43", "met"), ("kill", "over the cap")]),
    ("d43", None, {}, {}, [("rescope", "cut_n=2"), ("d43", "cut")]),
], ids=["d44-cut", "removal-then-kill", "d43-cut"])
def test_crash_between_files_completed_next_night(night, monkeypatch, dies_at, state, answers, d14, written):
    """A run that dies after a decision's first writes, before its gate line, leaves the rest pending in the
    progress file, saved with the decision: the next night writes them first, each line once, and goes on from
    the state the decision left (a cut to 2 pairs carried out, the kill ending the check)."""
    run, pairs, lean = night(4)
    if state is None:  # pass 1 short at the third pair: the D+43 cut
        run.progress.data["legs"][pairs[2]["pair_sha256"]]["legacy"]["terminal"] = False
    else:
        run.progress.aggregate().update(state)
    lean.answers.update(answers)
    append = gatefile.append

    def dies(pol, gate, *args):
        if gate == dies_at:
            raise SystemExit("killed")
        append(pol, gate, *args)
    monkeypatch.setattr(gatefile, "append", dies)
    with pytest.raises(SystemExit):
        step(run, pairs, 44, **d14)
    monkeypatch.setattr(gatefile, "append", append)
    lean.answers.clear()
    run = dataclasses.replace(run, consts=constants.load(run.consts.repo))  # the next night's run
    end = step(run, pairs, 45, **d14)
    assert gates(run) == written and run.progress.aggregate()["pending"] == []
    if dies_at == "kill":
        assert end == "replay-running" and overrides(run, pairs) == {"p0__p0": "d44"}
    else:
        assert end == "replay-returned" and membership(run)[1:] == ["p0__p0", "p1__p0"]


DEEP = [Path("lib/lean/Deep", *["x"] * i) for i in range(1100)]  # nested deeper than shutil.rmtree recurses
CHANGED = "the build changed an existing entry or Pairs/ under .lake/build"
TAMPER = {
    "existing-changed": lambda build: (build / "lib/lean/Kept.olean").write_text("KEPT"),  # same size: only ctime moves
    "pairs-new": lambda build: (build / "lib/lean/Pairs/Init.olean").write_text("planted"),
    "unremovable": lambda build: [(build / path).mkdir() for path in DEEP],
}


@pytest.mark.parametrize("tamper, cause", [
    ("existing-changed", CHANGED), ("pairs-new", CHANGED),
    ("unremovable", "an entry the build planted under .lake/build could not be removed"),
], ids=list(TAMPER))
def test_build_changing_its_tree_is_the_kill(night, monkeypatch, tamper, cause):
    """The build's tree, .lake/build, is listed before and after the aggregate's build: a build that changes an
    entry that was there, adds one under the pass-1 outputs in Pairs/ or plants one that cannot be removed leaves
    a tree that is not the one verified. That is the kill outright, with its cause, the re-scope unspent: nothing
    after the build runs, and the next night builds nothing over that tree."""
    run, pairs, lean = night(2)
    build = run.pol.root / "env/pin/.lake/build"
    (build / "lib/lean/Kept.olean").write_text("kept")

    def tampers(cmd, **kwargs):
        if "build" in cmd:
            TAMPER[tamper](build)
        return lean(cmd, **kwargs)
    monkeypatch.setattr(aggregate.confine, "run", tampers)
    try:
        step(run, pairs, 44)
        step(run, pairs, 45)
        kill = gatefile.rows(run.pol)[-1]
        assert kill[1:3] == ("kill", "build tree changed") and kill[4].startswith(f"{cause};")
        assert steps(lean) == ["build"]
    finally:  # what rmtree cannot remove, pytest's tmp cleanup cannot either
        for path in reversed(DEEP) if (build / DEEP[0]).exists() else ():
            (build / path).rmdir()


def test_planted_build_entries_removed_and_recorded(night, monkeypatch):
    """New entries the build leaves under .lake/build beyond the aggregate's own outputs, Lake's exact files for
    Aggregate (an Init/ that would shadow the toolchain's, holding directories their owner cannot list, one in the
    other; a link out of the tree; a file at the top; another file in ir/ or under Aggregate's name) are removed,
    no link followed, and recorded with the build; the night goes on to its replay."""
    run, pairs, lean = night(2)
    build, outside = run.pol.root / "env/pin/.lake/build", run.pol.root / "outside"
    (outside / "kept").mkdir(parents=True)

    def plants(cmd, **kwargs):
        if "build" in cmd:
            (build / "lib/lean/Init").mkdir()
            os.mkdir(build / "lib/lean/Init/locked", 0o300)
            os.mkdir(build / "lib/lean/Init/locked/locked", 0o300)
            for path in ("ir/Aggregate.c", "ir/plant.c", "lib/lean/Aggregate.olean", "lib/lean/Aggregate.evil",
                         "lib/lean/Init/locked/locked/Prelude.olean", "x"):
                (build / path).write_text("built")
            (build / "lib/lean/Outside").symlink_to(outside)
        return lean(cmd, **kwargs)
    monkeypatch.setattr(aggregate.confine, "run", plants)
    assert step(run, pairs, 44) == "replay-returned"
    assert run.progress.aggregate()["last_build"]["planted"] == [
        "ir/plant.c", "lib/lean/Aggregate.evil", "lib/lean/Init", "lib/lean/Outside", "x"]
    left = {str(path.relative_to(build)) for path in build.rglob("*") if "Pairs" not in path.parts}
    assert left == {"ir", "ir/Aggregate.c", "lib", "lib/lean", "lib/lean/Aggregate.olean"}
    assert (outside / "kept").is_dir()


def test_missing_decl_removed_as_harness_error(night):
    """A member the build passed but whose declaration is missing from the built aggregate (the audit, told to
    skip such names, prints no line for it) is removed as harness-error on the elaboration observable; the run
    goes on."""
    run, pairs, lean = night(3)
    lean.answers["audit"] = {"output": "".join(line + "\n" for line in AUDIT.splitlines() if "p1__p0" not in line)}
    assert step(run, pairs, 44) == "build-pending" and run.progress.aggregate()["reruns_used"] == 1
    (override,) = run.progress.data["harness_overrides"].values()
    assert override["source"] == "crosspass-d44" and override["detail"] == "elaboration"
    assert overrides(run, pairs) == {"p1__p0": "crosspass-d44"}


def test_removal_and_transition_one_save(night, monkeypatch):
    """A removal and the state transition it drives are on disk together: no saved progress file holds a removal
    without its re-run counted."""
    run, pairs, lean = night(3)
    saved, write = [], progress.write_atomic
    monkeypatch.setattr(progress, "write_atomic",
                        lambda path, data: saved.append(json.loads(data)) or write(path, data))
    lean.answers["replay"] = rejected("p1__p0")
    assert step(run, pairs, 44) == "rejected-rerun-pending"
    agg = [s["aggregate"] for s in saved if "aggregate" in s]
    assert agg[-1]["removals"] and all(len(a["removals"]) == a["reruns_used"] for a in agg)


def test_third_rerun_over_cap(night):
    """A member rejection once both re-runs are used needs a third, which is over the cap: the member is still
    rejected-by-replay, and with no re-run left the run is the kill."""
    run, pairs, lean = night(2)
    run.progress.aggregate().update(state="replay-pending", reruns_used=2)
    lean.answers["replay"] = rejected("p0__p0")
    assert step(run, pairs, 45) == "replay-running"
    assert overrides(run, pairs) == {"p0__p0": "d44"} and gates(run)[-1] == ("kill", "over the cap")


def test_illegal_transition_raises(night):
    """Only the PRD's transitions are legal: no replay result before a replay started, nothing after a return."""
    run, _, _ = night(1)
    with pytest.raises(LedgerStop, match="no transition from build-pending on returned"):
        run.progress.transition("returned")
    run.progress.aggregate()["state"] = "replay-returned"
    with pytest.raises(LedgerStop, match="no transition"):
        run.progress.transition("built")


def test_extension_only_d46(night, monkeypatch):
    """The extension is spent by the D+46 run alone, once, when a member rejection returns that night with a
    re-run left, in the same save as the removal; the D+47 run then rebuilds and replays."""
    run, pairs, lean = night(2)
    run.progress.aggregate().update(state="replay-pending", reruns_used=1)
    lean.answers["replay"] = rejected("p1__p0")
    saved, write = [], progress.write_atomic
    monkeypatch.setattr(progress, "write_atomic",
                        lambda path, data: saved.append(json.loads(data)["aggregate"]) or write(path, data))
    assert step(run, pairs, 46) == "rejected-rerun-pending" and run.progress.aggregate()["extension"] == "spent"
    assert all(agg["extension"] == "spent" for agg in saved if agg["removals"])
    lean.answers.clear()
    assert step(run, pairs, 47) == "replay-returned" and "kill" not in dict(gates(run))
    run.progress.aggregate()["state"] = "build-pending"
    with pytest.raises(LedgerStop, match="once"):
        run.progress.transition("built", spend=True)


@pytest.mark.parametrize("start, extension", [("rejected-rerun-pending", "spent"), ("build-pending", "unspent")])
def test_d46_rebuild_without_room_spends_extension_if_driven(night, start, extension):
    """A D+46 re-run whose rebuild leaves no room for its replay that night spends the extension with its
    transition only when a member rejection drove it; the D+47 run then replays, and without the extension, no D+47
    run working, the D+46 run ends with the kill."""
    run, pairs, lean = night(2, limits=CEILING)
    run.progress.aggregate().update(state=start, reruns_used=1)
    assert step(run, pairs, 46) == "replay-pending" and run.progress.aggregate()["extension"] == extension
    if extension == "spent":
        assert "kill" not in dict(gates(run))
        assert step(run, pairs, 47) == "replay-returned" and "kill" not in dict(gates(run))
    else:
        assert gates(run)[-1] == ("kill", "replay not returned by D+47")


@pytest.mark.parametrize("day, extension", [(47, "unspent"), (47, "spent"), (48, "unspent")])
def test_kill_at_d47(night, day, extension):
    """The D+47 run works only under the extension: without it, it writes the kill and runs nothing; with it, a
    re-run whose rebuild leaves no room for its replay that night ends D+47 with no returned replay, the kill. A
    night after D+47 is the kill too."""
    run, pairs, lean = night(2, limits=CEILING)
    run.progress.aggregate().update(state="rejected-rerun-pending", reruns_used=1, extension=extension)
    assert step(run, pairs, day) == ("replay-pending" if extension == "spent" else "rejected-rerun-pending")
    assert steps(lean) == (["build", "audit"] if extension == "spent" else [])
    assert gates(run)[-1] == ("kill", "replay not returned by D+47")


@pytest.mark.parametrize("answers, state, lines", [
    ({}, "replay-returned", []),
    ({"build": {"killed": "wall-clock"}}, "build-pending", [("kill", "over the cap")]),
    ({"replay": {"killed": "wall-clock"}}, "replay-running", [("kill", "over the cap")]),
], ids=["returned", "build_over_cap", "replay_over_cap"])
def test_date_free_check(night, answers, state, lines):
    """The D+44 check without its day rules builds and replays from the progress state until the replay returns; with
    no D+14 figures, over the cap, the build's or the replay's, is the kill, never a cut."""
    run, pairs, lean = night(2)
    lean.answers.update(answers)
    aggregate.check(run, pairs, D0)
    assert run.progress.aggregate()["state"] == state and gates(run) == lines


def test_d43_cut_longest_complete_prefix(night):
    """Pass 1 short at D+44: before the aggregate's state is read, the sample is cut to the longest prefix of the
    draw in which every pair is complete, written to cut_n and as the re-scope, once; that night's aggregate is
    built over the cut sample alone."""
    # covers: test_d43_cut_before_state_read
    run, pairs, lean = night(4)
    run.progress.data["legs"][pairs[2]["pair_sha256"]]["legacy"]["terminal"] = False
    assert step(run, pairs, 44) == "replay-returned"
    cut = tomllib.loads((run.consts.repo / "recipe/constants.toml").read_text())["sampling"]["cut_n"]
    assert cut == 2 and membership(run)[1:] == ["p0__p0", "p1__p0"]
    assert gates(run) == [("rescope", "cut_n=2"), ("d43", "cut")] and run.progress.data["d44_cut_written"]


def test_d43_cut_kill_when_spent(night):
    """Pass 1 short at D+44 with the re-scope already spent: the cut is the kill, and nothing is built."""
    run, pairs, lean = night(3)
    run.progress.data["legs"][pairs[1]["pair_sha256"]]["pin"]["terminal"] = False
    gatefile.append(run.pol, "rescope", "cut_n=3", "pipeline", "d21", D0 + timedelta(days=21))
    assert step(run, pairs, 44) == "build-pending" and steps(lean) == []
    assert gates(run)[1:] == [("kill", "d43: pass 1 short and the re-scope spent"), ("d43", "kill")]
    assert tomllib.loads((run.consts.repo / "recipe/constants.toml").read_text())["sampling"]["cut_n"] == 0


def test_d43_cut_to_zero_is_kill(night):
    """Pass 1 short at D+44 with no pair complete at the head of the draw: no cut fits, so it is the kill, with that
    reason, and cut_n stays 0; nothing is built that night or after."""
    run, pairs, lean = night(3)
    run.progress.data["legs"][pairs[0]["pair_sha256"]]["legacy"]["terminal"] = False
    assert step(run, pairs, 44) == "build-pending" and step(run, pairs, 45) == "build-pending" and steps(lean) == []
    assert gates(run) == [("kill", "d43: no pair complete at the head of the draw"), ("d43", "kill")]
    assert tomllib.loads((run.consts.repo / "recipe/constants.toml").read_text())["sampling"]["cut_n"] == 0


def test_step_refuses_before_d44(night):
    """The D+44 check runs from D+44 on."""
    run, pairs, lean = night(1)
    with pytest.raises(LedgerStop, match="before D\\+44"):
        step(run, pairs, 43)
    assert steps(lean) == [] and gates(run) == []
