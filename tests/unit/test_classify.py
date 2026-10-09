import dataclasses
import hashlib
import itertools
import json

import pytest
from conftest import CONSTS
from helpers import REPO

from ledger import classify, cli, confine, progress, records
from ledger.types import LedgerStop

OK = ["accepted", "accepted-env-axiom"]
FAILS = ["elab-error", "kernel-reject", "audit-failure"]
NO_RESULT = ["harness", "unclassified", "timeout-heartbeats", "timeout-wall-clock", "oom", "stack"]
PIN = OK + FAILS + NO_RESULT + ["replay-reject"]
LEGACY = OK + FAILS + NO_RESULT  # the legacy environment has no replay
REPLAY = {"source": "d44", "constant": "X__p0", "date": "2026-12-01", "at": "2026-12-01T03:00:00Z"}
HARNESS = {"source": "aggregate-elab", "detail": "error inside the member's lines", "date": "2026-12-02",
           "at": "2026-12-02T04:45:00Z"}
UNKNOWN = "Pairs/p0__p0.lean:8:8: error(lean.unknownIdentifier): Unknown identifier `outer`\n"


@pytest.mark.parametrize("pin, legacy, replay, harness, declared, cls", [
    pytest.param("accepted", "accepted", None, HARNESS, "standing", "harness-error", id="0"),
    pytest.param("accepted", "accepted", None, HARNESS | {"source": "crosspass-d44"}, "standing", "harness-error",
                 id="test_crosspass_removal_is_harness_error"),
    pytest.param("elab-error", "accepted", None, HARNESS | {"source": "d21-rehearsal"}, "standing", "harness-error",
                 id="test_rehearsal_mismatch_is_harness_error"),
    pytest.param("harness", "accepted", None, None, "standing", "harness-error", id="1"),
    pytest.param("unclassified", "accepted", None, None, "standing", "unclassified", id="2"),
    pytest.param("timeout-heartbeats", "accepted", None, None, "standing", "timed-out", id="3"),
    pytest.param("stack", "accepted", None, None, "standing", "resource-exhausted", id="4"),
    pytest.param("replay-reject", "accepted", None, None, "standing", "rejected-by-replay", id="5"),
    pytest.param("accepted", "elab-error", REPLAY, HARNESS | {"date": REPLAY["date"], "at": "2026-12-01T03:00:01Z"},
                 "standing", "rejected-by-replay", id="replay_override_before_harness_override_same_day"),
    pytest.param("accepted-env-axiom", "elab-error", None, None, "standing", "reproduced", id="6"),
    pytest.param("audit-failure", None, None, None, "unavailable", "environment-undeclared", id="7"),
    pytest.param("kernel-reject", "accepted-env-axiom", None, None, "standing", "environment-mismatch", id="8"),
    pytest.param("elab-error", "audit-failure", None, None, "standing", "axiom-audit-failure", id="9"),
    pytest.param("kernel-reject", "elab-error", None, None, "standing", "rejected-by-checker", id="10"),
    pytest.param("audit-failure", "kernel-reject", None, None, "standing", "axiom-audit-failure", id="11"),
    pytest.param("audit-failure", "timeout-wall-clock", None, None, "standing", "environment-undeclared", id="12"),
])
def test_rule(pin, legacy, replay, harness, declared, cls):
    """Each rule of the class derivation, the first that applies winning: a harness override not preceded by a
    replay override (a cross-pass, rehearsal or aggregate-elaboration mismatch) is harness-error."""
    assert classify.derive(pin, legacy, replay, harness, declared) == cls


@pytest.mark.parametrize("published, declared", [
    pytest.param({"status": {"legacy": "environment-unavailable"}}, "unavailable",
                 id="test_uninstallable_declared_is_undeclared_never_nonrepro"),
    pytest.param({}, "none", id="test_declared_none_is_undeclared_while_legacy_stands"),
])
def test_declared_side_absent(leg_results, published, declared):
    """A pair failing at the pin whose declared revision is not installable, or which declares none while the
    legacy environment stands, is environment-undeclared, never a mathematics class or a skew case, and its
    record carries no legacy leg even where one ran."""
    run, sample, pairs = leg_results([{"pin": {"compile": {"exit": 1, "output": UNKNOWN}}, "legacy": {}}], **published)
    if declared == "none":
        run.progress.data["declared_none"] = [pairs[0]["pair_sha256"]]
    (record,) = records.build(sample, pairs, run.progress, run.results, run.table, run.consts)
    assert (record["declared"], record["legs"]["legacy"], record["recipe_ids"]["legacy"], record["class"],
            record["skew_case"]) == (declared, None, None, "environment-undeclared", None)


@pytest.mark.parametrize("pin, cls", [("harness", "harness-error"), ("unclassified", "unclassified"),
                                      ("timeout-heartbeats", "timed-out"), ("timeout-wall-clock", "timed-out"),
                                      ("oom", "resource-exhausted"), ("stack", "resource-exhausted")])
def test_pin_harness_beats_legacy(pin, cls):
    """A pin outcome with no result decides the class whatever the declared side, a replay override included."""
    for legacy, replay in itertools.product(LEGACY, (None, REPLAY)):
        assert classify.derive(pin, legacy, replay, None, "standing") == cls
    assert classify.derive(pin, None, None, None, "unavailable") == cls


def test_override_beats_environment_classes():
    """A replay override makes every pin result rejected-by-replay, whatever the declared side."""
    for pin, legacy in itertools.product(OK + FAILS, LEGACY + [None]):
        assert classify.derive(pin, legacy, REPLAY, None, "standing" if legacy else "none") == "rejected-by-replay"


def test_legacy_never_labelled_verified():
    """Over every combination, a pair is reproduced exactly when its pin leg was accepted and no override stands
    against it: no declared-side outcome alone ever makes a pair reproduced."""
    for pin, legacy, replay, harness in itertools.product(PIN, LEGACY + [None], (None, REPLAY), (None, HARNESS)):
        cls = classify.derive(pin, legacy, replay, harness, "standing" if legacy else "unavailable")
        assert (cls == "reproduced") == (pin in OK and not replay and not harness)


@pytest.mark.parametrize("pin, legacy, replay, harness, declared", [
    pytest.param(None, "accepted", None, None, "standing", id="no_pin_result"),
    pytest.param("elab-error", None, None, None, "standing", id="no_legacy_result_while_standing"),
    pytest.param("elab-error", "accepted", None, None, "unavailable", id="legacy_result_while_unavailable"),
    pytest.param("accepted", "accepted", REPLAY | {"at": HARNESS["at"]}, HARNESS, "standing",
                 id="replay_override_not_before_harness_override"),
])
def test_incomplete_pair_raises(pin, legacy, replay, harness, declared):
    """A pair without every required leg result, or with a legacy result its declared status excludes, has no
    class; nor do overrides recorded in an order the pipeline cannot produce."""
    with pytest.raises(LedgerStop):
        classify.derive(pin, legacy, replay, harness, declared)


@pytest.mark.parametrize("pin, legacy, replay, harness, case", [
    pytest.param("accepted", "accepted-env-axiom", None, None, "both", id="both"),
    pytest.param("accepted", "kernel-reject", None, None, "pin-only", id="pin-only"),
    pytest.param("accepted", "accepted", REPLAY, None, "declared-only", id="declared-only"),
    pytest.param("kernel-reject", "elab-error", None, None, "fails-both", id="fails-both"),
    pytest.param("accepted", "oom", None, None, "unverifiable-declared", id="unverifiable-declared"),
    pytest.param("elab-error", "timeout-wall-clock", None, None, "unverifiable-declared",
                 id="test_skew_undecided_declared_is_unverifiable"),
    pytest.param("timeout-wall-clock", "accepted", None, None, None, id="no-pin-result"),
    pytest.param("accepted", "accepted", None, HARNESS, None, id="harness-override"),
    pytest.param("elab-error", None, None, None, None, id="legacy-unavailable"),
])
def test_skew(pin, legacy, replay, harness, case):
    """The five skew cases, a pin pass under a replay override counting as no pass and an undecided declared side
    as unverifiable, never a failure; and no case when the pin side has no result or there is no legacy leg."""
    assert classify.skew_case(pin, legacy, replay, harness) == case


def test_frozen_table_hash_enforced(tmp_path):
    """Once the classifier is frozen, only the table with the recorded sha256 loads: one edited byte stops."""
    rel = CONSTS.published["classifier"]["table"]
    (tmp_path / rel).parent.mkdir()
    data = (REPO / rel).read_bytes()
    (tmp_path / rel).write_bytes(data)
    frozen = dataclasses.replace(CONSTS, published=CONSTS.published | {"classifier": CONSTS.published["classifier"] | {
        "status": "frozen", "table_sha256": "sha256:" + hashlib.sha256(data).hexdigest()}})
    assert classify.load(tmp_path, frozen) == classify.load(REPO, CONSTS)
    (tmp_path / rel).write_bytes(data.replace(b"# Leg", b"# leg", 1))
    with pytest.raises(LedgerStop, match="not the frozen table"):
        classify.load(tmp_path, frozen)


def test_substitution_missing_is_harness_error_never_math(leg_results):
    """A pair whose assembled text lacks its proof is refused at assembly; its record is harness-error at both
    environments, never a mathematics class, and nothing was compiled."""
    run, sample, pairs = leg_results([{"refusal": "substitution-missing", "pin": {}, "legacy": {}}])
    (record,) = records.build(sample, pairs, run.progress, run.results, run.table, run.consts)
    assert (record["class"], record["legs"]["pin"]["table_row"], record["legs"]["pin"]["compile"]) == (
        "harness-error", "any.refusal", None)


def test_replay_kill_rows(leg_results):
    """A per-pair replay killed at the wall-clock limit is timed-out, and one killed by the memory ceiling, once
    retries are spent, resource-exhausted: neither is a replay rejection."""
    killed = {"exit": -9, "killed": "wall-clock"}, {"exit": -9, "killed": "oom", "oom_kill": 1}
    run, sample, pairs = leg_results([{"pin": {"replay": kill}, "legacy": {}} for kill in killed],
                                     limits={"attempt_bound": 1})
    built = records.build(sample, pairs, run.progress, run.results, run.table, run.consts)
    assert [(r["legs"]["pin"]["table_row"], r["class"]) for r in built] == [
        ("pin.replay.wallclock", "timed-out"), ("pin.replay.oom", "resource-exhausted")]


def test_reclassify_reproduces_published_classes(leg_results, make_policy, monkeypatch, capsys):
    """A leg left unclassified, and so retryable, by an earlier table keeps its pair from having a record until
    `report --reclassify` derives its outcome again from the stored facts: then it equals a fresh derivation, its
    terminal state follows, a leg killed on every attempt is left as it was, and the pair's record has the class
    a fresh derivation gives."""
    run, sample, pairs = leg_results([{"pin": {"compile": {"exit": 1, "output": UNKNOWN}}, "legacy": {}},
                                      {"pin": None, "legacy": {}}])
    rel = run.progress.data["legs"][pairs[0]["pair_sha256"]]["pin"]["leg"]
    pin, killed = run.results / rel, run.results / run.progress.data["legs"][pairs[1]["pair_sha256"]]["pin"]["leg"]
    killed_before = killed.read_bytes()
    pin.write_text(json.dumps(json.loads(pin.read_text()) | {"outcome": "unclassified", "table_row": "any.unmatched",
                                                             "terminal": False}))
    run.progress.finish(pairs[0]["pair_sha256"], "pin", rel, False)
    with pytest.raises(LedgerStop, match="not terminal"):
        records.build(sample, pairs, run.progress, run.results, run.table, run.consts)

    monkeypatch.setattr(confine, "apply_fs", lambda pol: None)  # the real one would also confine this process
    assert cli.main(["report", "--reclassify", "--policy", str(make_policy())]) == 0
    assert capsys.readouterr().out == f"1 leg outcomes changed\n  {rel}\n"
    prog = progress.load(run.results / "progress.json", run.progress.data["sample_sha256"])
    leg = json.loads(pin.read_text())
    allowlist = run.consts.published["audit"]["allowlist"]
    assert (leg["outcome"], leg["table_row"]) == classify.leg_outcome(classify.facts_of(leg, allowlist), run.table)
    assert leg["terminal"] and prog.data["legs"][pairs[0]["pair_sha256"]]["pin"]["terminal"]
    assert killed.read_bytes() == killed_before
    built = records.build(sample, pairs, prog, run.results, run.table, run.consts)
    assert [r["class"] for r in built] == ["environment-mismatch", "unclassified"]


def test_reclassify_stops_without_progress(make_policy, monkeypatch, capsys):
    """`report --reclassify` over a root with no progress file stops rather than re-deriving nothing."""
    monkeypatch.setattr(confine, "apply_fs", lambda pol: None)  # the real one would also confine this process
    assert cli.main(["report", "--reclassify", "--policy", str(make_policy())]) == 2
    assert "results/progress.json does not exist" in capsys.readouterr().err
