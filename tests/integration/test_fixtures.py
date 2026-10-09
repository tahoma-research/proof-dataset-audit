import json
import os
import re
import shutil
from pathlib import Path

import pytest
from helpers import PY, REPO, in_unit, write_policy

from ledger import fixtures

pytestmark = [pytest.mark.integration, pytest.mark.slow]

SCRIPT = """
import dataclasses, json, os, sys
from datetime import date
from ledger import confine, fixtures, policy
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
(tmp := pol.root / "tmp" / sys.argv[2]).mkdir(parents=True, exist_ok=True)
os.environ["TMPDIR"] = str(tmp)
print(json.dumps(dataclasses.asdict(fixtures.run_proof1b(pol, 600, date.today()))))
"""


@pytest.fixture(scope="module")
def proof1b(tmp_path_factory):
    """Proof 1b run once in the development environment, from a systemd user unit, over the fixture project as
    stage copies it beside the public tree. Returns the report, and per run its results directory and the victim's
    pin leg result."""
    if not os.environ.get("LEDGER_DEV_ROOT"):
        pytest.skip("LEDGER_DEV_ROOT is unset: integration tests need the development environment")
    dev_root, tmp = Path(os.environ["LEDGER_DEV_ROOT"]), tmp_path_factory.mktemp("proof1b")
    made = [dev_root / "fixtures-src/proof1b", dev_root / "fixtures-run/proof1b",
            dev_root / "tmp" / f"proof1b-{tmp.name}", dev_root / "fixtures-run/env/proof1b",
            dev_root / "fixtures-run/tmp/proof1b"]
    shutil.copytree(REPO / "fixtures/proof1b", made[0])
    try:
        ran = in_unit(PY, "-c", SCRIPT, write_policy(tmp / "policy.toml", dev_root), made[2].name,
                      env={"LEDGER_DEV_ROOT": dev_root}, timeout=3600)
        assert ran.code == 0, ran.err[-3000:]
        pairs = json.loads((made[1] / "work/sample.json").read_text())
        victim = next(pair["pair_sha256"] for pair in pairs if pair["pair_id"] == "victim__p0")[7:]
        runs = {n: (made[1] / f"run-{n}", json.loads((made[1] / f"run-{n}/legs/{victim}.pin.1.json").read_text()))
                for n in (1, 2)}
        yield json.loads(ran.out), runs
    finally:
        for path in made:
            if path.exists():
                shutil.rmtree(path)


def test_proof1b_fresh_rejects_attributes_by_walk_removes_reruns(proof1b):
    """Run 1: with the victim's per-pair replay bypassed, its leg is accepted and it enters the aggregate; the
    aggregate's --fresh replay rejects planted_false, which no member's name prefixes, so the dependency walk
    attributes it to the victim; its class is rejected-by-replay and it is removed; and the aggregate rebuilt over
    the remainder replays clean."""
    report, runs = proof1b
    results, victim = runs[1]
    assert (report["passed"], report["classes"][0]) == (True, "rejected-by-replay"), report["evidence"]
    assert (victim["outcome"], victim["replay"], victim["dev_overlay"]) == ("accepted", None, True)
    progress = json.loads((results / "progress.json").read_text())
    (override,) = progress["replay_overrides"].values()
    assert (override["source"], override["constant"]) == ("d21-proof-1b", "planted_false")
    assert json.loads((results / "logs/aggregate-walk.log").read_text()) == {"member": "victim__p0"}
    assert (results / "membership.txt").read_text().splitlines()[1:] == ["companion__p0"]
    replayed = (results / "logs/aggregate-replay.log").read_text()
    assert "replaying Aggregate with --fresh" in replayed and "while replaying declaration" not in replayed


def test_proof1b_per_pair_replay_rejects_without_bypass(proof1b):
    """Run 2: with no bypass, the victim's per-pair replay rejects planted_false in pass 1, so it is replay-reject,
    its class rejected-by-replay, and never enters the aggregate, which replays clean without it."""
    report, runs = proof1b
    results, victim = runs[2]
    assert (report["passed"], report["classes"][1]) == (True, "rejected-by-replay"), report["evidence"]
    assert (victim["outcome"], victim["table_row"]) == ("replay-reject", "pin.replay.reject")
    assert victim["replay"]["rejected_constant"] == "planted_false" and victim["audit"] is None
    assert (results / "membership.txt").read_text().splitlines()[1:] == ["companion__p0"]
    assert "replay_overrides" not in json.loads((results / "progress.json").read_text())
    assert "replaying Aggregate with --fresh" in (results / "logs/aggregate-replay.log").read_text()


SET = """
import dataclasses, json, os, shutil, sys
from datetime import date
from ledger import REPO, confine, constants, fixtures, policy, preflight
preflight.headroom = lambda *_: 2  # two legs at once: the host's development runs stay small
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
(tmp := pol.root / "tmp" / sys.argv[2]).mkdir(parents=True, exist_ok=True)
os.environ["TMPDIR"] = str(tmp)
consts = constants.load(REPO)
consts = dataclasses.replace(consts, published=consts.published | {
    "status": consts.published["status"] | {"legacy": sys.argv[3]}})
print(json.dumps(dataclasses.asdict(fixtures.run_fixture_set(pol, consts, date.today()))))
shutil.rmtree(tmp)
"""


def trees(dev_root: Path) -> dict[str, tuple[int, int]]:
    """Every entry of the development environment's own trees, with its size and modification time."""
    return {str(path): (path.lstat().st_size, path.lstat().st_mtime_ns)
            for tree in ("pin", "legacy") for path in (dev_root / "env" / tree).rglob("*")}


@pytest.fixture(scope="module")
def fixture_run(tmp_path_factory):
    """The fixture run in the development environment, from a systemd user unit, over the planted entries as stage
    copies them beside the public tree: once with the legacy environment standing, once with it unavailable. Returns
    per branch the report and the planted records by pair_id, and under "trees" the development environment's own
    trees before and after."""
    if not os.environ.get("LEDGER_DEV_ROOT"):
        pytest.skip("LEDGER_DEV_ROOT is unset: integration tests need the development environment")
    dev_root, tmp = Path(os.environ["LEDGER_DEV_ROOT"]), tmp_path_factory.mktemp("set")
    made = [dev_root / "fixtures-src/planted", dev_root / "fixtures-run", dev_root / "tmp" / f"set-{tmp.name}"]
    shutil.copytree(REPO / "fixtures/planted", made[0])
    found = {"trees": [trees(dev_root)]}
    try:
        for legacy in ("standing", "environment-unavailable"):
            ran = in_unit(PY, "-c", SET, write_policy(tmp / "policy.toml", dev_root), made[2].name, legacy,
                          env={"LEDGER_DEV_ROOT": dev_root}, timeout=3600)
            assert ran.code == 0, ran.err[-3000:]
            lines = (made[1] / "planted/results/records.jsonl").read_text().splitlines()
            found[legacy] = json.loads(ran.out), {r["pair_id"]: r for r in map(json.loads, lines)}
        found["trees"].append(trees(dev_root))
        yield found
    finally:
        for path in made:
            if path.exists():
                shutil.rmtree(path)


def axioms(record, kind: str) -> dict:
    return {a["name"]: a for a in record["legs"]["pin"]["audit"]["decls"][0][f"axioms_{kind}"]}


def test_proof1_kernel_failure_flagged_excluded_counted(fixture_run):
    """Proof 1: the planted kernel failure is rejected by the kernel at both revisions, kept with its record and
    reason, counted, and rejected-by-checker, outside the reproduced set and the aggregate."""
    report, found = fixture_run["standing"]
    record = found["planted_kernel__p0"]
    assert report["verdicts"]["d21-proof-1"][0] is True, report
    assert [record["legs"][env]["outcome"] for env in ("pin", "legacy")] == ["kernel-reject"] * 2
    assert "(kernel) declaration type mismatch" in record["legs"]["pin"]["compile"]["diagnostics"]
    assert (record["class"], record["aggregate"]["member"]) == ("rejected-by-checker", False)


def test_proof2_injected_axiom(fixture_run):
    """Proof 2: the entry depending on an axiom its own text declares compiles with exit 0, and the audit makes it
    an axiom-audit-failure at both revisions."""
    report, found = fixture_run["standing"]
    record = found["planted_axiom__p0"]
    assert report["verdicts"]["d21-proof-2"][0] is True, report
    assert record["legs"]["pin"]["compile"]["exit"] == 0 and record["class"] == "axiom-audit-failure"
    assert axioms(record, "walk")["planted_ax"]["module"] is None


def test_proof2_synthetic_sorry(fixture_run):
    """Proof 2: the entry closed by `sorry` compiles with exit 0 and is an axiom-audit-failure through sorryAx."""
    _, found = fixture_run["standing"]
    record = found["planted_sorry__p0"]
    assert record["legs"]["pin"]["compile"]["exit"] == 0 and record["class"] == "axiom-audit-failure"
    assert "sorryAx" in axioms(record, "walk")


def test_proof2_axiom_behind_axiom(fixture_run):
    """Proof 2, with the lean4#8840 guard: sorryAx, reached only through another axiom's type, is found by the
    independent walk, and the entry is an axiom-audit-failure."""
    _, found = fixture_run["standing"]
    record = found["planted_behind__p0"]
    assert record["legs"]["pin"]["compile"]["exit"] == 0 and record["class"] == "axiom-audit-failure"
    assert {"planted_outer", "sorryAx"} <= axioms(record, "walk").keys()


def test_proof3_mismatch_and_undeclared_excluded_from_rate_counted_neutral_heading(fixture_run):
    """Proof 3: the entry failing at the pin and checking at its declared revision is environment-mismatch; the one
    failing at the pin and declaring none, its legacy leg never run, is environment-undeclared. Both are recorded,
    so counted, and both classes are outside the mathematics classes the rate counts."""
    report, found = fixture_run["standing"]
    mismatch, undeclared = found["planted_mismatch__p0"], found["planted_undeclared__p0"]
    assert report["verdicts"]["d21-proof-3"][0] is True, report
    assert (mismatch["legs"]["pin"]["outcome"], mismatch["legs"]["legacy"]["outcome"]) == ("elab-error", "accepted")
    assert (undeclared["declared"], undeclared["legs"]["legacy"]) == ("none", None)
    assert [mismatch["class"], undeclared["class"]] == ["environment-mismatch", "environment-undeclared"]
    assert not {mismatch["class"], undeclared["class"]} & {"rejected-by-checker", "axiom-audit-failure",
                                                           "rejected-by-replay"}


def test_proof3b_collision_refused_at_assembly(fixture_run):
    """Proof 3b: the entry whose declaration name collides with its neighbour's is refused at assembly, as
    name-collision, never compiled, and a harness-error."""
    _, found = fixture_run["standing"]
    record = found["#7__p0"]
    assert (record["refusal"], record["class"], record["legs"]["pin"]["compile"]) == ("name-collision",
                                                                                     "harness-error", None)


def test_proof3b_scope_leak_caught_by_crosspass_run_fails(fixture_run):
    """Proof 3b: the pair that compiles clean alone, but elaborates to another type in the aggregate after its
    neighbour's leaked instance, is caught by the cross-pass rule: a harness-error, and the batch's run failed."""
    report, found = fixture_run["standing"]
    record, evidence = found["planted_victim__p0"], report["verdicts"]["d21-proof-3b"][1]
    assert record["legs"]["pin"]["outcome"] == "accepted" and record["class"] == "harness-error"
    assert (record["overrides"]["harness"]["source"], record["overrides"]["harness"]["detail"]) == (
        "crosspass-d21", "type")
    assert "scope-leak pair caught by the cross-pass rule; the planted batch failed" in evidence


def test_branch_reduction_proofs_1_2_3_when_legacy_unavailable(fixture_run):
    """With the legacy environment unavailable, proofs 1, 2 and 3 pass in their reduced forms: each planted entry
    of proofs 1 and 2 environment-undeclared, its pin-side kernel rejection or offending axiom in its record, and
    proof 3 its undeclared entry alone, no legacy leg run."""
    report, found = fixture_run["environment-unavailable"]
    assert report["reduced"] is True and all(report["verdicts"][f"d21-proof-{n}"][0] for n in "123"), report
    assert "planted_mismatch__p0" not in found and all(r["legs"]["legacy"] is None for r in found.values())
    for pair_id in ("planted_kernel__p0", "planted_axiom__p0", "planted_sorry__p0", "planted_behind__p0"):
        assert (found[pair_id]["class"], found[pair_id]["declared"]) == ("environment-undeclared", "unavailable")
    assert "(kernel)" in found["planted_kernel__p0"]["legs"]["pin"]["compile"]["diagnostics"]
    assert "planted_ax" in axioms(found["planted_axiom__p0"], "walk")


def test_planted_records_only_in_fixture_run(fixture_run):
    """Every planted pair's record is in the fixture run's own result set, no planted digest is anywhere in the
    development environment's real result set, and its own trees are as they were: no entry added, removed or
    written."""
    _, found = fixture_run["standing"]
    dev_root = Path(os.environ["LEDGER_DEV_ROOT"])
    assert len(found) == len(fixtures.EXPECTED) == len(json.loads((REPO / "fixtures/planted/entries.json").read_text()))
    digests = {record["pair_sha256"].removeprefix("sha256:") for record in found.values()}
    real = [path for path in (dev_root / "results").rglob("*") if path.is_file()]
    assert not [path for path in real if any(d in path.name or d in path.read_text(errors="ignore") for d in digests)]
    before, after = fixture_run["trees"]
    assert before == after, sorted(set(before.items()) ^ set(after.items()))[:10]


def test_assembler_fixture_set_elaboration_agrees_per_pair(fixture_run):
    """The assembler fixture set's pairs that compile clean at the pin elaborate in the aggregate as they do alone:
    no member is removed and the aggregate without the scope-leak fixture is built. With that fixture first, a member
    after it elaborates to another type, which the cross-pass rule catches, and proof 3b passes."""
    passed, evidence = fixture_run["standing"][0]["verdicts"]["d21-proof-3b"]
    clean = re.search(r"assembler set: (\d+) of \d+ clean at the pin, without the scope-leak fixture agreeing, "
                      r"with it first disagreeing by the cross-pass rule", evidence)
    assert passed and clean and int(clean[1]) >= 2, evidence
