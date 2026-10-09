import dataclasses
import json
import shutil
from datetime import date

import pytest
from helpers import REPO

from ledger import cli, confine, fixtures, freeze, gatefile, legs, policy, preflight
from ledger.types import LedgerStop

TIMING_S = 40  # the D+14 timing of the fixture's --fresh replay
TODAY = date(2026, 11, 23)
REJECTS = {"exit": 1, "output": "replaying Aggregate with --fresh\nuncaught exception: while replaying declaration "
                               "'planted_false':\n(kernel) declaration type mismatch\n"}
CAUGHT = {"replay": [{}, REJECTS, {}, REJECTS, {}, {}], "walk": {"output": '{"member": "victim__p0"}\n'}}


def frozen(pol) -> None:
    """Today's freeze lines, which the fixture run and proof 1b require."""
    for gate in freeze.LINES:
        gatefile.append(pol, gate, "frozen", "pipeline", "test", date.today())


@pytest.fixture
def ledger(legs_run, root, make_policy, code_repo, monkeypatch):
    """`ledger <argv>` in-process over a root whose pin and legacy trees have passed builds, beside which stage copied
    both fixture sources, under a committed copy of the recipe with the legacy environment `legacy` and a cut to two
    pairs written, every process answered by FakeLean; the command's lock, confinement and preflight are not these tests'. Returns the call,
    giving its exit, the FakeLean and the policy."""
    def make(legacy: str = "pending"):
        _, _, lean = legs_run(0)
        for fixture in ("planted", "proof1b"):
            shutil.copytree(REPO / "fixtures" / fixture, root / "fixtures-src" / fixture)
        shutil.copytree(REPO / "classifier", code_repo / "classifier")
        path = code_repo / "recipe/constants.toml"
        path.write_text(path.read_text().replace('legacy = "pending"', f'legacy = "{legacy}"').replace(
            "cut_n = 0", "cut_n = 2"))
        for name, value in (("headroom", lambda *_: 1), ("CHECKS", ()), ("lock", lambda *_: None)):
            monkeypatch.setattr(preflight, name, value)
        monkeypatch.setattr(confine, "apply_fs", lambda pol: None)
        monkeypatch.setattr(cli, "REPO", code_repo)
        return lambda *argv: cli.main([*argv, "--policy", str(make_policy())]), lean, policy.load(make_policy())
    return make


@pytest.fixture
def proof1b_cli(ledger, root):
    """`ledger fixtures --proof1b` with the D+14 timing `timing_s` recorded, every process answered as when proof 1b
    passes. Returns the call, giving its exit, and the policy."""
    invoke, lean, pol = ledger()
    (root / "measure/d14").mkdir(parents=True)

    def call(timing_s: float) -> int:
        (root / "measure/d14/proof1b.json").write_text(json.dumps({"timing_s": timing_s}))
        lean.answers = {key: list(value) if isinstance(value, list) else value for key, value in CAUGHT.items()}
        return invoke("fixtures", "--proof1b")
    return call, pol


def test_real_run_refuses_bypass_and_fixture_header(legs_run):
    """Outside the fixture-run root, legs.run_leg refuses the per-pair replay bypass, and a pair whose text does not
    begin with the recipe's header, whatever core-only header it has instead, before it counts an attempt or starts
    a process; pass 1 refuses that pair too."""
    run, pairs, lean = legs_run(2, ("pin",))
    for root in (run.pol.root, run.pol.root / "elsewhere/fixtures-run"):
        with pytest.raises(LedgerStop, match="a real run refuses"):
            legs.run_leg(dataclasses.replace(run, pol=dataclasses.replace(run.pol, root=root)), pairs[0], "pin",
                         bypass=True)
    for header in (fixtures.HEADER, "import Lean\n", "import Lean\n" + run.consts.published["assembly"]["header"]):
        (run.work / "pairs/p1__p0.lean").write_text(header + "theorem p1__p0 : True := by\n  trivial\n")
        for refused in (lambda: legs.run_leg(run, pairs[1], "pin"), lambda: legs.pass1(run, pairs[1:], ceiling_s=1e9)):
            with pytest.raises(LedgerStop, match="a real run refuses"):
                refused()
    assert run.progress.data["legs"] == {} and [step for step, _, _ in lean.calls] == ["git"]


@pytest.mark.parametrize("replays, passed", [
    ([{}, REJECTS, {}, REJECTS, {}, {}], True),
    ([{}, REJECTS, {}, {"exit": -9, "killed": "wall-clock"}, {}, {}], False),
    ([{}] * 5, False),
], ids=["caught", "killed-in-pass-1", "missed"])
def test_proof1b_replay_capped_1_5x_timing(legs_run, root, monkeypatch, replays, passed):
    """Each --fresh replay of proof 1b's aggregates runs under 1.5 times the D+14 timing, and each per-pair replay
    under the per-pair limit. The proof passes when the aggregate's replay rejects the plant in run 1, the walk
    attributes it to the victim, removed under the run's date, and the per-pair replay rejects it in run 2; it fails
    when either does not."""
    run, _, lean = legs_run(0, ("pin",))
    monkeypatch.setattr(preflight, "headroom", lambda *_: 1)  # pass 1's legs one at a time, the replays in turn
    shutil.copytree(REPO / "fixtures/proof1b", root / "fixtures-src/proof1b")
    # in turn, run 1: the companion, the aggregate, the rebuilt one; run 2: the victim, the companion, the aggregate
    lean.answers |= {"replay": replays, "walk": {"output": '{"member": "victim__p0"}\n'}}
    assert (report := fixtures.run_proof1b(run.pol, TIMING_S, TODAY)).passed is passed
    caps = {("--fresh" in cmd, kwargs["timeout_s"]) for (step, cmd, _), kwargs in zip(lean.calls, lean.kwargs)
            if step == "replay"}
    assert caps == {(True, 1.5 * TIMING_S), (False, run.consts.published["limits"]["per_pair_wall_clock_s"])}
    if passed:
        found = json.loads((root / "fixtures-run/proof1b/run-1/progress.json").read_text())["replay_overrides"]
        assert [(o["source"], o["constant"], o["date"]) for o in found.values()] == [
            ("d21-proof-1b", "planted_false", TODAY.isoformat())]
        assert report.classes == ("rejected-by-replay",) * 2


def test_proof1b_refused_fixture_pair_fails(legs_run, root):
    """A fixture pair the assembler refuses fails the proof, named in its evidence, before any leg runs."""
    run, _, lean = legs_run(0, ("pin",))
    src = shutil.copytree(REPO / "fixtures/proof1b", root / "fixtures-src/proof1b")
    entries = json.loads((src / "entries.json").read_text())
    entries[1]["proof"] = ["trivial\r"]
    (src / "entries.json").write_text(json.dumps(entries))
    assert fixtures.run_proof1b(run.pol, TIMING_S, TODAY) == fixtures.Proof1bReport(
        False, "the assembler refused companion__p0: carriage-return")
    assert [step for step, _, _ in lean.calls] == ["git"]


@pytest.mark.parametrize("builds, typed, shown, sources, verdict", [
    ([{}, {}, {}], "2", "disagreeing by the cross-pass rule", {"crosspass-d21"}, "pass"),
    ([{}, {}, {"exit": 1, "output": "error: Aggregate.lean:10:0: unsolved goals\n"}], "1",
     "not caught by the cross-pass rule", {"aggregate-elab"}, "fail"),
    ([{}, {}, {}], "1", "not caught by the cross-pass rule", set(), "fail"),
    ([{"exit": 1, "output": "error: Aggregate.lean:29:0: unsolved goals\n"}, {}, {}], "2",  # the planted victim's line
     "disagreeing by the cross-pass rule", {"crosspass-d21"}, "fail"),
], ids=["caught", "build-failed", "missed", "planted-build-failed"])
def test_assembler_scope_leak_fixture_fails_agreement(ledger, root, monkeypatch, builds, typed, shown, sources,
                                                      verdict):
    """`ledger fixtures`, refused until the freeze lines are recorded, writes each proof's verdict line, and the
    branch reduction where the legacy environment is unavailable, in a fixture run whose pairs are its own, no cut
    of the draw's applying, and whose trees are its own. Its assertion over the assembler fixture set builds one
    aggregate over the clean fixtures but the scope-leak fixture, then one with it first, so that its instance
    reaches every later member: a member whose type changes there is removed by the cross-pass rule as
    harness-error, and the leak is shown failing the agreement; a build that fails instead, or nothing changed,
    fails proof 3b, whose planted half holds here: the planted leak changes its victim's type in the aggregate, and
    a planted aggregate whose build fails on the victim's line instead fails proof 3b too."""
    invoke, lean, pol = ledger("environment-unavailable")
    assert invoke("fixtures") == 2 and gatefile.rows(pol) == []
    frozen(pol)

    def leaking(cmd, **kwargs):  # the aggregate audits: what types the planted victim, and with the scope-leak
        proc = lean(cmd, **kwargs)  # fixture first, the members after it, report there
        if "Aggregate" in cmd and "synthetic_scope_leak__p0" in cmd:
            return dataclasses.replace(proc, output=proc.output.replace('"type_hash": "1"', f'"type_hash": "{typed}"'))
        if "Aggregate" in cmd and "planted_victim__p0" in cmd:
            return dataclasses.replace(proc, output="".join(
                line.replace('"type_hash": "1"', '"type_hash": "2"') if "planted_victim" in line else line
                for line in proc.output.splitlines(True)))
        return proc
    monkeypatch.setattr(confine, "run", leaking)
    lean.answers["build"] = builds  # the planted batch's aggregate, then the assembler set's two
    assert invoke("fixtures") == 1  # every planted pair accepted here: proofs 1, 2 and 3 fail
    rows = gatefile.rows(pol)[2:]
    assert [row[1:3] for row in rows] == [("branch-reduction", "proofs 1, 2 and 3 reduced")] + [
        (f"d21-proof-{n}", "fail") for n in ("1", "2", "3")] + [("d21-proof-3b", verdict)]
    assert "absent" not in rows[-1][4]  # each planted pair recorded, past the draw's cut
    assert f"without the scope-leak fixture agreeing, with it first {shown}" in rows[-1][4]
    overrides = json.loads((root / "fixtures-run/assembler/results/progress.json").read_text()).get(
        "harness_overrides", {})
    assert {o["source"] for o in overrides.values()} == sources
    assert not (root / "env/pin/Pairs").exists() and not (root / "env/pin/Aggregate.lean").exists()


def test_fixture_aggregate_over_cap_is_kill_never_cut(ledger, root, code_repo):
    """A fixture-run aggregate over its cap is the kill in the fixture run's own gate file, with no per-member cost
    to cut by, and fails proof 3b; the repository's recipe/constants.toml is left byte-identical."""
    invoke, lean, pol = ledger()
    frozen(pol)
    before = (code_repo / "recipe/constants.toml").read_bytes()
    lean.answers["build"] = [{"exit": -9, "killed": "wall-clock"}, {}, {}]  # the planted batch's aggregate killed
    assert invoke("fixtures") == 1
    assert (code_repo / "recipe/constants.toml").read_bytes() == before
    own = gatefile.rows(dataclasses.replace(pol, root=root / "fixtures-run"))
    assert [row[1:3] for row in own] == [("kill", "over the cap, no cut fits")]
    assert gatefile.rows(pol)[-1][1:3] == ("d21-proof-3b", "fail")


def test_proof1b_flag_runs_project_alone(proof1b_cli, root):
    """`ledger fixtures --proof1b`, refused until the freeze lines are recorded, runs proof 1b's fixture project
    alone, none of the fixture run's planted entries, and writes its verdict line, d21-proof-1b, alone."""
    call, pol = proof1b_cli
    assert call(TIMING_S) == 2 and gatefile.rows(pol) == []
    frozen(pol)
    assert call(TIMING_S) == 0
    assert [row[1:3] for row in gatefile.rows(pol)][2:] == [("d21-proof-1b", "pass")]
    assert not (root / "fixtures-run/planted").exists() and (root / "fixtures-run/proof1b").is_dir()


def test_proof1b_first_when_timing_over_2h(proof1b_cli, monkeypatch):
    """With its D+14 timing over 2 hours, proof 1b runs first on D+21: refused until the classifier-freeze and
    limit-freeze lines exist, then run, and, on the freeze's day, refused once a proof or pilot line exists, where
    with a timing of 2 hours it is not; a repeat runs on a later night."""
    call, pol = proof1b_cli
    assert call(3 * 3600) == 2 and gatefile.rows(pol) == []
    frozen(pol)
    assert call(3 * 3600) == 0 and gatefile.rows(pol)[-1][1:3] == ("d21-proof-1b", "pass")
    gatefile.append(pol, "d21-pilot", "met", "pipeline", "test", date.today())
    assert call(3 * 3600) == 2 and [row[1] for row in gatefile.rows(pol)].count("d21-proof-1b") == 1
    assert call(2 * 3600) == 0

    class Tomorrow(date):
        @classmethod
        def today(cls):
            return date.fromordinal(date.today().toordinal() + 1)
    monkeypatch.setattr(cli, "date", Tomorrow)
    assert call(3 * 3600) == 0 and [row[1] for row in gatefile.rows(pol)].count("d21-proof-1b") == 3
