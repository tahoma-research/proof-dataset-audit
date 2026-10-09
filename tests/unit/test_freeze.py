"""The D+21 freeze: the classifier table and the per-pair limit frozen in the published constants with their gate
lines, committed in the public tree; the D+14 pilot legs the frozen limit reopens; and the one re-freeze."""

import dataclasses
import hashlib
import json
import shutil
from datetime import date

import pytest
from helpers import REPO, git

from ledger import classify, confine, constants, freeze, gatefile, legs, policy
from ledger.types import LedgerStop

TODAY = date(2026, 11, 23)
WALL = {"exit": -9, "killed": "wall-clock", "wall_s": 1800.0}
RUN = confine.run  # the real one, which the public tree's commits go through
ERROR = {"exit": 1, "output": "Pairs/p.lean:2:2: error: unknown identifier\n"}


def dies_once(monkeypatch, module, name: str) -> None:
    """`module.name` raises the first time it is called, as a run that died there, and is itself again after."""
    real = getattr(module, name)

    def died(*args):
        monkeypatch.setattr(module, name, real)
        raise LedgerStop("the run died")
    monkeypatch.setattr(module, name, died)


@pytest.fixture
def pilot(legs_run, root, make_policy, code_repo, monkeypatch):
    """D+14 pilot pin legs of pairs answered as `cases` gives (FakeLean compile answers, the replay's wall-clock, and
    any audit answers),
    their figures in measure/d14/pairs.json, under a policy whose public tree is the committed code repository, as in
    production, which git then commits in. Returns the policy, the code's constants, the progress and the pairs."""
    def make(*cases):
        run, pairs, lean = legs_run(len(cases), ("pin",))
        figures = []
        for pair, (compiled, replay_s, *audit) in zip(pairs, cases):
            lean.answers = {"compile": compiled, "replay": {"wall_s": replay_s}, "audit": audit[0] if audit else {}}
            leg = legs.run_leg(run, pair, "pin")
            figures.append({"pair_id": pair["pair_id"], "outcome": leg["outcome"], "compile_s": compiled["wall_s"],
                            "replay_s": leg["replay"] and replay_s, "peak_mem_kb": 1000})
        run.progress.pilot([pair["pair_sha256"] for pair in pairs], 0.0, False)
        (root / "measure/d14").mkdir(parents=True)
        (root / "measure/d14/pairs.json").write_text(json.dumps(figures))
        shutil.copytree(REPO / "classifier", code_repo / "classifier")
        (code_repo / "gates").mkdir()
        (code_repo / "gates/GATES.md").touch()
        git("-C", code_repo, "add", ".")
        git("-C", code_repo, "-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-qm", "public")
        monkeypatch.setattr(confine, "run", RUN)
        return policy.load(make_policy(public_tree=str(code_repo))), constants.load(code_repo), run.progress, pairs
    return make


def test_sets_table_and_limit_writes_lines(pilot, root, code_repo, monkeypatch):
    """The freeze records the table's sha256 and sets it frozen, sets the per-pair limit to 5 times the slowest
    clean pilot pair with its rule, writes classifier-freeze then limit-freeze, derives every earlier leg outcome
    again from the frozen table, and commits the constants and the gate file in the public tree. With no D+14
    figure to set the limit from, nothing is frozen. A freeze that died before its lines is run again whole by its
    retry; a freeze after them is refused."""
    pol, consts, prog, pairs = pilot(({"wall_s": 10.0}, 2.0), (ERROR | {"wall_s": 30.0}, None))
    first = root / "results" / prog.data["legs"][pairs[0]["pair_sha256"]]["pin"]["leg"]
    first.write_text(json.dumps(json.loads(first.read_text()) | {"outcome": "elab-error"}))  # an earlier outcome
    (figures := root / "measure/d14/pairs.json").rename(away := figures.with_suffix(".away"))
    with pytest.raises(FileNotFoundError):  # no limit to freeze: nothing is frozen
        freeze.freeze(pol, consts, prog, root / "results", TODAY)
    assert constants.load(code_repo).published["classifier"]["status"] == "draft" and gatefile.rows(pol) == []
    away.rename(figures)
    dies_once(monkeypatch, legs, "reclassify")
    with pytest.raises(LedgerStop, match="died"):
        freeze.freeze(pol, consts, prog, root / "results", TODAY)
    report = freeze.freeze(pol, constants.load(code_repo), prog, root / "results", TODAY)
    frozen = constants.load(code_repo).published
    table = (code_repo / "classifier/table-v1.toml").read_bytes()
    assert (frozen["classifier"]["status"], frozen["classifier"]["table_sha256"]) == ("frozen", report.table_sha256)
    assert report.table_sha256 == "sha256:" + hashlib.sha256(table).hexdigest()
    assert classify.load(code_repo, constants.load(code_repo)) == classify.load(REPO, constants.load(REPO))
    assert {key: frozen["limits"][key] for key in ("per_pair_wall_clock_s", "per_pair_limit_status",
                                                   "per_pair_limit_rule")} == {
        "per_pair_wall_clock_s": 50, "per_pair_limit_status": "frozen", "per_pair_limit_rule": "5x-slowest-clean"}
    assert [(row[1], row[2]) for row in gatefile.rows(pol)] == [("classifier-freeze", "v1 frozen"),
                                                               ("limit-freeze", "per_pair_wall_clock_s=50")]
    assert json.loads(first.read_text())["outcome"] == "accepted" and report.reclassified
    assert git("-C", code_repo, "status", "--porcelain") == "" and "Freeze" in git("-C", code_repo, "log", "-1")
    with pytest.raises(LedgerStop, match="recorded"):
        freeze.freeze(pol, constants.load(code_repo), prog, root / "results", TODAY)


@pytest.mark.parametrize("clean_s, reopened", [
    (300.0, {"p1__p0": "over-frozen-limit", "p2__p0": "over-frozen-limit"}),
    (400.0, {"p2__p0": "killed-at-provisional", "p3__p0": "killed-at-provisional"}),
], ids=["limit-1500", "limit-2000"])
def test_reopen_legs_over_frozen_limit(pilot, root, clean_s, reopened):
    """Every D+14 pilot pin leg whose compile or replay wall-clock exceeds the frozen limit is reopened, and one
    killed at the provisional 30 minutes in any step, its audit included, is reopened when the frozen limit is
    longer: each made not terminal, so that the next run takes it again, which the outcomes derived again from the
    frozen table leave so, and recorded with its reason and date."""
    pol, consts, prog, pairs = pilot(({"wall_s": clean_s}, 1.0), (ERROR | {"wall_s": 1700.0}, None), (WALL, None),
                                     ({"wall_s": 10.0}, 1.0, WALL))
    killed = root / "results" / prog.data["legs"][pairs[2]["pair_sha256"]]["pin"]["leg"]
    killed.write_text(json.dumps(json.loads(killed.read_text()) | {"outcome": "accepted"}))  # one the table changes
    freeze.freeze(pol, consts, prog, root / "results", TODAY)
    ids = {pair["pair_sha256"]: pair["pair_id"] for pair in pairs}
    assert {ids[sha]: why for sha, why in prog.data["reopened"].items()} == {
        pair_id: {"reason": reason, "date": TODAY.isoformat()} for pair_id, reason in reopened.items()}
    assert {ids[sha] for sha, envs in prog.data["legs"].items() if not envs["pin"]["terminal"]} == set(reopened)


def test_refreeze_once_only_named_rows(pilot, root, code_repo, tmp_path, monkeypatch):
    """A failed proof's re-freeze puts table-v2.toml in force under version v2, only after a failed proof, only where
    it changes the rows the proof names and none other, only before the first pass-1 run, and only once; one that
    died is completed by its retry."""
    pol, consts, prog, _ = pilot(({"wall_s": 10.0}, 2.0))
    freeze.freeze(pol, consts, prog, root / "results", TODAY)
    v2 = (code_repo / "classifier/table-v1.toml").read_text().replace('version = "v1"', 'version = "v2"')
    kernel = "pattern = '^[^\\n]*error[^\\n]*\\(kernel\\)'"
    assert v2.count(kernel) == 1
    (enabled := tmp_path / "enabled/gates").mkdir(parents=True)
    (enabled / "GATES.md").write_text(f"| {TODAY} | d21-proof-1 | fail | pipeline | planted_kernel__p0: accepted |\n"
                                      f"| {TODAY} | timer-enabled | enabled | assistant | proofs passed |\n")

    def refreeze(table: str, rows: list[str], public=code_repo):
        (code_repo / "classifier/table-v2.toml").write_text(table)
        return freeze.refreeze(dataclasses.replace(pol, values=pol.values | {"public_tree": str(public)}),
                               constants.load(code_repo), prog, root / "results", rows, TODAY)
    gatefile.append(pol, "d21-proof-2", "pass", "pipeline", "planted_sorry__p0: axiom-audit-failure", TODAY)
    with pytest.raises(LedgerStop, match="follows a failed proof"):
        refreeze(v2.replace(kernel, "pattern = '\\(kernel\\)'"), ["any.kernel"])
    gatefile.append(pol, "d21-proof-1", "fail", "pipeline", "planted_kernel__p0: accepted", TODAY)
    with pytest.raises(LedgerStop, match="rows other than any.kernel"):
        refreeze(v2.replace('outcome = "oom" }', 'outcome = "stack" }', 1), ["any.kernel"])
    with pytest.raises(LedgerStop, match="before the first pass-1 run"):
        refreeze(v2.replace(kernel, "pattern = '\\(kernel\\)'"), ["any.kernel"], enabled.parent)
    dies_once(monkeypatch, legs, "reclassify")
    with pytest.raises(LedgerStop, match="died"):
        refreeze(v2.replace(kernel, "pattern = '\\(kernel\\)'"), ["any.kernel"])
    refreeze(v2.replace(kernel, "pattern = '\\(kernel\\)'"), ["any.kernel"])
    named = constants.load(code_repo).published["classifier"]
    assert (named["version"], named["table"], named["status"]) == ("v2", "classifier/table-v2.toml", "frozen")
    rows = classify.load(code_repo, constants.load(code_repo))
    assert next(row for row in rows if row["id"] == "any.kernel")["pattern"] == "\\(kernel\\)"
    assert gatefile.rows(pol)[-1][1:3] == ("classifier-freeze", "v2 re-frozen: any.kernel")
    with pytest.raises(LedgerStop, match="once"):
        refreeze(v2.replace('version = "v2"', 'version = "v3"'), ["any.kernel"])
