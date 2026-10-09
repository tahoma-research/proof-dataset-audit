import json
from datetime import date

import pytest
from helpers import git

from ledger import aggregate, cli, confine, constants, gatefile, publish, stage
from ledger.types import LedgerStop

TODAY = date(2026, 12, 21)


def published(public, ref: str = "") -> list[dict]:
    """The records of the public tree, or of `ref` in it."""
    text = git("-C", public, "show", f"{ref}:results/records.jsonl") if ref else (
        public / "results/records.jsonl").read_text()
    return [json.loads(line) for line in text.splitlines()]


def test_forward_commit_excluded_from_rates_old_tag_resolves(snapshot, dev_repo, stage_policy, root, monkeypatch,
                                                            capsys):
    """withdraw marks a pair's published record withdrawn, with the date, the demanding party's class and the stated
    ground, in one commit on HEAD holding the withdrawal line, a withdrawal gate line and the report made again: the
    pair leaves both rates, numerator and denominator, and every listed set, while the tag that published it still
    resolves to its record unmarked. It is staged by stage itself, so a check of stage's that fails, or a drawn pair
    with no record yet, leaves nothing recorded. Staging again keeps the mark. A second withdrawal of the pair, by its
    digest or, at the command line, its pair_id, and one of a pair with no published record, are refused."""
    # covers: test_report_after_withdraw_keeps_mark
    public, found = snapshot
    git("-C", public, "update-ref", publish.PUSHED + "v0-pin", "HEAD")
    head, pair, consts = git("-C", public, "rev-parse", "HEAD"), found[5], constants.load(dev_repo)
    before = json.loads((public / "results/summary.json").read_text())
    kept = {path: path.read_bytes() for path in (root / "results/membership.txt", root / "results/withdrawals.jsonl",
                                                 public / "gates/GATES.md")}
    aggregate.write_membership(root / "results", [r["pair_id"] for r in found if r["aggregate"]["member"] or r == pair])
    with pytest.raises(LedgerStop, match="membership.txt is not the records' aggregate members"):
        publish.withdraw(stage_policy, consts, pair["pair_sha256"], TODAY, "dataset publisher", "a takedown notice")
    (root / "results/membership.txt").write_bytes(kept.pop(root / "results/membership.txt"))
    progress = json.loads(text := (root / "results/progress.json").read_text())
    progress["legs"][found[1]["pair_sha256"]]["pin"]["terminal"] = False
    (root / "results/progress.json").write_text(json.dumps(progress))
    with pytest.raises(LedgerStop, match="its pin leg is not terminal"):
        publish.withdraw(stage_policy, consts, pair["pair_sha256"], TODAY, "dataset publisher", "a takedown notice")
    (root / "results/progress.json").write_text(text)
    assert {path: path.read_bytes() for path in kept} == kept and git("-C", public, "rev-parse", "HEAD") == head
    publish.withdraw(stage_policy, consts, pair["pair_sha256"], TODAY, "dataset publisher", "a takedown notice")
    mark = {"date": TODAY.isoformat(), "party_class": "dataset publisher", "ground": "a takedown notice"}
    assert git("-C", public, "rev-parse", "HEAD~") == head and git("-C", public, "status", "--porcelain") == ""
    assert gatefile.rows(stage_policy)[-1] == (TODAY.isoformat(), "withdrawal", "withdrawn", "operator",
                                               f"pair={pair['pair_id']}; party_class=dataset publisher; "
                                               "ground=a takedown notice")
    assert (public / "results/withdrawals.jsonl").read_text().splitlines()[-1] == json.dumps(
        {"pair_sha256": pair["pair_sha256"]} | mark, sort_keys=True, separators=(",", ":"))
    after = json.loads((public / "results/summary.json").read_text())
    for level in ("pair", "entry"):
        assert [after["rates"][level][key] for key in ("numerator", "denominator")] == [
            before["rates"][level][key] - 1 for key in ("numerator", "denominator")]
    assert (after["withdrawn"], pair["pair_id"] in before["listed"][pair["class"]]) == (2, True)
    assert pair["pair_id"] not in after["listed"][pair["class"]]
    assert published(public)[5]["withdrawn"] == mark
    assert published(public, publish.PUSHED + "v0-pin")[5]["withdrawn"] is None
    stage.stage(stage_policy, constants.load(dev_repo), dry_run=False)
    assert published(public)[5]["withdrawn"] == mark
    with pytest.raises(LedgerStop, match=f"{pair['pair_id']} was withdrawn on {TODAY}"):
        publish.withdraw(stage_policy, consts, pair["pair_sha256"], TODAY, "dataset publisher", "a takedown notice")
    monkeypatch.setattr(confine, "apply_fs", lambda pol: None)  # the real one would also confine this process
    assert cli.main(["withdraw", "--pair", pair["pair_id"], "--party-class", "author", "--ground", "a request",
                     "--policy", str(stage_policy.path)]) == 2
    assert f"{pair['pair_id']} was withdrawn on {TODAY}" in capsys.readouterr().err
    with pytest.raises(LedgerStop, match="p9__p0: no published record"):
        publish.withdraw(stage_policy, consts, "p9__p0", TODAY, "dataset publisher", "a takedown notice")


def test_deletion_or_rewrite_fails(snapshot, dev_repo, stage_policy, root, monkeypatch):
    """A withdrawal made by deleting a published record or withdrawal line, or by rewriting a published commit, is
    refused by publish, its dry run too, and by withdraw; a published tag is never moved. A withdrawal line lost from
    the root's file stops staging, and withdraw still refuses the pair the published file names."""
    public, found = snapshot
    consts = constants.load(dev_repo)
    (root / "results/withdrawals.jsonl").write_bytes(b"")
    with pytest.raises(LedgerStop, match="results/withdrawals.jsonl: the root's is not the published one with lines "
                                         "appended"):
        stage.stage(stage_policy, consts, dry_run=True)
    with pytest.raises(LedgerStop, match=f"{found[0]['pair_id']} was withdrawn on 2026-12-20"):
        publish.withdraw(stage_policy, consts, found[0]["pair_id"], TODAY, "author", "a request")
    git("-C", public, "update-ref", publish.PUSHED + "v0-pin", "HEAD")
    runs = (lambda: publish.publish(stage_policy, tag=None, dry_run=True),
            lambda: publish.withdraw(stage_policy, consts, found[1]["pair_id"], TODAY, "author", "a request"))
    for rel, keep, reason in (("results/records.jsonl", lambda lines: lines[:5] + lines[6:], "p5__p0"),
                              ("results/withdrawals.jsonl", lambda lines: [], "withdrawals.jsonl")):
        data = (public / rel).read_text()
        (public / rel).write_text("".join(keep(data.splitlines(keepends=True))))
        for run in runs:
            with pytest.raises(LedgerStop, match=f"v0-pin.*{reason}"):
                run()
        (public / rel).write_text(data)
    monkeypatch.setenv("TZ", "UTC")
    identity = stage_policy.values["identity"]
    git("-C", public, "-c", f"user.name={identity['name']}", "-c", f"user.email={identity['email']}", "commit", "-q",
        "--amend", "-m", "Stage the published code, recipe and templates again")
    for run in runs:
        with pytest.raises(LedgerStop, match="v0-pin is not in HEAD's history"):
            run()
    with pytest.raises(LedgerStop, match="v0-pin exists"):
        publish.publish(stage_policy, tag="v0-pin", dry_run=True)
