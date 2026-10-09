import hashlib

import pytest
from helpers import record

from ledger import frame, sample
from ledger.types import LedgerStop

pytestmark = pytest.mark.assembler


def test_proofless_excluded_and_counted(build_frame):
    """An entry with no proof is excluded and counted, in no eligible entry and no pair count."""
    built = build_frame(record("a", 0), record("b", 3, "P", "lean_workbook_plus"), record("c", 1, "Q"))
    assert built.summary == {
        "schema": "frame/1", "entries_sha256": built.summary["entries_sha256"], "records_total": 3,
        "split_counts": {"lean_workbook": 2, "lean_workbook_plus": 1}, "card_count_lean_workbook": 57231,
        "reconciliation": "counted split values sum to records_total: true", "proofless_excluded": 1,
        "proof_bearing": 2, "proof_elements_raw": 4, "within_entry_exact_duplicates_removed": 0,
        "cross_entry_duplicates_removed": 0, "refused": {"no-decl": 0, "double-underscore": 0,
        "unsafe-name": 0, "comment-before-suffix": 0, "suffix-mismatch": 0, "name-collision": 0}, "eligible_entries": 2, "drawable_pairs_before_cross_dedupe": 3,
        "drawable_pairs": 3, "multiplier": {"mean": 2.0, "median": 2.0, "max": 3, "max_entry": "b"}}
    assert [(e.decl, len(e.proofs)) for e in built.eligible] == [("b", 3), ("c", 1)]


def test_cross_entry_dedupe_name_masked_first_wins(build_frame):
    """# covers: test_proofless_never_evicts_proof_bearing
    Statements equal once whitespace is collapsed and the name masked collapse to the first proof-bearing one in
    file order, even when a proof-less entry with the same statement came earlier; a different statement
    survives, and the removed entries leave the drawable counts."""
    built = build_frame(record("first", 0, "P"), record("second", 2, "P"), record("third", 5, "P"),
                        record("spaced", 4, "P  \n"), record("other", 1, "Q"))
    assert [e.decl for e in built.eligible] == ["second", "other"]
    assert (built.summary["cross_entry_duplicates_removed"], built.summary["proof_bearing"]) == (2, 4)
    assert (built.summary["drawable_pairs_before_cross_dedupe"], built.summary["drawable_pairs"]) == (7, 3)


def test_refused_entries_stay_eligible(build_frame, published):
    """# covers: test_refused_pair_has_refusal_key
    Refused proof-bearing entries stay in the frame and are counted by kind; entries with no declaration
    name are never deduplicated; a drawn refused pair has a pair_id of its
    position, so every pair_id in a draw is unique."""
    bad = record("bad", 1) | {"formal_statement": "theorem bad : True := by simp"}
    nameless = {"formal_statement": "example : True :=  by sorry", "split": "lean_workbook", "proof": ["x"]}
    built = build_frame(bad, nameless, nameless, record("a", 1), record("a", 1, "Q"))
    assert [e.refusal for e in built.eligible] == ["suffix-mismatch", "no-decl", "no-decl", None, "name-collision"]
    assert built.summary["refused"] == {"no-decl": 2, "double-underscore": 0, "unsafe-name": 0,
                                        "comment-before-suffix": 0, "suffix-mismatch": 1, "name-collision": 1}
    drawn = sample.draw(built, published)["draw"]
    assert sorted(p["pair_id"] for p in drawn) == ["#0__p0", "#1__p0", "#2__p0", "#4__p0", "a__p0"]


def test_line_separator_in_a_proof_survives(build_frame):
    """A U+2028 inside a proof element does not split an entries.jsonl line."""
    built = build_frame(record("a") | {"proof": ["nlinarith\u2028[sq_nonneg x]"]})
    assert [e.proofs for e in built.eligible] == [["nlinarith\u2028[sq_nonneg x]"]]


def test_no_proof_bearing_entry_stops(build_frame):
    with pytest.raises(LedgerStop, match="no entry with a proof"):
        build_frame(record("a", 0))


def test_frame_sizes_published_before_draw(build_frame, published, tmp_path):
    """A draw is refused until frame.json is written and matches the entries; its digest then goes into
    sample.json."""
    built = build_frame(record("a", 2))
    with pytest.raises(LedgerStop, match="frame.json"):
        frame.published(built, tmp_path / "work")
    digest = frame.write(built, tmp_path / "work")
    assert digest == "sha256:" + hashlib.sha256((tmp_path / "work" / "frame.json").read_bytes()).hexdigest()
    frame.published(built, tmp_path / "work")
    with pytest.raises(LedgerStop, match="frame.json"):
        frame.published(build_frame(record("b", 2)), tmp_path / "work")
    assert sample.draw(built, published)["frame_sha256"] == digest
