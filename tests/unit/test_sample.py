import json
import random

import pytest
from helpers import REPO, record

from ledger import frame, sample
from ledger.types import LedgerStop

pytestmark = pytest.mark.assembler


def real(name):
    """The release record a fixture was cut from (its header line skipped)."""
    return json.loads((REPO / f"fixtures/assembler/{name}.jsonl").read_text(encoding="utf-8").splitlines()[1])


@pytest.fixture
def draw(published):
    def draw(built, **override):
        return sample.draw(built, published | {"sampling": published["sampling"] | override})
    return draw


@pytest.fixture
def big(build_frame):
    """A frame of 200 entries of 3 proofs each: 400 drawable pairs, so a draw of 50 is a real selection."""
    return build_frame(*(record(f"t{i}", 3, f"P{i}") for i in range(200)))


def test_same_seed_same_draw_other_seed_differs(big, draw):
    """# covers: test_same_seed_same_draw, test_different_seed_different_draw"""
    assert draw(big, sample_size=50) == draw(big, sample_size=50)
    assert draw(big, sample_size=50)["draw"] != draw(big, sample_size=50, seed=1)["draw"]


def test_reordered_frame_same_draw(big, draw):
    shuffled = frame.Frame(big.summary, random.Random(7).sample(big.eligible, len(big.eligible)))
    assert draw(shuffled, sample_size=50)["draw"] == draw(big, sample_size=50)["draw"]


def test_counts_match_records(big, draw):
    """The sample's pair and distinct-entry counts are those of its draw, at most two pairs per entry."""
    out = draw(big, sample_size=50)
    assert out["drawable_frame_size"] == big.summary["drawable_pairs"] == 400
    assert [p["i"] for p in out["draw"]] == list(range(50))
    assert out["distinct_entries"] == len({p["decl"] for p in out["draw"]})


def test_small_frame_takes_every_pair_in_draw_order(build_frame, draw):
    """# covers: test_max_two_per_entry, test_single_pair_entry_contributes_one, test_small_frame_takes_all_in_rng_order
    A frame smaller than the sample is drawn whole: the 64-proof entry (lean_workbook_698) gives two pairs, the
    one-proof entry gives one, and the order is that of rng.sample(pairs, len(pairs)). Expected order hand-run
    at seed 0: Random(0) draws sample(range(64), 2) -> 49, 53, sample(range(1), 1) -> 0, sample(range(2), 2)
    -> 0, 1; sample of those five pairs then returns the order below."""
    built = build_frame(real("max_multiplicity"), real("proof_bearing"), record("two", 2, "R"))
    assert [(p["decl"], p["k"]) for p in draw(built)["draw"]] == [
        ("two", 0), ("lean_workbook_146", 0), ("lean_workbook_698", 53), ("two", 1), ("lean_workbook_698", 49)]


def test_cut_keeps_first_n(big, draw):
    assert draw(big, sample_size=50, cut_n=7)["draw"] == draw(big, sample_size=50)["draw"][:7]


def test_python_version_asserted(big, draw):
    with pytest.raises(LedgerStop, match="Python"):
        draw(big, python="0.0.0")

