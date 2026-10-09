import math

import pytest
from helpers import HARNESS, REPLAYED, summary_of

from ledger import classify

UNAVAILABLE = {"status": {"legacy": "environment-unavailable"}}


def test_rates_recompute_from_class_counts():
    """Both rates, recomputed from the published class counts by the published formula, equal the published figures,
    each with its denominator, rejected-by-replay in the numerator; the class counts, pairs, distinct entries and
    audit disagreements are the records'."""
    # covers: test_counts_by_class, test_pair_level_rate_formula_and_denominator, test_run_metadata_is_carried_through
    pairs = [(0, "reproduced"), (0, "rejected-by-checker"), (1, "axiom-audit-failure"), (2, "rejected-by-replay"),
             (3, "environment-mismatch"), (4, "environment-undeclared"), (4, "timed-out"), (5, "resource-exhausted"),
             (6, "harness-error"), (7, "unclassified"), (8, "reproduced"), (8, "reproduced")]
    s = summary_of(pairs, disagree=(1,))
    classes = s["classes"]
    assert classes == {cls: sum(c == cls for _, c in pairs) for cls in sorted(classify.CLASSES)}
    assert (s["pairs"], s["distinct_entries"], s["audit_disagreements"]) == (12, 9, 1)
    numerator = sum(classes[cls] for cls in ("rejected-by-checker", "axiom-audit-failure", "rejected-by-replay"))
    denominator = s["pairs"] - sum(classes[cls] for cls in ("timed-out", "resource-exhausted", "harness-error",
                                                            "unclassified", "environment-undeclared",
                                                            "environment-mismatch"))
    assert {k: s["rates"]["pair"][k] for k in ("numerator", "denominator", "percent")} == {
        "numerator": numerator, "denominator": denominator, "percent": round(100 * numerator / denominator, 2)}
    assert s["rates"]["entry"] == {"numerator": 2, "denominator": 4, "percent": 50.0}  # entries 1 and 2 of 0, 1, 2, 8


def test_inverted_numerator_mutation_caught():
    """An entry reproduces if at least one of its sampled pairs does: the entry-level numerator counts the countable
    entries with no reproduced pair, here 3 of 4, where its inversion gives 1 and an any-pair-fails reading 4."""
    s = summary_of([(0, "rejected-by-checker"), (1, "rejected-by-replay"), (2, "axiom-audit-failure"),
                    (2, "harness-error"), (3, "reproduced"), (3, "rejected-by-checker"), (4, "timed-out")])
    assert s["rates"]["entry"] == {"numerator": 3, "denominator": 4, "percent": 75.0}


def test_zero_numerator_wilson_nondegenerate():
    """A zero numerator publishes a Wilson interval from zero to above zero, widened by the square root of the design
    effect measured from the countable cluster sizes; at 1,000 pairs the interval is within 0.05 points of the
    normal-approximation figures given for scale, about ±1.35 points near 5 percent and ±1.86 near 10."""
    # covers: test_deff_from_cluster_sizes_defined_at_zero, test_ci_widened_by_sqrt_design_effect
    pair = summary_of([(e, "reproduced") for e in range(9)] + [(0, "reproduced")])["rates"]["pair"]
    assert (pair["numerator"], pair["denominator"], pair["percent"]) == (0, 10, 0.0)
    assert (pair["deff"], pair["cluster_sizes"]) == (1.2, {"1": 8, "2": 1})
    (lo, hi), (wlo, whi) = pair["interval_percent"]["nominal"], pair["interval_percent"]["widened"]
    assert lo == wlo == 0.0 < hi
    assert math.isclose(whi, hi / 2 * (1 + math.sqrt(1.2)), abs_tol=0.01)  # at zero the centre is the half-width
    for failures, half in ((50, 1.35), (100, 1.86)):
        pair = summary_of([(e, "rejected-by-checker" if e < failures else "reproduced")
                           for e in range(1000)])["rates"]["pair"]
        lo, hi = pair["interval_percent"]["nominal"]
        assert abs((hi - lo) / 2 - half) < 0.05 and pair["interval_percent"]["widened"] == [lo, hi]


def test_deff_over_countable_pairs():
    """The design effect counts only the countable pairs of each countable entry, never an excluded pair."""
    pair = summary_of([(0, "reproduced"), (0, "harness-error"), (1, "rejected-by-checker"),
                       (1, "reproduced")])["rates"]["pair"]
    assert (pair["denominator"], pair["cluster_sizes"], pair["deff"]) == (3, {"1": 1, "2": 1}, round(5 / 3, 4))


def test_skew_unverifiable_bucket():
    """A pair with no declared-side result counts as undecided at the declared revision, never as a declared
    failure, whether it reproduces at the pin or fails there; a pair with no result at the pin is left out of the
    table and counted beside it."""
    s = summary_of([(0, "reproduced", "accepted", "timeout-wall-clock"),
                    (1, "environment-undeclared", "kernel-reject", "oom"),
                    (2, "reproduced", "accepted", "elab-error"), (3, "rejected-by-checker"), (4, "timed-out")])
    assert s["skew"] == {"both": 0, "pin-only": 1, "declared-only": 0, "fails-both": 1, "unverifiable-declared": 2}
    assert s["skew_left_out"] == 1


def test_abandoned_branch_publishes_no_class_rate():
    """With the legacy environment unavailable the summary carries no class-based rate and no skew table, only the
    pin's rates from the pin leg outcomes: a pair counts unless its pin leg has no result or a harness override
    stands, and fails on an elaboration, kernel, audit or replay rejection, or a replay override. The rates
    recompute from the pin outcomes; the shortlist reads not-computable; the bound is every pin-failing pair."""
    # covers: test_pin_only_numerator_from_pin_outcomes, test_pin_only_entry_rate, test_pin_only_rates_recompute
    # covers: test_shortlist_not_computable_on_abandoned_branch, test_bound_formula
    undeclared = "environment-undeclared"
    pairs = [(0, "reproduced", "accepted", None), (0, undeclared, "audit-failure", None),
             (1, undeclared, "kernel-reject", None), (2, "rejected-by-replay", "replay-reject", None),
             (3, "harness-error", "harness", None), (4, undeclared, "elab-error", None),
             (5, "rejected-by-replay", "accepted", None, REPLAYED), (6, "harness-error", "accepted", None, HARNESS)]
    s = summary_of(pairs, **UNAVAILABLE)
    assert "rates" not in s and s["skew"] is None and s["mismatch_kernel_subcount"] == "not-computable"
    countable = [p for p in pairs if p[2] not in classify.NO_RESULT and p[4:] != (HARNESS,)]
    failing = [p for p in countable if p[2] in classify.FAILS | {"replay-reject"} or p[4:] == (REPLAYED,)]
    assert (len(countable), len(failing)) == (6, 5)
    assert {k: s["pin_only_rates"]["pair"][k] for k in ("numerator", "denominator")} == {"numerator": 5,
                                                                                        "denominator": 6}
    assert s["pin_only_rates"]["entry"] == {"numerator": 4, "denominator": 5, "percent": 80.0}  # all but entry 0
    assert s["bound"] == 5


def test_mismatch_kernel_subcount_and_bound():
    """The shortlist counts the environment-mismatch pairs the kernel row decided at the pin; the bound adds every
    environment-mismatch pair, the environment-undeclared pairs that fail at the pin, and the rejected-by-replay
    pairs whose declared leg is accepted."""
    s = summary_of([(0, "environment-mismatch", "kernel-reject", "accepted"),
                    (1, "environment-mismatch", "elab-error", "accepted"),
                    (2, "environment-undeclared", "kernel-reject", "timeout-wall-clock"),
                    (3, "rejected-by-replay", "replay-reject", "accepted"),
                    (4, "rejected-by-replay", "replay-reject", "kernel-reject"), (5, "reproduced")])
    assert (s["mismatch_kernel_subcount"], s["bound"]) == (1, 4)


@pytest.mark.parametrize("status, rows, framing", [
    pytest.param({}, [], "standard", id="test_route_two_not_decided_by_code"),
    pytest.param({}, [("2026-11-01", "route-one", "skew framing invoked", "pipeline", "r")], "skew", id="route_one"),
    pytest.param({}, [("2026-12-01", "route-two", "skew", "operator", "r")], "skew", id="route_two_skew"),
    pytest.param({}, [("2026-12-01", "route-two", "standard", "operator", "r")], "standard", id="route_two_other"),
    pytest.param(UNAVAILABLE["status"], [("2026-11-01", "route-one", "skew framing invoked", "pipeline", "r")],
                 "pin-only", id="pin_only_first"),
])
def test_framing_order_route_one_route_two_pin_only(status, rows, framing):
    """The framing is pin-only where the legacy environment is unavailable, else skew on a route-one line or a
    route-two line judged skew, else standard: never decided from the rates, so a zero numerator alone is
    standard."""
    s = summary_of([(e, "reproduced", "accepted", None if status else "accepted") for e in range(3)], rows,
                   status=status)
    assert s["framing"] == framing
