import pytest

from ledger import crosspass

PROPEXT = {"name": "propext", "module": "Init.Core", "via_own": False}
DECL = {"name": "a__p0", "axioms_collector": [PROPEXT], "axioms_walk": [PROPEXT], "type_hash": "7", "type_pp": "True"}


@pytest.mark.parametrize("aggregate, differs", [
    ([DECL | {"axioms_walk": [PROPEXT | {"via_own": True}]}], []),
    ([], ["elaboration"]),
    ([DECL | {"axioms_walk": [PROPEXT, {"name": "sorryAx", "module": None, "via_own": True}]}], ["axioms"]),
    ([DECL | {"type_hash": "8"}], ["type"]),
], ids=["agree", "elaboration", "axioms", "type"])
def test_outcome_axioms_type_compared(aggregate, differs):
    """A member's per-pair module and the aggregate are compared on three observables: whether the aggregate
    elaborated its declaration, its axiom set (union of both lists, by name and declaring module) and its type's
    hash."""
    assert crosspass.compare("a__p0", [DECL], aggregate) == differs
