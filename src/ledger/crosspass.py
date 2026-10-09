"""The cross-pass agreement rule: a member's per-pair module and the aggregate must agree on its elaboration, its
axiom set and its elaborated type."""


def compare(member: str, pair_audit: list[dict], aggregate_audit: list[dict]) -> list[str]:
    """The observables on which the member's pass-1 audit and the aggregate's disagree: "elaboration" when the
    aggregate's has no line for it; "axioms" when the union of the collector's and the walk's axioms differ by name
    or declaring module (each audit reports its own module's as null, so Pairs.X and Aggregate compare equal);
    "type" when the types' hashes differ."""
    ours = next(decl for decl in pair_audit if decl["name"] == member)
    theirs = next((decl for decl in aggregate_audit if decl["name"] == member), None)
    if theirs is None:
        return ["elaboration"]

    def axioms(decl: dict) -> set:
        return {(axiom["name"], axiom["module"]) for axiom in decl["axioms_collector"] + decl["axioms_walk"]}
    return [name for name, differs in (("axioms", axioms(ours) != axioms(theirs)),
                                       ("type", ours["type_hash"] != theirs["type_hash"])) if differs]
