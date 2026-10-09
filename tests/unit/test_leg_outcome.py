import pytest
from conftest import CONSTS
from helpers import REPO

from ledger import classify
from ledger.types import LedgerStop

TABLE = classify.load(REPO, CONSTS)
ALLOWLIST = CONSTS.published["audit"]["allowlist"]
CLEAN = {"exit": 0, "killed": None, "oom_kill": 0, "output_missing": False, "text": ""}
WALL, OOM = CLEAN | {"exit": -9, "killed": "wall-clock"}, CLEAN | {"exit": -9, "killed": "oom", "oom_kill": 1}
FAILED = CLEAN | {"exit": 1}
REPLAYED = CLEAN | {"rejected_constant": None}
# Diagnostics as Lean printed them at each toolchain, paths already rewritten relative.
HEARTBEATS = {
    "pin": "Pairs/X__p0.lean:7:2: error: Tactic `simp` failed with a nested error:\n(deterministic) timeout at "
           "`isDefEq`, maximum number of heartbeats (100) has been reached\n",
    "legacy": "Pairs/X__p0.lean:6:57: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (100) "
              "has been reached\nuse `set_option maxHeartbeats <num>` to set the limit\n",
}
RECURSION = ("Pairs/X__p0.lean:7:2: error: tactic 'simp' failed, nested error:\nmaximum recursion depth has been "
             "reached\nuse `set_option maxRecDepth <num>` to increase limit\n")
KERNEL = ("Pairs/X__p0.lean:6:0: error: (kernel) declaration type mismatch, 'badk' has type\n  True\nbut it is "
          "expected to have type\n  False\n")
UNKNOWN = {"pin": "Pairs/X__p0.lean:8:8: error(lean.unknownIdentifier): Unknown identifier `outer`\n",
           "legacy": "Pairs/X__p0.lean:8:8: error: unknown identifier 'outer'\n"}
PLANT = ("replaying Pairs.X__p0\nuncaught exception: while replaying declaration 'planted_false':\n(kernel) "
         "declaration type mismatch, 'planted_false' has type\n  True\nbut it is expected to have type\n  False\n")
# Audit lines as ledger-audit printed them for constructed pairs.
ALLOWED = [{"name": "X__p0", "axioms_collector": [{"name": "propext", "module": "Init.Core", "via_own": False}],
            "axioms_walk": [{"name": "propext", "module": "Init.Core", "via_own": False}]}]
OWN_AXIOM = [{"name": "X__p0", "axioms_collector": [{"name": "ownAx", "module": None, "via_own": True}],
              "axioms_walk": [{"name": "ownAx", "module": None, "via_own": True}]}]
LIB_AX = {"name": "libAx", "module": "Pairs.lib__p0", "via_own": False}
IMPORTED_AXIOM = [{"name": "X__p0", "axioms_collector": [LIB_AX], "axioms_walk": [LIB_AX]}]


def facts(env: str, refusal=None, residue=False, compile=CLEAN, replay=REPLAYED, audit=CLEAN, decls=ALLOWED) -> dict:
    """The facts of a leg result of pair X__p0, stage by stage up to the first stage that did not end with exit 0,
    each stage's "text" its output field."""
    leg = {"env": env, "pair_id": "X__p0", "refusal": refusal, "path_residue": residue, "compile": None,
           "replay": None, "audit": None}
    for stage, value in (("compile", compile), ("replay", replay if env == "pin" else None),
                         ("audit", audit | {"decls": decls})):
        if refusal or value is None:
            continue
        leg[stage] = value | {classify.TEXT[stage]: value["text"]}
        if value["exit"] != 0:
            break
    return classify.facts_of(leg, ALLOWLIST)


CASES = {
    "any.refusal": facts("pin", refusal="no-decl"),
    "any.path_residue": facts("legacy", residue=True),
    "any.output_missing": facts("pin", compile=CLEAN | {"output_missing": True}),
    "any.oom": facts("legacy", compile=OOM),
    "any.wallclock": facts("pin", compile=WALL),
    "pin.heartbeats": facts("pin", compile=FAILED | {"text": HEARTBEATS["pin"]}),
    "legacy.heartbeats": facts("legacy", compile=FAILED | {"text": HEARTBEATS["legacy"]}),
    "any.stack": facts("legacy", compile=FAILED | {"text": RECURSION}),
    "any.kernel": facts("pin", compile=FAILED | {"text": KERNEL}),
    "pin.error": facts("pin", compile=FAILED | {"text": UNKNOWN["pin"]}),
    "legacy.error": facts("legacy", compile=FAILED | {"text": UNKNOWN["legacy"]}),
    "pin.replay.oom": facts("pin", replay=REPLAYED | OOM),
    "pin.replay.wallclock": facts("pin", replay=REPLAYED | WALL),
    "pin.replay.reject": facts("pin", replay=FAILED | {"text": PLANT, "rejected_constant": "planted_false"}),
    "pin.replay.harness": facts("pin", replay=FAILED | {"text": "uncaught exception: Could not find any oleans for: "
                                                                "Pairs.X__p0\n", "rejected_constant": None}),
    "any.audit.oom": facts("pin", audit=OOM),
    "any.audit.wallclock": facts("legacy", audit=WALL),
    "any.audit.harness": facts("pin", audit=FAILED | {"text": "object file './.lake/build/lib/lean/Pairs/X__p0.olean' "
                                                              "of module Pairs.X__p0 does not exist\n"}),
    "any.audit.decls": facts("pin", decls=[]),
    "any.audit.own": facts("legacy", decls=OWN_AXIOM),
    "any.audit.env": facts("pin", decls=IMPORTED_AXIOM),
    "any.accepted": facts("pin"),
    "any.unmatched": facts("pin", compile=FAILED | {"text": "INTERNAL PANIC: out of memory\n"}),
}


@pytest.mark.parametrize("row", [row["id"] for row in TABLE])
def test_row(row):
    """Each row of the seed table is the first to match the facts it names, and gives its own outcome."""
    # covers: test_unmatched_is_unclassified (row any.unmatched: a failed compile no pattern names is unclassified)
    outcome = next(r["outcome"] for r in TABLE if r["id"] == row)
    assert classify.leg_outcome(CASES[row], TABLE) == (outcome, row)


@pytest.mark.parametrize("table, reason", [
    ('version = "v2"\nrow = []\n', "is version v2"),
    ('version = "v1"\nrow = [{ id = "r", env = "any", stage = "compile", when = "oom_kill > 0", outcome = "oom" }]\n',
     "unknown conditions"),
], ids=["version", "condition"])
def test_load_refuses_table_it_cannot_apply(tmp_path, table, reason):
    """A table of another version than the constants name, or with a condition no code evaluates, stops at load,
    before any leg."""
    (tmp_path / CONSTS.published["classifier"]["table"]).parent.mkdir()
    (tmp_path / CONSTS.published["classifier"]["table"]).write_text(table)
    with pytest.raises(LedgerStop, match=reason):
        classify.load(tmp_path, CONSTS)
