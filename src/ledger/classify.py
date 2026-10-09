"""Classification: the published decision table that maps one leg's facts to its outcome, and the derivation of
a pair's class from its two leg outcomes and any override. Nothing else classifies a leg or a pair."""

import hashlib
import re
import tomllib

from ledger.types import LedgerStop

STAGES = ("assemble", "compile", "replay", "audit")  # pipeline order
RETRYABLE = {"oom", "stack", "unclassified"}  # retried up to the attempt bound; every other outcome is terminal
CONDITIONS = {  # the conditions a row's `when` may join with " and ", over one stage's facts
    "exit==0": lambda f: f["exit"] == 0,
    "exit!=0": lambda f: f["exit"] != 0,
    "killed==wall-clock": lambda f: f["killed"] == "wall-clock",
    "oom_kill>0": lambda f: f["oom_kill"] > 0,
    "refusal!=null": lambda f: f["refusal"] is not None,
    "path_residue": lambda f: f["path_residue"],
    "output_missing": lambda f: f["output_missing"],
    "rejected_constant!=null": lambda f: f["rejected_constant"] is not None,
    "audit.own_bad": lambda f: f["own_bad"],
    "audit.env_bad": lambda f: f["env_bad"],
    "audit.other_decls": lambda f: f["other_decls"],
}
TEXT = {"compile": "diagnostics", "replay": "output", "audit": "stderr"}  # the output a stage's pattern searches
OK = {"accepted", "accepted-env-axiom"}
FAILS = {"elab-error", "kernel-reject", "audit-failure"}
NO_RESULT = {"harness": "harness-error", "unclassified": "unclassified", "timeout-heartbeats": "timed-out",
             "timeout-wall-clock": "timed-out", "oom": "resource-exhausted", "stack": "resource-exhausted"}
CLASSES = ("harness-error", "unclassified", "timed-out", "resource-exhausted", "rejected-by-replay", "reproduced",
           "environment-undeclared", "environment-mismatch", "axiom-audit-failure", "rejected-by-checker")
KILLED = {"outcome": "unclassified", "table_row": None, "diagnostic": "no outcome: run killed", "compile": None,
          "replay": None, "audit": None}  # a leg killed before an outcome on every attempt: no facts, so no row


def load(repo, consts) -> list[dict]:
    """The rows of the table the published constants name, of the version they name, every condition one of
    CONDITIONS; once frozen, only the file whose sha256 they record."""
    named = consts.published["classifier"]
    data = (repo / named["table"]).read_bytes()
    if named["status"] == "frozen" and "sha256:" + hashlib.sha256(data).hexdigest() != named["table_sha256"]:
        raise LedgerStop(f"{named['table']} is not the frozen table: its sha256 differs from table_sha256")
    table = tomllib.loads(data.decode())
    if table["version"] != named["version"]:
        raise LedgerStop(f"{named['table']} is version {table['version']}, the constants name {named['version']}")
    for row in table["row"]:
        if unknown := [c for c in row["when"].split(" and ") if c not in CONDITIONS]:
            raise LedgerStop(f"{named['table']}: row {row['id']} has unknown conditions {unknown}")
    return table["row"]


def facts_of(leg: dict, allowlist: list[str]) -> dict:
    """The facts the table reads, from a leg result alone, so that its outcome can be derived again from the
    record: at the assembly the refusal and the path residue; per stage that ran its fields and its output as
    "text"; at the audit the axiom flags, and whether it reported anything but the pair's one declaration."""
    facts = {"env": leg["env"], "assemble": {"refusal": leg["refusal"], "path_residue": leg["path_residue"]}}
    for stage, text in TEXT.items():
        if leg[stage] is not None:
            facts[stage] = leg[stage] | {"text": leg[stage][text]}
    if leg["audit"] is not None:
        own_bad, env_bad, _ = audit_flags(leg["audit"]["decls"], allowlist)
        facts["audit"] |= {"own_bad": own_bad, "env_bad": env_bad,
                           "other_decls": [d["name"] for d in leg["audit"]["decls"]] != [leg["pair_id"]]}
    return facts


def leg_outcome(facts: dict, table: list[dict]) -> tuple[str, str]:
    """The outcome and row id of the first row, stage by stage in pipeline order and row by row within a stage,
    whose env, condition and pattern match `facts`: {"env", and per stage that ran, its facts}. A pattern is
    searched over the stage's "text"."""
    for stage in STAGES:
        if (found := facts.get(stage)) is None:
            continue
        for row in table:
            if (row["stage"] == stage and row["env"] in ("any", facts["env"])
                    and all(CONDITIONS[c](found) for c in row["when"].split(" and "))
                    and ("pattern" not in row or re.search(row["pattern"], found["text"], re.MULTILINE))):
                return row["outcome"], row["id"]
    raise LedgerStop("no table row matches the leg's facts")


def rederive(leg: dict, table: list[dict], allowlist: list[str]) -> tuple[str, str | None]:
    """The outcome and row of a leg result, with its env, pair_id and refusal, derived again from the facts it
    stores. Two legs have no row and keep their outcome: one killed on every attempt, which has no facts (its
    caller checks the attempts), and a harness leg whose own output could not be read, whose facts the table
    reads as no outcome or as harness too: its audited declarations unreadable, or no row matching. Stops on any
    other leg with no row."""
    where = f"{leg['pair_id']}, {leg['env']} leg"
    if leg["table_row"] is not None:
        return leg_outcome(facts_of(leg, allowlist), table)
    if leg["outcome"] == "harness":
        try:
            facts = facts_of(leg, allowlist)
        except (KeyError, TypeError):  # the audited declarations as unreadable as when the leg ran
            return "harness", None
        try:
            found = leg_outcome(facts, table)
        except LedgerStop:  # no row matches
            return "harness", None
        if found[0] != "harness":
            raise LedgerStop(f"{where}: harness with no table row, yet the table derives {found} from its facts")
        return "harness", None
    if any(leg.get(key) != value for key, value in KILLED.items()):
        raise LedgerStop(f"{where}: no table row, yet not a leg killed on every attempt")
    return leg["outcome"], None


def audit_flags(decls: list[dict], allowlist: list[str]) -> tuple[bool, bool, bool]:
    """own_bad, env_bad and the disagreement, over the union of the collector's and the walk's axioms of every
    audited declaration. own_bad: any sorryAx, or an axiom off the allowlist that the pair's own module declares
    or uses directly; env_bad: an axiom off the allowlist reached only through imported constants. The two
    lists disagree when their (name, module) sets differ."""
    own_bad = env_bad = disagreement = False
    for decl in decls:
        found = {}
        for axiom in decl["axioms_collector"] + decl["axioms_walk"]:
            via_own = found.get(axiom["name"], (None, False))[1] or axiom["via_own"]
            found[axiom["name"]] = (axiom["module"], via_own)
        for name, (module, via_own) in found.items():
            if name == "sorryAx" or name not in allowlist and (module is None or via_own):
                own_bad = True
            elif name not in allowlist:
                env_bad = True
        disagreement |= ({(a["name"], a["module"]) for a in decl["axioms_collector"]}
                         != {(a["name"], a["module"]) for a in decl["axioms_walk"]})
    return own_bad, env_bad, disagreement


def derive(pin: str | None, legacy: str | None, replay: dict | None, harness: dict | None, declared: str) -> str:
    """The pair's class from its terminal pin and legacy leg outcomes (None: no terminal outcome), its replay and
    harness overrides, and whether its declared revision is "standing", "unavailable" or "none"; the first rule
    that applies wins. Stops on an incomplete pair, a legacy outcome where none is declared, or a replay
    override not recorded (`at`, UTC to the second) before a harness override, an order the pipeline cannot
    produce."""
    if pin is None or (legacy is None) == (declared == "standing"):
        raise LedgerStop(f"no class: pin {pin}, legacy {legacy}, declared {declared}")
    if replay and harness and replay["at"] >= harness["at"]:
        raise LedgerStop(f"the replay override of {replay['at']} is not before the harness override of {harness['at']}")
    if harness and not replay:
        return "harness-error"
    if pin in NO_RESULT:
        return NO_RESULT[pin]
    if pin == "replay-reject" or replay:
        return "rejected-by-replay"
    if pin in OK:
        return "reproduced"
    if pin in FAILS and (legacy is None or legacy in NO_RESULT):
        return "environment-undeclared"
    if pin in FAILS and legacy in OK:
        return "environment-mismatch"
    if pin in FAILS and legacy in FAILS:
        return "axiom-audit-failure" if "audit-failure" in (pin, legacy) else "rejected-by-checker"
    raise LedgerStop(f"no class: pin {pin}, legacy {legacy}")


def skew_case(pin: str, legacy: str | None, replay: dict | None, harness: dict | None) -> str | None:
    """The pair's cell of the skew table, or None when it has no legacy leg or its pin side has no result: a
    pin outcome with no result, or a harness override not preceded by a replay override."""
    if legacy is None or pin in NO_RESULT or harness and not replay:
        return None
    if legacy in NO_RESULT:
        return "unverifiable-declared"
    return {(True, True): "both", (True, False): "pin-only", (False, True): "declared-only",
            (False, False): "fails-both"}[pin in OK and not replay, legacy in OK]


def is_mismatch_kernel(cls: str, pin_row: str | None) -> bool:
    """Whether the pair joins the kernel-rejection shortlist: environment-mismatch with a pin leg the kernel row
    decided. It splits the count of that class and never changes a class."""
    return cls == "environment-mismatch" and pin_row == "any.kernel"
