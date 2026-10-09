"""Records: results/records.jsonl, one line per sampled pair in draw order. Each is derived from the pair's leg
results, its overrides and the decision table, and carries every fact the table reads, so that the published
records and table alone derive every leg outcome and class again. A record is written whole, never edited."""

import hashlib
import json
import re
from collections import Counter
from pathlib import Path

from ledger import classify
from ledger.types import Digest, LedgerStop, canonical

SCHEMA = "record/1"
FIELDS = {"schema_version", "classifier_version", "code_commit", "i", "pair_id", "decl", "k", "split", "position",
          "element_sha256", "pair_sha256", "source_sha256", "recipe_ids", "refusal", "legs", "overrides", "declared",
          "class", "skew_case", "aggregate", "mismatch_kernel_rejection", "provenance", "withdrawn"}
LEG = {"outcome", "table_row", "attempts", "limits", "compile", "replay", "audit", "audit_disagreement",
       "path_residue"}  # a record's leg, and a leg with no row has its diagnostic too
RAN = {"exit", "killed", "oom_kill", "wall_s", "peak_mem_kb", "output_truncated"}  # the keys a record's stage has:
STAGE = {"compile": RAN | {"diagnostics", "output_missing", "peak_mem_source", "max_rss_kb"},
         "replay": RAN | {"rejected_constant", "output"}, "audit": RAN | {"stderr", "decls"}}  # max_rss_kb optional
SOURCES = {"replay": {"d14-pilot", "d21-pilot", "d44"},
           "harness": {"d21-rehearsal", "crosspass-d21", "crosspass-d44", "aggregate-elab"}}
OVERRIDE = {"replay": {"source", "constant", "date", "at"}, "harness": {"source", "detail", "date", "at"}}
DECIDED_BY = {  # what decided a pair's class, by its override's source
    "d14-pilot": "the D+14 pilot's replay", "d21-pilot": "the D+21 pilot's replay", "d44": "the D+44 aggregate replay",
    "d21-rehearsal": "the D+21 rehearsal of its pin leg, whose outcome differed from D+14's",
    "crosspass-d21": "the D+21 cross-pass check, where it differed in the aggregate from its own check",
    "crosspass-d44": "the D+44 cross-pass check, where it differed in the aggregate from its own check",
    "aggregate-elab": "the aggregate's build, which failed on its lines"}
AT = re.compile(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z")


class Pending(LedgerStop):
    """A drawn pair has no record yet: a leg its record needs is not terminal."""


def _leg(leg: dict, attempts: int) -> dict:
    """A leg result as its pair's record carries it: its outcome, limits and the facts of every stage that ran,
    the audit's without its disagreement, which the record derives, and each audited declaration without its
    printed type."""
    stages = {stage: leg[stage] and {k: v for k, v in leg[stage].items() if k != "disagreement"} for stage in STAGE}
    if audit := stages["audit"]:
        audit["decls"] = [{k: v for k, v in decl.items() if k != "type_pp"} for decl in audit["decls"]]
    return {k: leg[k] for k in LEG | {"diagnostic"} if k in leg} | stages | {"attempts": attempts}


def _classed(record: dict, table: list, consts) -> dict:
    """`record` with what its legs and overrides give: each leg's audit disagreement, the class, skew case and
    kernel shortlist flag, and the aggregate. A pair is in the aggregate while it is reproduced, and was removed
    from it when its pin leg passed and an override stands against it. The aggregate's fresh replay is
    unavailable when the constants say so, rejected the pair when the D+44 replay's override stands, and
    otherwise accepted it only if it is a member and the record says so; else it has not run. Stops unless the
    table derives each leg's recorded outcome and row from the facts the record carries, after from 1 to the
    attempt bound's attempts, and after exactly the bound's on a retryable outcome."""
    published, legs = consts.published, {}
    allowlist, bound = published["audit"]["allowlist"], published["limits"]["attempt_bound"]
    for env in ("pin", "legacy"):
        if (leg := record["legs"][env]) is not None:
            attempts = leg["attempts"]
            if not (type(attempts) is int and 1 <= attempts <= bound) or (
                    leg["outcome"] in classify.RETRYABLE and attempts != bound):
                raise LedgerStop(f"{record['pair_id']}, {env} leg: {leg['outcome']} after {attempts!r} attempts, "
                                 f"with an attempt bound of {bound}")
            found = classify.rederive(leg | {"env": env, "pair_id": record["pair_id"], "refusal": record["refusal"]},
                                      table, allowlist)
            if found != (recorded := (leg["outcome"], leg["table_row"])):
                raise LedgerStop(f"{record['pair_id']}, {env} leg: the table derives {found}, not the recorded "
                                 f"{recorded}")
            audit = leg["audit"]
            leg = leg | {"audit_disagreement": bool(audit and classify.audit_flags(audit["decls"], allowlist)[2])}
        legs[env] = leg
    pin, legacy = (leg and leg["outcome"] for leg in legs.values())
    replay, harness = record["overrides"]["replay"], record["overrides"]["harness"]
    cls = classify.derive(pin, legacy, replay, harness, record["declared"])
    removed = cls if pin in classify.OK and cls in ("rejected-by-replay", "harness-error") else None
    member = cls == "reproduced"
    fresh = ("replay-unavailable" if published["status"]["independent_check"] == "replay-unavailable"
             else "rejected" if (replay or {}).get("source") == "d44"
             else "accepted" if member and record["aggregate"]["fresh"] == "accepted" else "not-run")
    return record | {"legs": legs, "class": cls, "skew_case": classify.skew_case(pin, legacy, replay, harness),
                     "mismatch_kernel_rejection": classify.is_mismatch_kernel(cls, legs["pin"]["table_row"]),
                     "aggregate": {"member": member, "removed_cause": removed, "fresh": fresh}}


def _declared(prog, sha: str, published) -> str:
    """Whether the pair's declared revision is "standing", "unavailable" (the legacy environment is) or "none"."""
    return ("none" if sha in prog.data.get("declared_none", []) else
            "unavailable" if published["status"]["legacy"] == "environment-unavailable" else "standing")


def pair_class(prog, results: Path, sha: str, published) -> str:
    """The class a pair's record carries, from its terminal legs' outcomes, its overrides and its declared revision
    alone, without building the record."""
    found = {env: json.loads((results / state["leg"]).read_text())["outcome"]
             for env, state in prog.data["legs"][sha].items()}
    declared = _declared(prog, sha, published)
    return classify.derive(found["pin"], found.get("legacy") if declared == "standing" else None,
                           *(prog.data.get(f"{kind}_overrides", {}).get(sha) for kind in ("replay", "harness")),
                           declared)


def legs_text(outcomes: dict[str, str], cls: str | None = None, overrides: dict | None = None,
              earlier: bool = False) -> str:
    """A pair's legs by outcome, the pin's first, as a run report gives them: "pin elab-error and legacy accepted";
    with `cls`, the class the pair carries, and its replay and harness `overrides`, what decided the class when an
    override did and its legs alone did not: the replay override where there is one, which wins, else the harness's;
    `earlier` when the override came before the night whose run completed the legs, which then gives its day too."""
    text = " and ".join(f"{env} {outcomes[env]}" for env in ("pin", "legacy") if env in outcomes)
    if cls and cls != classify.derive(outcomes["pin"], outcomes.get("legacy"), None, None,
                                      "standing" if "legacy" in outcomes else "none"):
        found = overrides["replay"] or overrides["harness"]
        text += (f", the class decided on {found['date']} by {DECIDED_BY[found['source']]}, before tonight's run, "
                 "which only completed the legs" if earlier else f", decided by {DECIDED_BY[found['source']]}")
    return text


def build(sample: dict, assembled: list[dict], prog, results: Path, table: list, consts,
          withdrawals: Path | None = None) -> list[dict]:
    """The records of the draw up to the published cut, in draw order: one per line of work/assembled.jsonl, its
    identity from work/sample.json, its legs the results the progress file points at under `results` (the legacy
    leg only while a revision is declared and the legacy environment stands), its overrides from the progress
    file and its withdrawal from `withdrawals`, results/withdrawals.jsonl by default. The code commit is the pin
    leg's. The aggregate's fresh replay accepted a member once the replay returned; a pilot's override is not that
    replay's verdict. Stops (Pending) on a pair whose required legs are not all terminal, or on one whose leg
    outcome the table does not derive."""
    published = consts.published
    path = withdrawals or results / "withdrawals.jsonl"
    lines = path.read_text().splitlines() if path.exists() else []
    withdrawn = {w.pop("pair_sha256"): w for w in map(json.loads, lines)}
    returned = "accepted" if prog.data.get("aggregate", {}).get("state") == "replay-returned" else "not-run"
    built = []
    for pair in assembled[:published["sampling"]["cut_n"] or None]:
        sha, row = pair["pair_sha256"], sample["draw"][pair["i"]]
        declared = _declared(prog, sha, published)
        files = {}
        for env in ("pin", "legacy") if declared == "standing" else ("pin",):
            state = prog.data["legs"].get(sha, {}).get(env)
            if not (state and state["terminal"]):
                raise Pending(f"{pair['pair_id']}: its {env} leg is not terminal, so the pair has no record yet")
            files[env] = json.loads((results / state["leg"]).read_text())
        record = _classed({
            "schema_version": SCHEMA, "classifier_version": published["classifier"]["version"],
            "code_commit": files["pin"]["code_commit"], "pair_sha256": sha, "element_sha256": pair["element_sha256"],
            **{key: row[key] for key in ("i", "pair_id", "decl", "k", "split", "position")},
            "source_sha256": "sha256:" + consts.source["sha256"], "refusal": pair["refusal"], "declared": declared,
            "recipe_ids": {env: files[env]["recipe_id"] if env in files else None for env in ("pin", "legacy")},
            "legs": {env: _leg(files[env], prog.attempts(sha, env)) if env in files else None
                     for env in ("pin", "legacy")},
            "overrides": {"replay": prog.data.get("replay_overrides", {}).get(sha),
                          "harness": prog.data.get("harness_overrides", {}).get(sha)},
            "provenance": files["pin"]["provenance"], "withdrawn": withdrawn.get(sha),
            "aggregate": {"fresh": returned},
        } | ({"dev_overlay": True} if any(leg.get("dev_overlay") for leg in files.values()) else {}), table, consts)
        built.append(record)
    return built


def dump(records: list[dict]) -> bytes:
    """records.jsonl's bytes: one canonical line per record, in order. Stops on a pair named twice, or records
    not in draw order."""
    for key in ("pair_id", "pair_sha256"):
        if twice := [value for value, n in Counter(r[key] for r in records).items() if n > 1]:
            raise LedgerStop(f"duplicate {key}: {twice}")
    if any(a["i"] >= b["i"] for a, b in zip(records, records[1:])):
        raise LedgerStop("the records are not in draw order")
    return b"".join(map(canonical, records))


def validate(record: dict, consts) -> None:
    """Stop unless `record` is an object with exactly a record's fields (and the development overlay's mark,
    true), is of this schema, with an integer draw index, a declared status, a class of the classifier, a known
    provenance and a withdrawal null or exactly a withdrawal's fields; overrides replay and harness, each null or
    exactly an override's fields, of a known source, `at` a UTC time to the second and `date` its date; legs pin
    and legacy, each null or exactly a leg's fields, a diagnostic too if and only if it has no row, with every
    stage null or an object with exactly that stage's keys, max_rss_kb optional, no replay on the legacy leg and
    one on the pin leg if it was audited; and a legacy recipe exactly when it has a legacy leg; and unless it is
    of the classifier version the constants name, and declared neither unavailable while the constants say the
    legacy environment is not, nor standing while they say it is."""
    if not isinstance(record, dict):
        raise LedgerStop(f"{record!r}: not a {SCHEMA} record")
    legs, overrides, withdrawn, ids = (record.get(key) for key in ("legs", "overrides", "withdrawn", "recipe_ids"))
    if not (isinstance(legs, dict) and record.keys() - {"dev_overlay"} == FIELDS and record["schema_version"] == SCHEMA
            and record.get("dev_overlay", True) is True and isinstance(record["i"], int)
            and record["declared"] in ("standing", "unavailable", "none") and record["class"] in classify.CLASSES
            and record["provenance"] in ("from-source", "cache-seeded")
            and (withdrawn is None or isinstance(withdrawn, dict) and withdrawn.keys() == {"date", "party_class",
                                                                                          "ground"})
            and isinstance(overrides, dict) and overrides.keys() == SOURCES.keys() and all(
                found is None or isinstance(found, dict) and found.keys() == OVERRIDE[kind]
                and isinstance(found["source"], str) and found["source"] in SOURCES[kind]
                and isinstance(found["at"], str) and AT.fullmatch(found["at"]) and found["date"] == found["at"][:10]
                for kind, found in overrides.items())
            and legs.keys() == {"pin", "legacy"} and all(
                leg is None or isinstance(leg, dict) and leg.keys() - {"diagnostic"} == LEG
                and ("diagnostic" in leg) == (leg["table_row"] is None)
                and all(leg[stage] is None or isinstance(leg[stage], dict)
                        and keys - {"max_rss_kb"} <= leg[stage].keys() <= keys for stage, keys in STAGE.items())
                for leg in legs.values()) and (legs["legacy"] or {}).get("replay") is None
            and ((legs["pin"] or {}).get("audit") is None or legs["pin"]["replay"] is not None)
            and isinstance(ids, dict) and ids.keys() == legs.keys()
            and (ids["legacy"] is None) == (legs["legacy"] is None)):
        raise LedgerStop(f"{record.get('pair_id')}: not a {SCHEMA} record")
    if record["classifier_version"] != (version := consts.published["classifier"]["version"]):
        raise LedgerStop(f"{record['pair_id']}: a record of classifier {record['classifier_version']}, not {version}")
    status = consts.published["status"]["legacy"]
    if record["declared"] == ("standing" if status == "environment-unavailable" else "unavailable"):
        raise LedgerStop(f"{record['pair_id']}: declared {record['declared']}, yet the legacy environment is {status}")


def _not_a_number(name: str):
    raise ValueError(f"{name} is not a JSON number")


def from_records(path: Path, table: list, consts) -> bytes:
    """`report --from-records`: derive every record of a records.jsonl again from its own facts and `table`
    alone, and return the bytes, which are the file's. Stops on a record not of this schema and classifier
    version, or malformed below its legs, a pair named twice or out of draw order, a leg outcome the table does
    not derive, a class, skew case, shortlist flag, audit disagreement or aggregate status that the record's
    legs, overrides and the constants do not give, or members the aggregate's one fresh replay gave two
    statuses."""
    data, found, classed = path.read_bytes(), [], []
    for n, line in enumerate(data.splitlines(), 1):
        try:
            found.append(json.loads(line, parse_constant=_not_a_number))
        except (ValueError, RecursionError) as error:  # JSONDecodeError is a ValueError
            raise LedgerStop(f"{path.name}, line {n}: not JSON: {error}") from error
    for record in found:
        validate(record, consts)
    for record in found:
        try:
            classed.append(_classed(record, table, consts))
        except (KeyError, TypeError) as error:
            raise LedgerStop(f"{record['pair_id']}: not a {SCHEMA} record, a field is malformed: {error!r}") from error
    if len({r["aggregate"]["fresh"] for r in classed if r["aggregate"]["member"]}) > 1:
        raise LedgerStop(f"{path.name}: the aggregate's fresh replay both accepted members and has not run on others")
    again = dump(classed)
    if again != data:  # each has a line per record
        n = next(n for n, lines in enumerate(zip(data.splitlines(keepends=True), again.splitlines(keepends=True)))
                 if lines[0] != lines[1])
        raise LedgerStop(f"{path.name}: the bytes of line {n + 1}, {found[n]['pair_id']}, do not derive from its own "
                         f"facts")
    return again


def axioms(pair_id: str, audit: dict | None) -> str:
    """A pair's axiom list: every axiom the collector or the walk reports for its own declaration in its pin leg's
    audit, allowlisted ones included, each once, in codepoint order, joined by commas; empty with no audit."""
    decls = [decl for decl in (audit or {"decls": []})["decls"] if decl["name"] == pair_id]
    return ",".join(sorted({a["name"] for decl in decls for a in decl["axioms_collector"] + decl["axioms_walk"]}))


def subset_sha256(lines: list[tuple[str, str, str]]) -> Digest:
    """sha256 over one "<pair_sha256>\t<class or outcome>\t<axiom list>\n" line per pair, sorted by pair_sha256."""
    return "sha256:" + hashlib.sha256("".join(f"{a}\t{b}\t{c}\n" for a, b, c in sorted(lines)).encode()).hexdigest()

