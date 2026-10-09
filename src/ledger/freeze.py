"""The D+21 freeze: the classifier table and the per-pair limit frozen in the published constants and committed
beside the pin, before the fixture run and the pilot; the D+14 pilot pin legs the frozen limit reopens; every earlier
leg outcome derived again from the frozen table; and the one re-freeze a failed proof permits."""

import hashlib
import json
import tomllib
from dataclasses import dataclass
from datetime import date
from pathlib import Path

from ledger import classify, constants, envbuild, gatefile, legs, measure, stage
from ledger.types import LedgerStop

V1, V2 = "classifier/table-v1.toml", "classifier/table-v2.toml"  # the frozen table, and the re-freeze's
PATHS = ("recipe/constants.toml", "gates/GATES.md")  # what a freeze commits in the public tree
LINES = ("classifier-freeze", "limit-freeze")  # the freeze's last writes: once both are recorded, it is done


@dataclass(frozen=True)
class FreezeReport:
    table_sha256: str
    limit_s: int
    rule: str  # which rule set the limit
    reopened: dict  # pair digest -> {reason, date}
    reclassified: list[str]  # the leg results whose outcome the frozen table changed


def frozen(pol) -> bool:
    """Whether the freeze is done: its last writes, the classifier-freeze and limit-freeze lines, recorded."""
    return set(LINES) <= {row[1] for row in gatefile.rows(pol)}


def _sha256(consts, path: str) -> str:
    return "sha256:" + hashlib.sha256((consts.repo / path).read_bytes()).hexdigest()


def _line(pol, gate: str, verdict: str, reason: str, today: date) -> None:
    """Append the line unless the retry of a freeze that died after writing it finds it recorded."""
    if (gate, verdict) not in {row[1:3] for row in gatefile.rows(pol)}:
        gatefile.append(pol, gate, verdict, "pipeline", reason, today)


def _commit(pol, message: str, paths: tuple[str, ...]) -> None:
    """Commit `paths` in the public tree, once it holds the gate file."""
    if pol.kind == "operator" and (public := Path(pol.values["public_tree"])).joinpath("gates/GATES.md").exists():
        stage.commit(public, pol.values["identity"], message, paths)


def freeze(pol, consts, prog, results: Path, today: date) -> FreezeReport:
    """The per-pair limit set from the D+14 pilot (measure.frozen_limit) with the rule used, and the classifier
    table's sha256 recorded; every D+14 pilot pin leg whose compile or replay wall-clock exceeds the frozen limit
    reopened, and every one killed at the provisional limit in any step when the frozen limit is longer; every
    earlier outcome derived again from the table; then the table set frozen, the classifier-freeze and limit-freeze
    lines written, and the change committed. Each write but those last ones is repeated to the same effect by a
    retry, so a freeze that died before its lines runs again whole. Refused once the lines are recorded."""
    if frozen(pol):
        raise LedgerStop("the freeze is recorded; a failed proof's one re-freeze is `freeze --rows`")
    seconds, rule = measure.frozen_limit(pol.root / measure.DIR)  # before any write: no figure, nothing frozen
    named = consts.published["classifier"]
    sha = _sha256(consts, named["table"])
    for key, value in (("table_sha256", f'"{sha}"'), ("per_pair_wall_clock_s", seconds),
                       ("per_pair_limit_rule", f'"{rule}"'), ("per_pair_limit_status", '"frozen"')):
        envbuild.set_constant(consts, key, str(value))
    reopened = {}
    for pair in prog.data["d14_pilot"]["attempted"]:
        if not (path := prog.data["legs"][pair]["pin"]["leg"]):
            continue  # no result yet: pass 1 runs it
        leg = json.loads((results / path).read_text())
        killed = any(leg[step] and leg[step]["killed"] == "wall-clock" for step in ("compile", "replay", "audit"))
        if killed and seconds > leg["limits"]["wall_clock_limit_s"]:
            reopened[pair] = {"reason": "killed-at-provisional", "date": today.isoformat()}
        elif any(leg[step] and leg[step]["wall_s"] > seconds for step in ("compile", "replay")):
            reopened[pair] = {"reason": "over-frozen-limit", "date": today.isoformat()}
    prog.reopen(reopened)
    consts = constants.load(consts.repo)
    changed = legs.reclassify(prog, results, classify.load(consts.repo, consts), consts)
    envbuild.set_constant(consts, "status", '"frozen"')
    _line(pol, "classifier-freeze", f"{named['version']} frozen", f"table={named['table']}; sha256={sha}", today)
    _line(pol, "limit-freeze", f"per_pair_wall_clock_s={seconds}", f"rule={rule}", today)
    _commit(pol, f"Freeze: classifier table, per-pair limit {seconds} s", PATHS)
    return FreezeReport(sha, seconds, rule, reopened, changed)


def refreeze(pol, consts, prog, results: Path, rows: list[str], today: date) -> list[str]:
    """A failed proof's one re-freeze, once a d21-proof line records a fail, before the first pass-1 run (no
    timer-enabled line): with table v1 frozen, classifier/table-v2.toml, of version v2 and changed from v1 in the
    named rows alone, frozen in its place, every earlier outcome derived again from it, its classifier-freeze line
    written, and the change committed. The version is set last, so a re-freeze that died before it runs again whole.
    Returns the leg results changed."""
    named = consts.published["classifier"]
    if named["status"] != "frozen" or named["version"] != "v1":
        raise LedgerStop(f"the re-freeze follows the v1 freeze, once: the classifier is {named['version']}, "
                         f"{named['status']}")
    recorded = gatefile.rows(pol)
    if not any(row[1].startswith("d21-proof-") and row[2] == "fail" for row in recorded):
        raise LedgerStop("the re-freeze follows a failed proof, and no d21-proof line records a fail")
    if any(row[1] == "timer-enabled" for row in recorded):
        raise LedgerStop("the re-freeze comes before the first pass-1 run, and the timer is enabled")
    old = tomllib.loads((consts.repo / V1).read_text())["row"]
    new = tomllib.loads((consts.repo / V2).read_text())
    if new["version"] != "v2" or [row for row in old if row["id"] not in rows] != [
            row for row in new["row"] if row["id"] not in rows]:
        raise LedgerStop(f"{V2}: not version v2, or it changes rows other than {', '.join(rows)}")
    sha = _sha256(consts, V2)
    for key, value in (("table_sha256", sha), ("table", V2)):
        envbuild.set_constant(consts, key, f'"{value}"')
    changed = legs.reclassify(prog, results, new["row"], consts)
    _line(pol, "classifier-freeze", f"v2 re-frozen: {', '.join(rows)}", f"table={V2}; sha256={sha}", today)
    envbuild.set_constant(consts, "version", '"v2"')
    _commit(pol, f"Re-freeze: classifier table v2, rows {', '.join(rows)}", PATHS + (V2,))
    return changed
