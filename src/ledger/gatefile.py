"""The gate file: the dated, append-only record of every gate evaluation, one table row per line."""

import os
import re
from datetime import date
from pathlib import Path

from ledger import REPO, privacy
from ledger.types import LedgerStop

TEMPLATE = REPO / "templates/GATES.md.tmpl"
EVALUATORS = {"pipeline", "assistant", "operator", "stranger"}  # roles, never a person
WITHHELD = "[withheld]"  # what sanitize puts in place of text a gate line could not hold
GATES = {
    "prd-approved", "d-0-name", "d-0-research", "d0", "pin-amendment", "budget-check", "pre-d0-note-reply",
    "d7", "d7-frame", "d7-sample", "palomar-check", "independent-audit-check",
    "d14", "d14-outcome", "stop-loss", "legacy-cache-probe", "legacy-collector",
    "d21-legacy", "legacy-status", "classifier-freeze", "limit-freeze", "d21-proof-1", "d21-proof-1b",
    "d21-proof-2", "d21-proof-3", "d21-proof-3b", "branch-reduction", "d21-pilot", "route-one",
    "timer-enabled", "fixture-repeat",
    "rescope", "skipped-night", "d30-divergence-note", "d43",
    "d44-state", "notice", "route-two", "stranger-provisioning", "stranger-tree-deletion", "d48-smoke",
    "d50-tag", "proof-4", "d60", "timer-disabled", "d90", "proof-4b", "g1",
    "withdrawal", "outside-reproduction", "kill",
}
PARAMETERISED = re.compile(
    r"ceiling:[a-z0-9-]+|d30-attempt-[1-9][0-9]*|announce-[a-z0-9-]+|(?:g1-sweep|clone-count)-\d{4}-\d{2}-\d{2}")
SKEW = "skew"  # the route-two verdict that invokes the skew framing
ROUTE_TWO = (SKEW, "standard")  # the operator's notice-day verdict: the framing the README takes


def problem(gate: str, verdict: str, evaluator: str, reason: str) -> str | None:
    """Why a line with these fields breaks the gate file's rules, or None when it keeps them."""
    if gate not in GATES and not PARAMETERISED.fullmatch(gate):
        return f"unknown gate {gate!r}"
    if gate == "route-two" and verdict not in ROUTE_TWO:
        return f"the route-two verdict is one of {', '.join(ROUTE_TWO)}"
    if evaluator not in EVALUATORS:
        return "the evaluator is a role: pipeline, assistant, operator or stranger"
    if len(verdict) > 120 or len(reason) > 400:
        return "the verdict is over 120 or the reason over 400 characters"
    text = f"{verdict} {reason}"
    if re.search(r"[|\r\n]", text):
        return "a field contains | or a line break"
    if privacy.ROOTED.search(privacy.URL.sub("url", text)):
        return "a field contains an absolute path"
    # A non-public address (LAN, tailnet, loopback, link-local, documentation). A public one cannot be told from
    # a version string such as 1.2.3.4; the privacy sweep checks the policy's host_addresses, the public one too.
    if any(not address.is_global for address in privacy.addresses(text)):
        return "a field contains a host address"
    return None


def sanitize(policy, text: str, room: int) -> str:
    """Text from proof output made fit for a gate field, so that it never stops the run: | and line breaks
    replaced, cut to `room` characters, and withheld whole if `append` would still refuse it, for a path or an
    address or, under an operator policy, for anything the privacy sweep finds."""
    text = re.sub(r"[|\r\n]", "_", text)[:room]
    if problem("kill", "", "pipeline", text):
        return WITHHELD
    if policy.kind == "operator":
        try:
            privacy.sweep([("gates/GATES.md", text.encode())], policy)
        except LedgerStop:  # an empty denylist lands here too; append's own sweep then stops the run on it
            return WITHHELD
    return text


def _file(policy, create: bool = False) -> Path:
    """The policy's public tree's gate file once it exists; before that the bootstrap copy under the root,
    created from the preamble template on first use."""
    if "public_tree" in policy.values and (public := Path(policy.values["public_tree"], "gates/GATES.md")).exists():
        return public
    bootstrap = policy.root / "gates/GATES.md"
    if create and not bootstrap.exists():
        bootstrap.parent.mkdir(parents=True, exist_ok=True)
        tmp = bootstrap.with_name(f".GATES.md.{os.getpid()}")
        with open(tmp, "wb") as f:
            f.write(TEMPLATE.read_bytes())
            f.flush()
            os.fsync(f.fileno())
        try:
            os.link(tmp, bootstrap)  # appears complete, and only if still absent
        except FileExistsError:
            pass
        finally:
            tmp.unlink()
    return bootstrap


def append(policy, gate: str, verdict: str, evaluator: str, reason: str, today: date) -> None:
    """Append one line, refusing any that breaks the gate file's rules or, under an operator policy, holds
    anything the privacy sweep refuses."""
    if found := problem(gate, verdict, evaluator, reason):
        raise LedgerStop(f"gate line refused: {found}")
    line = f"| {today.isoformat()} | {gate} | {verdict} | {evaluator} | {reason} |\n"
    if policy.kind == "operator":
        privacy.sweep([("gates/GATES.md", line.encode())], policy)
    with open(_file(policy, create=True), "a", encoding="utf-8") as f:
        f.write(line)
        f.flush()
        os.fsync(f.fileno())


def rows(policy) -> list[tuple[str, ...]]:
    """Every recorded line as (date, gate, verdict, evaluator, reason), in file order."""
    path = _file(policy)
    if not path.exists():
        return []
    cells = [tuple(cell.strip() for cell in line.strip().strip("|").split("|"))
             for line in path.read_text(encoding="utf-8").splitlines() if line.startswith("|")]
    return [row for row in cells if row[0] not in ("date", "---")]


def d0(policy) -> date | None:
    """The D+0 date, from the d0 line; None before it is recorded."""
    return next((date.fromisoformat(row[0]) for row in rows(policy) if row[1] == "d0"), None)
