"""The D+21 pilot: the first 30 pairs of the draw end to end through both environments under the frozen constants,
their pin legs a rehearsal of D+14's; route one; the fit check against the pass-1 nights; and, in a unit of its own,
the pilot replay under the cap in force. A re-scope at any of them is the single permitted one: a second is the kill."""

import json
import time
from dataclasses import dataclass
from datetime import date

from ledger import aggregate, classify, freeze, gatefile, legs, measure
from ledger.types import LedgerStop

PAIRS = 30
NIGHTS = 21  # D+22 to D+43, the D+30 night excluded
ROUTE_ONE = 20  # of the 30 pairs in an environment class: the skew framing is invoked
ENVIRONMENT = {"environment-mismatch", "environment-undeclared"}


@dataclass(frozen=True)
class D21Report:
    verdict: str  # met, rescope or kill, as the d21-pilot line has it
    reason: str


def nights(pol) -> int:
    """The pass-1 nights: 21, less each recorded skipped night, and less the D+22 night where a D+21 proof failed,
    since its fixture run is repeated then."""
    rows = gatefile.rows(pol)
    repeat = any(row[1].startswith("d21-proof-") and row[2] == "fail" for row in rows)
    return NIGHTS - sum(row[1] == "skipped-night" for row in rows) - repeat


def _rescope(run, n: int, cause: str) -> tuple[str, list[list]]:
    """The single permitted re-scope, to the first `n` pairs of the draw, for `cause`; the kill where a rescope line
    is already recorded, or where no pair fits. Returns the verdict and its writes, for aggregate._write, which saves
    them before it makes any, as the D+44 check's are."""
    if any(row[1] == "rescope" for row in gatefile.rows(run.pol)) or n < 1:
        return "kill", [["kill", "a second re-scope" if n >= 1 else "no cut fits", f"d21: {cause}; N={n}"]]
    return "rescope", [["cut_n", n, ""], ["rescope", f"cut_n={n}", f"d21: {cause}"]]


def _outcome(run, pair: str, env: str) -> str:
    """The outcome of the latest result of the pair's leg in `env`."""
    return json.loads((run.results / run.progress.data["legs"][pair][env]["leg"]).read_text())["outcome"]


def d21(run, pairs: list[dict], today: date, clock=time.monotonic) -> D21Report:
    """PRD § D+21's pilot over `run`, legs.prepare's over the environments that stand, and `pairs`, the draw's lines
    in draw order, under the frozen constants: the first 30 pairs of the sample through one pass 1 at the preflight
    worker count, every leg they need, each pin leg of a D+14 pilot pair run again as a rehearsal, but for one
    reopened at the freeze, which runs again with no match required. A rehearsal whose outcome is not the one the
    D+14 measurement recorded makes the pair harness-error (d21-rehearsal) and fails the pilot, which is routed as
    nothing end to end: the re-scope, cut to the pairs complete and as many more as the pass-1 nights hold at 14 hours
    each and the parallel-amortised per-pair cost, the pass's wall-clock over the pairs it ran, saved as the pass
    returns, so a restart whose pass runs none costs by the saved one, and with none saved refuses. The fit check cuts
    the same way where the rest of the sample does not fit. 20 or more of the 30 in an environment class write
    route-one. Writes the d21-pilot line, saved with the others the verdict makes before any is made, so a pilot
    restarted after it died there makes the rest and returns the recorded verdict. A restarted pilot reopens no
    rehearsed leg a second time."""
    published, prog = run.consts.published, run.progress
    if not freeze.frozen(run.pol):
        raise LedgerStop("the pilot runs under the frozen classifier table and per-pair limit: freeze first")
    aggregate._flush(run, today)
    if done := next((row for row in gatefile.rows(run.pol) if row[1] == "d21-pilot"), None):
        return D21Report(done[2], done[4])
    sample = pairs[:published["sampling"]["cut_n"] or None]
    pilot, ceiling = sample[:PAIRS], published["limits"]["run_ceiling_s"]
    recorded = json.loads((run.pol.root / measure.DIR / "pairs.json").read_text())
    d14 = {row["pair_id"]: row["outcome"] for row in recorded}
    rehearsed = {pair["pair_sha256"]: d14[pair["pair_id"]] for pair in pilot
                 if pair["pair_id"] in d14 and pair["pair_sha256"] not in prog.data.get("reopened", {})}
    prog.reopen(dict.fromkeys(pair for pair in rehearsed if prog.reopened_at(pair, "pin") == 0))
    attempts = [sum(prog.attempts(pair["pair_sha256"], env) for env in run.trees) for pair in pilot]
    start = clock()
    legs.pass1(run, pilot, ceiling)
    ran = sum(sum(prog.attempts(pair["pair_sha256"], env) for env in run.trees) > before
              for pair, before in zip(pilot, attempts))  # those the ceiling let start
    if ran:  # saved before anything derives from it: a restart's pass starts nothing, and uses this
        prog.note(d21_pass={"wall_s": clock() - start, "ran": ran})
    if not (measured := prog.aggregate().get("d21_pass")):
        raise LedgerStop("the pilot's pass started no pair and no earlier pass's figure is saved: no per-pair cost "
                         "for the fit check")
    per_pair = measured["wall_s"] / measured["ran"]
    mismatched = {pair: {"source": "d21-rehearsal", "detail": f"pin {before} at D+14, {after} at D+21"}
                  for pair, before in rehearsed.items() if (after := _outcome(run, pair, "pin")) != before}
    if mismatched:
        prog.remove(mismatched, "harness-error", today)
    complete = [pair["pair_sha256"] for pair in pilot if not prog.pending_pairs([pair], list(run.trees))]
    declared = "standing" if "legacy" in run.trees else "unavailable"
    classes = [classify.derive(_outcome(run, pair, "pin"), _outcome(run, pair, "legacy") if "legacy" in run.trees
                               else None, prog.data.get("replay_overrides", {}).get(pair),
                               prog.data.get("harness_overrides", {}).get(pair), declared) for pair in complete]
    environment = sum(cls in ENVIRONMENT for cls in classes)
    writes = [["route-one", "skew framing invoked", f"{environment} of {len(pilot)} pilot pairs in an environment "
                                                    "class"]] if environment >= ROUTE_ONE else []
    room, left = nights(run.pol) * ceiling, len(sample) - len(complete)
    causes = [cause for cause, applies in (
        (f"rehearsal mismatch: {len(mismatched)} pairs harness-error", mismatched),
        ("nothing end to end", not complete),
        (f"the fit check: {left} pairs at {per_pair:.0f} s each over {room} s", per_pair * left > room)) if applies]
    n = min(len(sample), len(complete) + aggregate._fit(room, per_pair))
    verdict, cut = _rescope(run, n, "; ".join(causes)) if causes else ("met", [])
    reason = (f"{'; '.join(causes) or 'end to end and fits'}; complete={len(complete)}; per_pair_s={per_pair:.1f}; "
              f"nights={room // ceiling}; environment_classes={environment}")
    aggregate._write(run, today, *writes, *cut, ["d21-pilot", verdict, reason])
    return D21Report(verdict, reason)


def d21_replay(run, pairs: list[dict], today: date) -> str:
    """The pilot replay, in its own unit after the pilot's compile steps, none on the replay-unavailable branch: the
    aggregate over the clean members of the pilot's 30 built within D+14's 4-hour line, then replayed with --fresh
    under the cap in force. A rejection resolving to a member makes it rejected-by-replay (d21-pilot); one resolving
    to none stops. A replay killed under the cap is the re-scope, N = floor((cap - E) / m) with D+14's E and m: a
    replay that did not return gives no figure to recompute m from; run again, it finds that re-scope, or its kill,
    recorded and returns it. Returns what the replay did."""
    published, killed = run.consts.published, "the pilot replay was killed"
    if published["status"]["independent_check"] == "replay-unavailable":
        raise LedgerStop("no pilot replay runs on the replay-unavailable branch")
    aggregate._flush(run, today)
    if done := next((row[1] for row in gatefile.rows(run.pol)
                     if row[1] in ("rescope", "kill") and row[4].startswith(f"d21: {killed}")), None):
        return done
    found = aggregate.members(run.progress, pairs[:published["sampling"]["cut_n"] or None][:PAIRS], run.results)
    source, ranges = aggregate.text(run, found)
    aggregate.write_membership(run.results, list(ranges))
    built = aggregate.build(run, source, measure.BUILD_LINE_S, "pilot-")
    if built.exit or built.killed:
        raise LedgerStop(f"the pilot aggregate's build exited {built.exit} (killed {built.killed}); "
                         "see aggregate-pilot-build.log")
    cap = published["limits"]["replay_cap_s"]
    proc, constant = aggregate.replay(run, cap, "pilot-")
    if proc.killed:
        d14 = json.loads((run.pol.root / measure.DIR / "projection.json").read_text())
        verdict, cut = _rescope(run, aggregate._fit(cap - d14["E"], d14["m"]),
                                f"{killed} ({proc.killed}) under the cap of {cap} s")
        aggregate._write(run, today, *cut)
        return verdict
    if proc.exit == 0:
        return "returned"
    shas, failed = {leg["pair_id"]: leg["pair_sha256"] for leg in found}, []
    if not (member := constant and aggregate.attribute(constant, list(shas),
                                                      lambda c: aggregate._walk(run, c, failed, "pilot-"))):
        raise LedgerStop(f"the pilot replay's rejection resolves to no pair: {constant or 'no constant named'}; "
                         f"{'; '.join(failed)}")
    run.progress.remove({shas[member]: {"source": "d21-pilot", "constant": constant}}, "rejected-by-replay", today)
    return f"rejected {member}: {constant}"
