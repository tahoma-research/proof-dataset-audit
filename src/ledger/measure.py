"""The D+14 measurement: the serial pilot; the baseline aggregate, the header over the D+7 toy entry alone, and the
pilot aggregate, the toy and the clean pilot pairs, each built with `lake --no-cache build` and replayed to
completion with `leanchecker --fresh`, every figure recorded under measure/d14/; the projection and its one outcome,
computed from those files alone and published labelled extrapolated; and D+21's per-pair limit, from the same."""

import json
import math
import shutil
from datetime import date
from pathlib import Path

from ledger import REPO, aggregate, envbuild, gatefile, legs, preflight, probes
from ledger.types import LedgerStop, canonical, write_atomic

DIR = "measure/d14"
H = 3600
BUILD_LINE_S = 4 * H  # each aggregate build
REPLAY_LINE_S = 24 * H  # the baseline replay, the pilot replay and its one re-run together
CAP_S = 12 * H  # the replay cap until D+14 sets the one in force
NOISE = 0.05  # T - E within this share of E is run-to-run noise
FLOOR_S = 30 * 60  # the floor of the per-pair limit set from a pilot with no clean pair
TOY = REPO / "fixtures/toy/Toy/Entry.lean"
FIGURES = ("S", "M", "E", "T", "m", "P", "Eb", "Tb", "mb", "B", "cap_s", "N")
MEMORY = ("replay_memory_floor_mib", "leg_memory_max_mb", "agg_memory_max_mb")


def _proc(proc, **more) -> dict:
    return {"wall_s": round(proc.wall_s, 3), "exit": proc.exit, "killed": proc.killed, **more}


def _aggregate(run, name: str, members: list[dict], replay_s: float | None) -> dict:
    """Build the aggregate over `members` (pin leg results) and the toy within its 4-hour line, and audit it where
    it has members; then, given `replay_s` and a build that finished, replay it once within that, a rejection
    resolved to a member by the attribution rule (a walk that fails resolving none, its cause kept). Every call
    logs under `name`. Records measure/d14/<name>.json and returns it. A build that fails, or a build or replay
    killed for memory, stops: no outcome the PRD lists covers it."""
    ids, label = [leg["pair_id"] for leg in members], f"{name}-"
    aggregate.write_membership(run.results, ids)
    built = aggregate.build(run, aggregate.text(run, members)[0] + "\n" + TOY.read_text(), BUILD_LINE_S, label)
    if built.killed == "oom" or built.exit and not built.killed:
        raise LedgerStop(f"the {name} aggregate's build exited {built.exit} (killed {built.killed}); "
                         f"see aggregate-{label}build.log")
    found = {"members": ids, "build": _proc(built, peak_mem_kb=built.peak_mem_kb), "audit": None, "replay": None}
    if not built.killed and ids:
        audited = aggregate.audit(run, ids, BUILD_LINE_S, label)
        found["audit"] = _proc(audited, peak_mem_kb=audited.peak_mem_kb)
    if not built.killed and replay_s is not None:
        proc, constant = aggregate.replay(run, replay_s, label)
        if proc.killed == "oom":
            raise LedgerStop(f"the {name} aggregate's replay was killed for memory; see aggregate-{label}replay.log")
        rss, member, failed = legs.MAX_RSS.search(proc.output), None, []
        if proc.exit and not proc.killed and constant and ids:
            member = aggregate.attribute(constant, ids, lambda c: aggregate._walk(run, c, failed, label))
        found["replay"] = _proc(proc, max_rss_kb=rss and int(rss[1]), rejected_constant=constant, member=member,
                                walk_failed=failed)
    write_atomic(run.pol.root / DIR / f"{name}.json", canonical(found))
    return found


def _returned(replay: dict | None) -> bool:
    return replay is not None and replay["exit"] == 0 and not replay["killed"]


def _measure(run, pairs: list[dict], today: date) -> None:
    """Record every D+14 figure: the proof-1b timing, in proof1b.json, where proof 1b's replay cap and its D+21
    scheduling read it; the serial pilot's pairs attempted (its 25-hour line stops it); then the baseline, built and
    replayed first, then the pilot aggregate, unless no pilot pair compiled clean, replayed only after a baseline
    replay that returned clean, within what the baseline left of the 24-hour line. A pilot replay rejecting a member
    makes it rejected-by-replay (d14-pilot), and one re-run over the rest, where any remain, follows in what is left;
    a member that re-run rejects is removed the same way. Every file under measure/d14/ is this run's: an earlier
    run's are removed first."""
    if (out := run.pol.root / DIR).exists():
        shutil.rmtree(out)
    out.mkdir(parents=True)
    write_atomic(out / "proof1b.json", canonical({"timing_s": probes.d14_proof1b_timing(run.pol)}))
    legs.serial_pilot(run, pairs)
    attempted = set(run.progress.data["d14_pilot"]["attempted"])
    pilot = [pair for pair in pairs if pair["pair_sha256"] in attempted]
    results = [json.loads((run.results / run.progress.data["legs"][pair["pair_sha256"]]["pin"]["leg"]).read_text())
               for pair in pilot]
    write_atomic(out / "pairs.json", canonical([{
        "pair_id": leg["pair_id"], "outcome": leg["outcome"], "compile_s": leg["compile"] and leg["compile"]["wall_s"],
        "replay_s": leg["replay"] and leg["replay"]["wall_s"],
        "peak_mem_kb": max((leg[step]["peak_mem_kb"] for step in ("compile", "replay", "audit")
                            if leg[step] and leg[step]["peak_mem_kb"]), default=None)} for leg in results]))
    base = _aggregate(run, "baseline", [], REPLAY_LINE_S)
    left = REPLAY_LINE_S - base["replay"]["wall_s"] if _returned(base["replay"]) else None
    members = aggregate.members(run.progress, pilot, run.results)
    for name in ("pilot", "rerun"):
        if not members:
            return  # the pilot aggregate is the baseline, or its only member was rejected
        replay = _aggregate(run, name, members, left)["replay"]
        if not (replay and replay["member"]):
            return
        rejected = next(leg for leg in members if leg["pair_id"] == replay["member"])
        run.progress.remove({rejected["pair_sha256"]: {"source": "d14-pilot", "constant": replay["rejected_constant"]}},
                            "rejected-by-replay", today)
        members, left = [leg for leg in members if leg is not rejected], left - replay["wall_s"]


def project(d: Path, sample_size: int, ceiling_s: float) -> dict:
    """The projection (PRD § what verification means) from the files under `d` alone. M is the member count of the
    aggregate whose replay gave T, the re-run's where one ran, the toy not counted, and 0 where the pilot replay
    rejected its only member; E and T come only from replays that returned clean, a build killed at its line stands in
    at 4 hours, and with M = 0 m and mb are the slowest pilot pair's compile wall-clock, a stop where none has one. The
    outcome is the first that applies: replay-unavailable (a replay not returned, or a re-run that rejected a member
    again; a build at its line; a rejection resolving to no pair; 1.5 E + B over the ceiling), where a B over the
    ceiling cuts to the largest N whose B fits; the cap reset where 1.5 E exceeds 12 h, cut to
    N = floor((ceiling - E) / m) where P exceeds the ceiling; the re-scope where P exceeds 12 h,
    N = floor((12 h - E) / m); otherwise the default cap, the larger of 12 h and 1.5 P. No cap exceeds the ceiling, and
    a cut to no pair stops. The memory figures: the pilot replay's maximum resident set x 1.25, and 1.5 x the largest
    pilot leg peak and the pilot aggregate's larger build or audit peak, each in MiB. The marginal per-pair compile
    cost: the mean of the pilot pairs' serial compile wall-clocks."""
    def read(name: str) -> dict | None:
        return json.loads(path.read_text()) if (path := d / f"{name}.json").exists() else None
    pairs, base, first, rerun = map(read, ("pairs", "baseline", "pilot", "rerun"))
    builds = [a["build"] for a in (base, first, rerun) if a]
    replays = [a["replay"] for a in (base, first, rerun) if a and a["replay"]]
    pilot = rerun or (None if first and first["replay"] and first["replay"]["member"] else first)
    S, M = sample_size, len(pilot["members"]) if pilot else 0
    pilot = pilot or base
    Eb, Tb = (BUILD_LINE_S if a["build"]["killed"] else a["build"]["wall_s"] for a in (base, pilot))
    E, T = (a["replay"]["wall_s"] if _returned(a["replay"]) else None for a in (base, pilot))
    compiles = [p["compile_s"] for p in pairs if p["compile_s"] is not None]
    if M == 0:
        if not compiles:
            raise LedgerStop("M = 0 and no pilot pair has a compile wall-clock: m and mb have no figure")
        m = mb = max(compiles)
    else:
        mb = max(0, (Tb - Eb) / M)
        m = None if None in (E, T) else 0 if abs(T - E) <= NOISE * E else max(0, (T - E) / M)
    P = None if None in (E, m) else E + m * S
    B = 1.5 * (Eb + mb * S)
    rejection = next((r for r in replays if r["exit"] and not r["killed"] and not r["member"]), None)
    unavailable = [why for applies, why in (
        (any(r["killed"] for r in replays), "a replay did not return inside the 24-hour line"),
        (bool(rerun and rerun["replay"] and rerun["replay"]["member"]), "the pilot re-run rejected a member"),
        (any(b["killed"] for b in builds), "an aggregate build reached its 4-hour line"),
        (rejection is not None, "a replay rejection resolving to no pair"),
        (E is not None and 1.5 * E + B > ceiling_s, "1.5 E + B exceeds the run ceiling")) if applies]
    N, cap, rule = None, None, None
    if unavailable:
        outcome, why = "replay-unavailable", unavailable[0]
        if B > ceiling_s:
            N = aggregate._fit(ceiling_s / 1.5 - Eb, mb)
    elif 1.5 * E > CAP_S:
        outcome, why, rule = "cap-reset", "1.5 E exceeds the 12-hour cap", "reset"
        if P > ceiling_s:
            N = math.floor((ceiling_s - E) / m)
        cap = min(1.5 * (E + m * (S if N is None else N)), ceiling_s)
    elif P > CAP_S:
        outcome, why, rule = "rescope", "P exceeds the 12-hour cap", "rescope"
        N = math.floor((CAP_S - E) / m)
        cap = min(max(CAP_S, 1.5 * (E + m * N)), ceiling_s)
    else:
        outcome, why, rule = "default", "P fits the 12-hour cap", "max(12h,1.5P)"
        cap = min(max(CAP_S, 1.5 * P), ceiling_s)
    if N is not None and N < 1:
        raise LedgerStop(f"{outcome}: no cut fits, N={N}")
    rss = pilot["replay"] and pilot["replay"]["max_rss_kb"]
    legs_kb = max((p["peak_mem_kb"] for p in pairs if p["peak_mem_kb"]), default=None)
    agg_kb = max((a["peak_mem_kb"] for a in (pilot["build"], pilot["audit"]) if a and a["peak_mem_kb"]), default=None)
    return {"label": "extrapolated", "S": S, "M": M, "E": E, "T": T, "m": m, "P": P, "Eb": Eb, "Tb": Tb, "mb": mb,
            "B": B, "outcome": outcome, "reason": why, "cap_s": cap and round(cap), "rule": rule, "N": N,
            "constant": rejection and (rejection["rejected_constant"] or "none named"),
            "replay_memory_floor_mib": rss and math.ceil(1.25 * rss / 1024),
            "leg_memory_max_mb": legs_kb and math.ceil(1.5 * legs_kb / 1024),
            "agg_memory_max_mb": agg_kb and math.ceil(1.5 * agg_kb / 1024),
            "mean_compile_s": sum(compiles) / len(compiles) if compiles else None}


def record(pol, consts, d14: dict, today: date) -> None:
    """Write what the outcome sets: the published constants first (the independent check's status; the cap in force
    and its rule, unless replay-unavailable; a cut's cut_n; each memory figure measured), then the projection beside
    the measurements; then the gate lines: a cut's rescope line, exactly one d14-outcome line carrying the outcome,
    its reason, a rejection's constant and every figure, labelled extrapolated, and the d14 line, met."""
    unavailable = d14["outcome"] == "replay-unavailable"
    sets = {"independent_check": '"replay-unavailable"' if unavailable else '"available"',
            "replay_cap_s": None if unavailable else d14["cap_s"],
            "replay_cap_rule": None if unavailable else f'"{d14["rule"]}"', "cut_n": d14["N"]} | {
        key: d14[key] for key in MEMORY}
    for key, value in sets.items():
        if value is not None:
            envbuild.set_constant(consts, key, str(value))
    write_atomic(pol.root / DIR / "projection.json", canonical(d14))
    figures = "; ".join(f"{key}={'none' if d14[key] is None else round(d14[key], 1)}" for key in FIGURES)
    constant = f"constant={gatefile.sanitize(pol, d14['constant'], 100)}; " if d14["constant"] else ""
    if d14["N"]:
        gatefile.append(pol, "rescope", f"cut_n={d14['N']}", "pipeline", f"d14: {d14['outcome']}; {figures}", today)
    gatefile.append(pol, "d14-outcome", d14["outcome"], "pipeline",
                    f"extrapolated: {d14['reason']}; {constant}{figures}", today)
    gatefile.append(pol, "d14", "met", "pipeline", f"outcome={d14['outcome']}", today)


def d14(pol, consts, work: Path, results: Path, logs: Path, today: date) -> dict:
    """PRD § D+14 over the draw assembled in `work`: the preflight; the legacy environment's two probes, each unless
    its line is recorded (the cache probe fetches env/legacy afresh, which must never undo its build); then, in a pin
    run over `results`, every figure measured and recorded, the projection computed from those records and its
    outcome written. Refuses once the outcome is recorded: it is written once. Any other end without the outcome
    writes the d14 line unmet, with its cause. Returns the projection."""
    if "d14-outcome" in (recorded := {row[1] for row in gatefile.rows(pol)}):
        raise LedgerStop("the d14-outcome line is recorded: the D+14 measurement has run")
    try:
        preflight.check(pol, consts)
        if "legacy-cache-probe" not in recorded:
            probes.d14_cache_probe(pol, consts, logs)
        if "legacy-collector" not in recorded:
            probes.d14_legacy_collector(pol, consts, logs)
        run = legs.prepare(pol, consts, work, results, logs, ("pin",))
        _measure(run, [json.loads(line) for line in (work / "assembled.jsonl").read_text().splitlines()], today)
        found = project(pol.root / DIR, consts.published["sampling"]["sample_size"],
                        consts.published["limits"]["run_ceiling_s"])
        record(pol, consts, found, today)
    except BaseException as stop:
        gatefile.append(pol, "d14", "unmet", "pipeline",
                        f"{type(stop).__name__}: {gatefile.sanitize(pol, str(stop), 300)}", today)
        raise
    return found


def frozen_limit(d: Path) -> tuple[int, str]:
    """D+21's per-pair limit from the pilot pairs under `d`: 5 x the slowest compile or replay wall-clock of one
    that compiled clean; with none clean, 5 x the slowest of any outcome, at least 30 minutes. With the rule used."""
    if not (pairs := json.loads((d / "pairs.json").read_text())):
        raise LedgerStop("no D+14 pilot pair is recorded: the per-pair limit has no figure")
    clean = [p for p in pairs if p["outcome"] in aggregate.CLEAN]
    slowest = math.ceil(5 * max(max(p["compile_s"] or 0, p["replay_s"] or 0) for p in clean or pairs))
    return (slowest, "5x-slowest-clean") if clean else (max(FLOOR_S, slowest), "5x-slowest-any-floor-30min")
