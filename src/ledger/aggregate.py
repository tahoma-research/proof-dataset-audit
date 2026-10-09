"""The aggregate, the independent check: the declaration text of every pair that compiled cleanly in pass 1,
concatenated under one copy of the header, built with `lake build` and replayed once with `leanchecker --fresh`;
the rule that attributes a rejection to a member; and the D+44 check that runs them, one state step a night
after the D+43 cut, from the state the progress file records."""

import hashlib
import json
import math
import os
import re
import shutil
import stat
import time
from datetime import date
from functools import partial
from pathlib import Path

from ledger import REPO, confine, crosspass, devoverlay, diagnostics, envbuild, gatefile, ingest
from ledger.legs import MAX_RSS, REJECTED
from ledger.types import LedgerStop, write_atomic

CLEAN = {"accepted", "accepted-env-axiom"}  # pin outcomes of a pair that compiled cleanly
DONE = {"replay-returned", "replay-unavailable"}  # after these the check does no further work
REBUILD = {"build-pending", "rejected-rerun-pending"}
RERUNS = 2  # rebuild-and-replay re-runs, of either cause
# Lake's form of an error in the module. Member code can print such a line too: neither `lean --json` nor Lake's log
# gives a channel it cannot write (probed at v4.34.0), so a member can frame others into harness-error, or with a line
# outside every member put the run over the cap: the re-scope, then the kill.
ERROR = re.compile(r"^error: Aggregate\.lean:(\d+):\d+: .*", re.M)
PRIVATE = re.compile(r"^_private\.(?:[^.]+\.)*?\d+\.")  # _private.<module>.<n>.
FRESH = "replaying Aggregate with --fresh"
BUILD = ".lake/build"  # the pin project's build output, which the aggregate's build may write


def members(progress, pairs: list[dict], results) -> list[dict]:
    """The pin leg results, in the order of `pairs`, of the pairs that compiled cleanly in pass 1 (a terminal pin
    leg accepted or accepted-env-axiom) and carry no replay or harness override since."""
    overridden = progress.data.get("replay_overrides", {}).keys() | progress.data.get("harness_overrides", {}).keys()
    found = []
    for pair in pairs:
        leg = progress.data["legs"].get(pair["pair_sha256"], {}).get("pin", {})
        if leg.get("terminal") and pair["pair_sha256"] not in overridden:
            result = json.loads((results / leg["leg"]).read_text())
            if result["outcome"] in CLEAN:
                found.append(result)
    return found


def assemble(texts: list[tuple[str, str]], header: str) -> tuple[str, dict[str, tuple[int, int]]]:
    """The aggregate's text from (pair_id, pair text) in order: `header` once, then each pair text less that header,
    one blank line between members; and each member's first and last line, counted from 1. Stops unless every
    pair text starts with the header byte for byte and declares its own pair, no name comes twice, and no line
    below the header imports anything: a second header, or an import of a pair module, would put declarations
    behind an import boundary."""
    body, ranges, last = [], {}, header.count("\n")
    for pair_id, text in texts:
        decl = text.removeprefix(header)
        if decl == text:
            raise LedgerStop(f"{pair_id}: its text does not start with the aggregate's header")
        if (found := ingest.DECL.search(decl)) is None or found[1] != pair_id:
            raise LedgerStop(f"{pair_id}: its text does not declare {pair_id}")
        first = last + (2 if body else 1)
        last = first + decl.count("\n") - 1
        ranges[pair_id] = (first, last)
        body.append(decl)
    if len(ranges) != len(texts):
        raise LedgerStop("the aggregate's declaration names are not unique")
    if re.search(r"^import\b", "\n".join(body), re.M):
        raise LedgerStop("a line below the aggregate's header is an import")
    return header + "\n".join(body), ranges


def text(run, legs: list[dict]) -> tuple[str, dict[str, tuple[int, int]]]:
    """assemble over `legs`, pin leg results in order, their pair texts under the header, the development overlay's
    where one is in force."""
    overlay = devoverlay.load(run.pol)
    return assemble([(leg["pair_id"], (run.work / "pairs" / f"{leg['pair_id']}.lean").read_text()) for leg in legs],
                    overlay.header if overlay else run.consts.published["assembly"]["header"])


def write_membership(results: Path, names: list[str]) -> str:
    """results/membership.txt, the members' pair_ids in order under a line with their count and the sha256 of the
    list, which is returned."""
    listed = "".join(f"{pair_id}\n" for pair_id in names)
    digest = hashlib.sha256(listed.encode()).hexdigest()
    write_atomic(results / "membership.txt", f"# members={len(names)} sha256={digest}\n{listed}".encode())
    return digest


def attribute(constant: str, names: list[str], walk) -> str | None:
    """The member a rejected constant belongs to: with any _private.<module>.<n>. prefix stripped, the member whose
    name it is or extends by whole components, the longest (so _proof_N and its kin go to their parent);
    otherwise `walk(constant)`, the nearest member in the aggregate's dependency graph. None, a harness error of
    the run, when neither resolves it."""
    name = PRIVATE.sub("", constant)
    owners = [m for m in names if name == m or name.startswith(m + ".")]
    return max(owners, key=len) if owners else walk(constant)


def _lake(run, label: str, *args: str, writes: list, timeout_s: float, memory_max_mb: int | None):
    """`lake --no-cache <args>` in the pin's tree (the stop-loss's once that is in force), confined and bounded as
    proof code is: no file's metadata changed, nothing read but the toolchain, the tree, the audit executable and the
    membership file the walk reads."""
    tree = run.trees["pin"]
    path = run.pol.root / "env" / tree.name
    call = envbuild.lake(run.pol, run.consts, tree.name, tree.toolchain, path, *args)
    return confine.run(**call | {"writes": writes, "timeout_s": timeout_s}, memory_max_mb=memory_max_mb, no_meta=True,
                       reads=[tree.toolchain, path, tree.audit, run.results / "membership.txt"],
                       unit_name=confine.scope_name(run.pol.root, f"aggregate-{label}"),
                       log=run.logs / f"aggregate-{label}.log")


def _recorded(pol, gate: str) -> bool:
    return any(row[1] == gate for row in gatefile.rows(pol))


def _kill(run, verdict: str, cause: str) -> list:
    """The kill line, with the check's state as it stands."""
    agg = run.progress.aggregate()
    return ["kill", verdict, f"{cause}; state={agg['state']}; reruns_used={agg['reruns_used']}; "
                             f"extension={agg['extension']}"]


def _flush(run, today: date) -> int | None:
    """Make the writes the progress file holds pending, in order: cut_n, then each gate line unless a line of its gate
    (rescope, kill or d43, each written once) is recorded; then clear them. Returns the cut_n written. A decision is
    saved with its writes before any is made, and the gate lines come last, so the writes a run that died left
    unmade are the next night's first."""
    cut, pending = None, run.progress.aggregate().get("pending")
    for gate, verdict, reason in pending or ():
        if gate == "cut_n":
            envbuild.set_constant(run.consts, "cut_n", str(cut := verdict))
        elif not _recorded(run.pol, gate):
            gatefile.append(run.pol, gate, verdict, "pipeline", reason, today)
    if pending:
        run.progress.note(pending=[])
    return cut


def _write(run, today: date, *lines: list) -> None:
    run.progress.note(pending=list(lines))
    _flush(run, today)


def _fit(room: float, per_pair: float) -> int:
    """The most pairs whose cost at `per_pair` each fits `room`; 0 where a pair costs nothing, as no cut shortens
    that."""
    return math.floor(room / per_pair) if per_pair else 0


def _over_cap(run, cause: str, today: date, n: int | None, members: int, sample: int) -> None:
    """Over the cap (PRD § D+44): the kill where no cut is made (no `n`: the date-free command's check), the re-scope
    is spent or no re-run remains, or where `n`, the pair count this measurement supports (05 § aggregate), is below
    1. Otherwise the cut to the first `n` pairs of the draw, saved with its transition, then written to cut_n and as
    the re-scope, which the next re-run carries out as one of the two; an `n` not below the `members` built keeps
    every pair, cut_n the `sample`'s length: one retry, as the line says."""
    if n is None or _recorded(run.pol, "rescope") or run.progress.aggregate()["reruns_used"] >= RERUNS:
        return _write(run, today, _kill(run, "over the cap", cause))
    if n < 1:
        return _write(run, today, _kill(run, "over the cap, no cut fits", f"{cause}; N={n}"))
    cut = n if n < members else sample
    retry = f"; N={n} is not below the {members} members: every pair kept, one retry" if n >= members else ""
    run.progress.transition("cut", pending=[["cut_n", cut, ""], ["rescope", f"cut_n={cut}", f"d44: {cause}{retry}"]])
    _flush(run, today)


def _remove(run, faults: dict, cause: str, event: str, today: date, spend: bool = False) -> None:
    """Remove each member in `faults`, digest -> its override, with `cause`, and in the same save move to the
    re-run over the rest, spending the extension with `spend`; with no re-run left the removal stands, saved with
    the kill of the third re-run needed, which follows it."""
    if run.progress.aggregate()["reruns_used"] >= RERUNS:
        run.progress.remove(faults, cause, today, pending=[_kill(run, "over the cap", "a third re-run needed")])
        _flush(run, today)
        return
    run.progress.remove(faults, cause, today, event, spend=spend)


def _seen(path: Path) -> tuple:
    """An entry's identity, never read or followed: its inode and mode, and but for a directory, whose own size and
    ctime move with the entries in it (each listed in its own right), its size and ctime, which every write moves."""
    s = path.lstat()
    return (s.st_ino, s.st_mode) + (() if stat.S_ISDIR(s.st_mode) else (s.st_size, s.st_ctime_ns))


def _entries(top: Path, known: dict | None = None) -> dict[str, tuple | None]:
    """Each entry under `top`, the build's tree, by its path from `top`, with what `_seen` makes of it. With
    `known`, a listing from before the build, an entry not in it is listed as None, never read or descended into:
    a member may have planted it."""
    found = {}
    for d, dirs, files in os.walk(top):
        for name in dirs + files:
            rel = os.path.relpath(os.path.join(d, name), top)
            found[rel] = None if known is not None and rel not in known else _seen(Path(d, name))
        dirs[:] = [name for name in dirs if found[os.path.relpath(os.path.join(d, name), top)] is not None]
    return found


def _unlock(function, path: str, error: OSError) -> None:
    """shutil.rmtree's handler: a directory the build left unlistable to its owner is opened to it and removed;
    any other failure stands."""
    if not stat.S_ISDIR(os.lstat(path).st_mode):
        raise error
    os.chmod(path, 0o700)
    shutil.rmtree(path, onexc=_unlock)


def build(run, source: str, budget_s: float, label: str = ""):
    """Write `source` as Aggregate.lean, the pin project's library, and build it with `lake --no-cache build
    Aggregate` under `budget_s` and agg_memory_max_mb; the build, which elaborates the members' code, writes only
    the project's build output and the run's tmp/<run-id>/. `label`, here and in audit, replay and the walk,
    prefixes the call's step in its log's name, so the aggregates of one run keep apart."""
    tree = run.pol.root / "env" / run.trees["pin"].name
    write_atomic(tree / "Aggregate.lean", source.encode())
    return _lake(run, f"{label}build", "build", "Aggregate", writes=[tree / BUILD, envbuild.run_tmp(run.pol.root)],
                 timeout_s=budget_s, memory_max_mb=run.consts.published["limits"]["agg_memory_max_mb"])


def audit(run, names: list[str], timeout_s: float, label: str = ""):
    """`ledger-audit audit` over the built aggregate's members `names`, in one call, under agg_memory_max_mb."""
    return _lake(run, f"{label}audit", "env", str(run.trees["pin"].audit), "audit", "--skip-missing", "--module",
                 "Aggregate", *(arg for pair_id in names for arg in ("--decl", pair_id)), writes=[],
                 timeout_s=timeout_s, memory_max_mb=run.consts.published["limits"]["agg_memory_max_mb"])


def replay(run, cap_s: float, label: str = ""):
    """`leanchecker -v --fresh Aggregate`, one single-threaded process under /usr/bin/time -v, killed at `cap_s`,
    its memory capped at the replay floor D+14 sets, and until then at agg_memory_max_mb; and the constant it
    rejected, if it names one. Stops on a replay that exits 0 without the line saying it replayed the aggregate
    with --fresh."""
    limits = run.consts.published["limits"]
    proc = _lake(run, f"{label}replay", "env", "/usr/bin/time", "-v", "leanchecker", "-v", "--fresh", "Aggregate",
                 writes=[], timeout_s=cap_s,
                 memory_max_mb=limits["replay_memory_floor_mib"] or limits["agg_memory_max_mb"])
    if proc.exit == 0 and not proc.killed and FRESH not in proc.output:
        raise LedgerStop(f"the replay exited 0 without the line {FRESH!r}; see aggregate-{label}replay.log")
    return proc, (found := REJECTED.search(proc.output)) and found[1]


def _build(run, pairs: list[dict], today: date, deadline: float, eb_s: float | None = None, mb_s: float | None = None,
           override: str = "crosspass-d44") -> str | None:
    """Build the aggregate over the current members, budgeted at B = 1.5 (Eb + mb M) with D+14's figures, and without
    them, in the date-free command, at what remains before `deadline`, the run's ceiling; then compare every member's
    observables with its pass-1 audit. A new entry the build left under .lake/build beyond the aggregate's own
    outputs is removed and recorded; an existing entry there changed, one added under the pass-1 outputs in Pairs/
    or a planted one that cannot be removed leaves a tree that is not the one verified, and is the kill outright.
    Each member holding an elaboration error, missing from the built aggregate or disagreeing is removed as
    harness-error, its detail the error's first KiB, a disagreement's override from the source `override`. Over the
    cap, where the cut is the most pairs whose B fits the ceiling, and without D+14's figures the kill: the budget or a
    memory cap passed; a failure whose output was cut short, naming no line or with an error outside every member; an
    aggregate audit killed or failing. Otherwise the aggregate is built, and the event that says so is returned:
    built, or built-unavailable on that branch."""
    root, found, limits = run.pol.root, members(run.progress, pairs, run.results), run.consts.published["limits"]
    source, ranges = text(run, found)
    digest = write_membership(run.results, list(ranges))
    tree = root / "env" / run.trees["pin"].name
    lib = re.escape(str(Path(run.trees["pin"].out).relative_to(BUILD)))  # the pin's modules, under .lake/build
    own = re.compile(rf"ir/Aggregate\.(?:c|c\.hash|setup\.json)|{lib}/Aggregate\.(?:[oi]lean|[oi]lean\.hash|trace)")
    (tree / BUILD / "ir").mkdir(exist_ok=True)  # Lake's, made here so that what the build puts in it is listed
    budget, n = ((deadline - time.monotonic(), None) if eb_s is None else
                 (1.5 * (eb_s + mb_s * len(ranges)), _fit(limits["run_ceiling_s"] / 1.5 - eb_s, mb_s)))
    before = _entries(tree / BUILD)
    over = partial(_over_cap, run, today=today, n=n, members=len(ranges), sample=len(pairs))
    built = build(run, source, budget)
    after = _entries(tree / BUILD, before)
    planted = sorted(rel for rel, seen in after.items() if seen is None and not own.fullmatch(rel))
    run.progress.note(membership_sha256=f"sha256:{digest}", last_build={
        "wall_s": round(built.wall_s, 3), "exit": built.exit, "planted": planted[:20], "planted_count": len(planted)})
    try:
        for path in map((tree / BUILD).joinpath, planted):
            path.unlink() if path.is_symlink() or not path.is_dir() else shutil.rmtree(path, onexc=_unlock)
    except (OSError, RecursionError):  # RecursionError: nested deeper than rmtree recurses
        return _write(run, today, _kill(run, "build tree changed",
                                        "an entry the build planted under .lake/build could not be removed"))
    if (any(after.get(rel) != seen for rel, seen in before.items() if not own.fullmatch(rel))
            or any(re.match(rf"{lib}/Pairs/", rel) for rel in planted)):
        return _write(run, today, _kill(run, "build tree changed",
                                        "the build changed an existing entry or Pairs/ under .lake/build"))
    if built.killed:
        return over(f"the build passed its budget of {budget:.0f} s" if built.killed == "wall-clock" else
                    f"the build passed its memory cap ({built.killed})")
    if built.exit != 0:
        if built.output_truncated:
            return over("build output truncated")
        errors = [(int(found[1]), found[0]) for found in ERROR.finditer(built.output)]
        owner = {n: next((pair_id for pair_id, (a, b) in ranges.items() if a <= n <= b), None) for n, _ in errors}
        if not errors or None in owner.values():
            return over("a build error outside every member")
        shas = {leg["pair_id"]: leg["pair_sha256"] for leg in found}
        faults = {}
        for n, line in errors:
            detail = diagnostics.rewrite_paths(line, [tree, root, REPO])[0].encode()[:1024].decode(errors="ignore")
            faults.setdefault(shas[owner[n]], {"source": "aggregate-elab", "detail": detail})
        return _remove(run, faults, "harness-error", "removed", today)
    audited = audit(run, list(ranges), deadline - time.monotonic())
    if audited.killed or audited.exit != 0:
        return over(f"the aggregate's audit was killed ({audited.killed})" if audited.killed else
                    f"the aggregate's audit exited {audited.exit}")
    decls = [json.loads(line) for line in audited.output.splitlines() if line.startswith("{")]
    faults = {leg["pair_sha256"]: {"source": override, "detail": ", ".join(differs)} for leg in found
              if (differs := crosspass.compare(leg["pair_id"], leg["audit"]["decls"], decls))}
    if faults:
        return _remove(run, faults, "harness-error", "removed", today)
    unavailable = run.consts.published["status"]["independent_check"] == "replay-unavailable"
    return "built-unavailable" if unavailable else "built"


def _walk(run, constant: str, failed: list[str], label: str = "") -> str | None:
    """`ledger-audit walk` over the built aggregate: the member nearest the constant, if exactly one is; none where
    the walk passes its time or memory cap or fails, which it adds to `failed`."""
    limits = run.consts.published["limits"]
    walked = _lake(run, f"{label}walk", "env", str(run.trees["pin"].audit), "walk", "--module", "Aggregate",
                   "--constant", constant, "--members-file", str(run.results / "membership.txt"), writes=[],
                   timeout_s=limits["per_pair_wall_clock_s"], memory_max_mb=limits["agg_memory_max_mb"])
    if walked.killed or walked.exit != 0:
        failed.append(f"the dependency walk was killed ({walked.killed})" if walked.killed else
                      f"the dependency walk exited {walked.exit}")
        return None
    return json.loads(walked.output.splitlines()[-1])["member"]


def _replay(run, pairs: list[dict], today: date, e_s: float | None = None, m_s: float | None = None,
            spend: bool = False, source: str = "d44") -> None:
    """The replay, once, under the cap in force, its state replay-running while it runs. Returned:
    replay-returned. A rejection resolving to a member: that member is rejected-by-replay and removed, its override
    from `source`, and with `spend`, the D+46 run's, that spends the extension, in the same save. Killed, failed
    naming no constant, or rejecting a constant that resolves to no member (a walk that fails among the causes): over
    the cap, where the cut is N = floor((cap - E) / m) with D+14's E and m, since a replay over the cap never returned
    clean to recompute m from, and without them, in the date-free command, the kill; a constant named in its gate
    lines is sanitized."""
    cap = run.consts.published["limits"]["replay_cap_s"]
    supported = None if e_s is None else _fit(cap - e_s, m_s)
    shas = {leg["pair_id"]: leg["pair_sha256"] for leg in members(run.progress, pairs, run.results)}
    run.progress.transition("started")
    proc, constant = replay(run, cap)
    rss = MAX_RSS.search(proc.output)
    run.progress.note(last_replay={"wall_s": round(proc.wall_s, 3), "exit": proc.exit, "rejected_constant": constant,
                                   "max_rss_kb": rss and int(rss[1])})
    if proc.killed:
        return _over_cap(run, f"the replay was killed ({proc.killed}) under the cap of {cap} s", today, supported,
                         len(shas), len(pairs))
    if proc.exit == 0:
        return run.progress.transition("returned")
    failed = []
    member = constant and attribute(constant, list(shas), lambda c: _walk(run, c, failed))
    if not member:
        named = gatefile.sanitize(run.pol, constant, 200) if constant else "no constant named"
        return _over_cap(run, "; ".join([f"a rejection resolving to no pair: {named}", *failed]), today, supported,
                         len(shas), len(pairs))
    _remove(run, {shas[member]: {"source": source, "constant": constant}}, "rejected-by-replay", "rejected", today,
            spend=spend)


def d43_cut(run, pairs: list[dict], today: date) -> list[dict]:
    """PRD § D+43, computed once by the D+44 run before it reads the check's state: with pass 1 short of the
    sample (a required leg not terminal), the sample is cut to the longest prefix of the draw in which every pair
    is complete, written to cut_n and as the single re-scope; where a rescope line is already recorded, that is
    the kill, as is a cut to no pair. Writes the d43 line last, after the decision and its writes are saved
    together. Returns the pairs that remain."""
    consts, pol = run.consts, run.pol
    pairs = pairs[:consts.published["sampling"]["cut_n"] or None]
    required = ["pin"] if consts.published["status"]["legacy"] == "environment-unavailable" else ["pin", "legacy"]
    short = run.progress.pending_pairs(pairs, required)
    n = pairs.index(short[0][0]) if short else len(pairs)
    reason = f"complete_prefix={n}; sample={len(pairs)}"
    if not short:
        lines = [["d43", "met", reason]]
    elif _recorded(pol, "rescope"):
        lines = [_kill(run, "d43: pass 1 short and the re-scope spent", reason), ["d43", "kill", reason]]
    elif n == 0:
        lines = [_kill(run, "d43: no pair complete at the head of the draw", reason), ["d43", "kill", reason]]
    else:
        lines = [["cut_n", n, ""], ["rescope", f"cut_n={n}", f"d43: pass 1 short; {reason}"], ["d43", "cut", reason]]
        pairs = pairs[:n]
    run.progress.cut_written(lines)
    _flush(run, today)
    return pairs


def step(run, pairs: list[dict], today: date, eb_s: float, mb_s: float, e_s: float, m_s: float) -> str:
    """One night of the D+44 check (PRD § D+44) for `run`, legs.prepare's over the pin, and `pairs` in draw order;
    `eb_s` and `mb_s` are D+14's baseline build wall-clock and per-member build cost, `e_s` and `m_s` its baseline
    replay wall-clock and per-member replay cost. Returns the state it leaves. Refuses before D+44. The writes a run
    that died left pending come first, then the D+43 cut, once. Nothing follows once the check is done or the run
    killed, nor after D+47, nor on D+47 unless the D+46 run spent the extension. A replay left running by a run that
    died is pending again. Then the one step the state calls for: a build and the cross-pass comparison, then the
    replay only if the cap fits what remains of the ceiling (a re-run a member rejection drove spends the extension
    on D+46, with its transition, when it does not); or the replay, which always starts. A night that leaves no
    returned replay and no later working night, D+47 or D+46 with the extension unspent, is the kill."""
    limits, prog = run.consts.published["limits"], run.progress
    deadline = time.monotonic() + limits["run_ceiling_s"]
    day = (today - gatefile.d0(run.pol)).days
    if day < 44:
        raise LedgerStop(f"the D+44 check does not run before D+44 (D+{day})")
    cut = _flush(run, today) or run.consts.published["sampling"]["cut_n"]
    pairs = pairs[:cut or None] if prog.data.get("d44_cut_written") else d43_cut(run, pairs, today)
    agg = prog.aggregate()
    if agg["state"] in DONE or _recorded(run.pol, "kill"):
        return agg["state"]
    if day > 47 or day == 47 and agg["extension"] != "spent":
        _write(run, today, _kill(run, "replay not returned by D+47", f"D+{day}"))
        return agg["state"]
    if agg["state"] == "replay-running":
        prog.transition("resumed")
    replay = agg["state"] == "replay-pending"
    if agg["state"] in REBUILD:
        driven = agg["state"] == "rejected-rerun-pending"
        built = _build(run, pairs, today, deadline, eb_s, mb_s)
        replay = built == "built" and time.monotonic() + limits["replay_cap_s"] <= deadline
        if built:
            prog.transition(built, spend=built == "built" and not replay and day == 46 and driven)
    if replay:
        _replay(run, pairs, today, e_s, m_s, spend=day == 46)
    if (day == 47 or day == 46 and agg["extension"] != "spent") and agg["state"] not in DONE and not _recorded(
            run.pol, "kill"):
        _write(run, today, _kill(run, "replay not returned by D+47", "no re-run in progress"))
    return agg["state"]


def check(run, pairs: list[dict], today: date) -> None:
    """The D+44 check without its day rules, for the date-free command: from the state the progress file records, the
    build and its cross-pass comparison, then the replay, again over the remainder after each removal, until the
    replay returns (on the replay-unavailable branch, the build alone) or a kill is recorded, all within one run
    ceiling. No build or replay is cut short to fit a night, and over the cap is the kill, never a cut."""
    deadline = time.monotonic() + run.consts.published["limits"]["run_ceiling_s"]
    while (state := run.progress.aggregate()["state"]) not in DONE and not _recorded(run.pol, "kill"):
        if state not in REBUILD:
            _replay(run, pairs, today)
        elif built := _build(run, pairs, today, deadline):
            run.progress.transition(built)
