"""Honesty-proof fixtures, each run through the same ingest, assembly, legs, decision table and aggregate code a real
run uses. Proofs 1, 2, 3 and 3b: planted entries, each of a known class, run in both environments in a fixture run of
their own, whose aggregate is built for the cross-pass check; with them, the assembler fixture set's elaboration
agreement. Proof 1b: a constant added without the kernel's check, planted in the core-only fixture project ahead of
the theorem whose proof uses it, must be caught by the independent check and attributed."""

import contextlib
import dataclasses
import json
import os
import shutil
import time
from dataclasses import dataclass
from datetime import date
from pathlib import Path

from ledger import REPO, aggregate, assemble, classify, constants, devoverlay, ingest, legs, progress, records
from ledger.types import LedgerStop, canonical, write_atomic

HEADER = "import Lean.Elab.Term\n"  # the fixture project's own header: the Lean core module its plant needs
PLANTED, VICTIM = "planted_false", "victim__p0"  # the fixture's unchecked constant, and the pair whose proof uses it
# Each planted pair: its proof, its pin leg's outcome, and its class with the legacy environment standing and with it
# unavailable, where proofs 1 and 2 reduce and proof 3's mismatch entry is not introduced (None).
EXPECTED = {
    "planted_kernel__p0": ("1", "kernel-reject", "rejected-by-checker", "environment-undeclared"),
    "planted_axiom__p0": ("2", "audit-failure", "axiom-audit-failure", "environment-undeclared"),
    "planted_sorry__p0": ("2", "audit-failure", "axiom-audit-failure", "environment-undeclared"),
    "planted_behind__p0": ("2", "audit-failure", "axiom-audit-failure", "environment-undeclared"),
    "planted_mismatch__p0": ("3", "elab-error", "environment-mismatch", None),
    "planted_undeclared__p0": ("3", "elab-error", "environment-undeclared", "environment-undeclared"),
    "planted_leak__p0": ("3b", "accepted", "reproduced", "reproduced"),  # leaks a local instance forward
    "#7__p0": ("3b", "harness", "harness-error", "harness-error"),  # the name collision with planted_leak
    "planted_victim__p0": ("3b", "accepted", "harness-error", "harness-error"),  # changed by the leak
}
UNDECLARED = "planted_undeclared"  # the entry that declares no revision
LEAK = "synthetic_scope_leak.jsonl"  # the assembler fixture built to leak a local instance into the members after it


@dataclass(frozen=True)
class Proof1bReport:
    passed: bool
    evidence: str  # what each run found
    classes: tuple[str, ...] = ()  # the victim's, in each run


@dataclass(frozen=True)
class FixtureReport:
    verdicts: dict[str, tuple[bool, str]]  # gate (d21-proof-1, -2, -3, -3b) -> passed, and the evidence
    reduced: bool  # the legacy environment is unavailable: proofs 1, 2 and 3 ran in their reduced forms


def _fresh(path: Path) -> Path:
    if path.exists():
        shutil.rmtree(path)
    path.mkdir(parents=True)
    return path


def _assemble(entries, assembly: dict, work: Path) -> list[dict]:
    """Pair 0 of each entry, in the order given, assembled into work/pairs/ under `assembly` as `assemble` writes it,
    an entry refused at ingest named by its position as the draw names it; work/sample.json, whose digest keys the
    progress file, lists them. Returns the pairs, each line both the draw's and the assembler's."""
    (work / "pairs").mkdir(parents=True)
    pairs = []
    for i, entry in enumerate(entries):
        row = {"i": i, "decl": entry.decl, "k": 0, "position": entry.position, "split": entry.split,
               "pair_id": assembly["name_mangle"].format(decl=f"#{entry.position}" if entry.refusal else entry.decl,
                                                         k=0), "element_sha256": entry.element_sha256[0]}
        made = assemble.assemble_pair(row, entry, assembly)
        if made.text is not None:
            write_atomic(work / "pairs" / f"{made.pair_id}.lean", made.text.encode())
        pairs.append(row | {"pair_sha256": made.pair_sha256, "refusal": made.refusal})
    write_atomic(work / "sample.json", canonical(pairs))
    return pairs


def _check(run: legs.Run, pairs: list[dict], today: date, timing_s: float) -> tuple[list[str], str, str | None]:
    """The D+44 check's own build and replay of the aggregate over the run's members, with no per-member cost, so
    that over the cap is the kill in the fixture's gate file, never a cut; a member a rejection resolves to is removed
    with its override from the d21-proof-1b source. Returns the members built over, the state the check is left in,
    and the constant its last replay rejected."""
    built = [leg["pair_id"] for leg in aggregate.members(run.progress, pairs, run.results)]
    cap = run.consts.published["limits"]["replay_cap_s"]
    if aggregate._build(run, pairs, today, time.monotonic() + cap, timing_s, 0) == "built":
        run.progress.transition("built")
        aggregate._replay(run, pairs, today, timing_s, 0, source="d21-proof-1b")
    agg = run.progress.aggregate()
    return built, agg["state"], (agg["last_replay"] or {}).get("rejected_constant")


def _victim(run: legs.Run, victim: str) -> tuple[str, str | None, str]:
    """The victim's pin leg outcome, the constant its per-pair replay rejected, and its class from classify.derive."""
    leg = json.loads((run.results / run.progress.data["legs"][victim]["pin"]["leg"]).read_text())
    replay, harness = (run.progress.data.get(kind, {}).get(victim)
                       for kind in ("replay_overrides", "harness_overrides"))
    return leg["outcome"], (leg["replay"] or {}).get("rejected_constant"), classify.derive(
        leg["outcome"], None, replay, harness, "none")


def _into(run: legs.Run) -> legs.Run:
    """`run`, as legs.prepare made it from the recipe, moved into the fixture run: rooted at fixtures-run/, its gate
    file its own, and its constants' repository that root, so no constant the run sets reaches the repository's."""
    fixture = dataclasses.replace(run.pol, root=run.pol.root / "fixtures-run", values={
        key: value for key, value in run.pol.values.items() if key != "public_tree"})
    return dataclasses.replace(run, pol=fixture, consts=dataclasses.replace(run.consts, repo=fixture.root))


@contextlib.contextmanager
def tmpdir(pol, name: str = "proof1b"):
    """TMPDIR the fixture run's own tmp/<name>/, fresh, for the calls inside; restored after."""
    tmp, called = _fresh(pol.root / "fixtures-run/tmp" / name), os.environ["TMPDIR"]
    os.environ["TMPDIR"] = str(tmp)
    try:
        yield tmp
    finally:
        os.environ["TMPDIR"] = called


def project(pol, name: str, **limits) -> tuple[legs.Run, list[dict]] | str:
    """The fixture project made ready under the fixture run's own root, fixtures-run/, where alone legs.run_leg
    honours the per-pair replay bypass, and whose gate file, trees, scratch and results are its own: the entries of
    the fixture project stage copied to fixtures-src/proof1b/ ingested and assembled under its own header into
    proof1b/work/; the project copied to env/proof1b/ at the pin's toolchain; and the pin run over it, with `limits`
    over the published ones and its results and logs under proof1b/<name>/. Returns that run and the pairs, or the
    assembler's refusal of a fixture pair. Called under tmpdir."""
    consts = constants.load(REPO)
    consts = dataclasses.replace(consts, published=consts.published | {
        "assembly": consts.published["assembly"] | {"header": HEADER},
        "limits": consts.published["limits"] | limits,
        "status": consts.published["status"] | {"independent_check": "available"}})  # its replays run on every branch
    out, src = pol.root / "fixtures-run/proof1b", pol.root / "fixtures-src/proof1b"
    work = _fresh(out) / "work"
    pairs = _assemble(ingest.parse(src / "entries.json", consts.published["assembly"]["suffix_regex"]),
                      consts.published["assembly"], work)
    if refused := next((pair for pair in pairs if pair["refusal"]), None):
        return f"the assembler refused {refused['pair_id']}: {refused['refusal']}"
    (logs := out / name / "logs").mkdir(parents=True)
    run = _into(legs.prepare(pol, consts, work, logs.parent, logs, ("pin",)))
    pin, tree = run.trees["pin"], run.pol.root / "env/proof1b"
    if tree.exists():
        shutil.rmtree(tree)
    shutil.copytree(src, tree)
    shutil.copy(REPO / "recipe" / pin.name / "lean-toolchain", tree)
    return dataclasses.replace(run, consts=dataclasses.replace(
        run.consts, env=consts.env | {"proof1b": consts.env[pin.name]}), trees={"pin": dataclasses.replace(
            pin, name="proof1b", recipe_id=None, provenance=None)}), pairs  # the fixture project is no recipe's tree


def run_proof1b(pol, timing_s: float, today: date) -> Proof1bReport:
    """Proof 1b over the fixture project as `project` makes it ready: two runs of its pin legs and aggregate, each
    --fresh replay under 1.5 times `timing_s`, the D+14 timing. Run 1 bypasses the victim's per-pair replay, so the
    plant reaches the aggregate: its replay must reject the planted constant, the walk attribute it to the victim,
    which is removed, and the aggregate rebuilt without it replay clean. Run 2 is pass 1, which bypasses nothing:
    the victim's per-pair replay must reject the plant, and the aggregate, without it, replay clean. In each run the
    victim's class must be rejected-by-replay. A fixture pair the assembler refuses fails the proof."""
    with tmpdir(pol) as tmp:
        if isinstance(made := project(pol, "run-1", replay_cap_s=1.5 * timing_s), str):
            return Proof1bReport(False, made)
        run, pairs = made
        victim = next(pair["pair_sha256"] for pair in pairs if pair["pair_id"] == VICTIM)
        for pair in pairs:
            legs.run_leg(run, pair, "pin", bypass=pair["pair_id"] == VICTIM)
        first = _check(run, pairs, today, timing_s)
        rerun = _check(run, pairs, today, timing_s) if first[1] in aggregate.REBUILD else None
        victims = [_victim(run, victim)]

        _fresh(tmp)
        (results := run.results.parent / "run-2").mkdir()
        for name in ("legs", "logs"):
            (results / name).mkdir()
        run = dataclasses.replace(run, results=results, logs=results / "logs",
                                  progress=progress.load(results / "progress.json", run.progress.data["sample_sha256"]))
        legs.pass1(run, pairs, run.consts.published["limits"]["run_ceiling_s"])  # two pairs: no ceiling cuts it short
        second = _check(run, pairs, today, timing_s)
        victims.append(_victim(run, victim))
    ids, cls = [pair["pair_id"] for pair in pairs], "rejected-by-replay"
    rest = [pair_id for pair_id in ids if pair_id != VICTIM]
    passed = (first == (ids, "rejected-rerun-pending", PLANTED) and rerun == second == (rest, "replay-returned", None)
              and victims == [("accepted", None, cls), ("replay-reject", PLANTED, cls)])
    return Proof1bReport(passed, f"aggregate (members, state, rejected): run 1 {first}, rebuilt {rerun}, run 2 "
                                 f"{second}; {VICTIM} (outcome, rejected, class) {victims}",
                         tuple(found[2] for found in victims))


def _pass1(run: legs.Run, pairs: list[dict]) -> None:
    """Pass 1 over `pairs` until each of the run's legs is terminal: a retryable outcome runs again, to the bound."""
    while run.progress.pending_pairs(pairs, list(run.trees)):
        if truncated := legs.pass1(run, pairs, run.consts.published["limits"]["run_ceiling_s"]):
            raise LedgerStop(truncated)


def _link(tree: Path, to: Path) -> None:
    """`tree` hard-linked at `to`, but for what a run writes in it: the pair sources, the aggregate's and the build
    output, made anew there. Nothing a run in `to` writes then reaches `tree`."""
    skip = {str(tree): {"Pairs", "Aggregate.lean"}, str(tree / ".lake"): {"build"}}
    shutil.copytree(tree, to, copy_function=os.link, ignore=lambda path, names: skip.get(path, set()) & set(names))
    (to / aggregate.BUILD).mkdir()


def _batch(pol, consts, out: Path, entries: list, envs: tuple[str, ...]) -> tuple[legs.Run, list]:
    """One batch of the fixture run, under `out`: pair 0 of each entry assembled, then pass 1 over them in
    `envs`, the undeclared entry's pair at the pin alone, recorded as declaring no revision; each environment's tree,
    as legs.prepare checks it under `pol`, the fixture run's own copy."""
    pairs = _assemble(entries, consts.published["assembly"], _fresh(out) / "work")
    (logs := out / "logs").mkdir()
    run = _into(legs.prepare(pol, consts, out / "work", out / "results", logs, envs))
    for tree in run.trees.values():
        if not (run.pol.root / "env" / tree.name).exists():
            _link(pol.root / "env" / tree.name, run.pol.root / "env" / tree.name)
    none = [pair for pair in pairs if pair["decl"] == UNDECLARED]
    run.progress.data["declared_none"] = [pair["pair_sha256"] for pair in none]
    _pass1(dataclasses.replace(run, trees={"pin": run.trees["pin"]}), none)
    _pass1(run, [pair for pair in pairs if pair not in none])
    return run, pairs


def _aggregate(run: legs.Run, pairs: list[dict], today: date) -> str | None:
    """The D+44 check's build of the aggregate over the batch's clean pairs, with its cross-pass comparison and no
    replay, budgeted at 1.5 times the per-pair limit with no per-member cost, as proof 1b's, so that over the cap is
    the kill in the fixture run's own gate file, a failed proof, never a cut written to the repository's constants:
    the event it returns, or None where the batch failed."""
    limits = run.consts.published["limits"]
    return aggregate._build(run, pairs, today, time.monotonic() + limits["run_ceiling_s"],
                            limits["per_pair_wall_clock_s"], 0, "crosspass-d21")


def run_fixture_set(pol, consts, today: date) -> FixtureReport:
    """Proofs 1, 2, 3 and 3b in the fixture run, under fixtures-run/ as its root, whose trees, scratch, results,
    records and gate file are its own, and whose pairs are all its own, no cut of the draw's applying. The planted
    entries stage copied to fixtures-src/planted/, under the run's header, go through pass 1 in both environments
    (at the pin alone where the legacy environment is unavailable, which leaves proof 3's mismatch entry out), then an
    aggregate over the clean ones, for the cross-pass check, with no replay; their records are written, and each
    planted pair's pin outcome and class held to EXPECTED. With them, proof 3b's other half, the assembler fixture
    set's elaboration agreement: pair 0 of each of its proof-bearing fixtures through pass 1 at the pin, then one
    aggregate over the clean ones but the scope-leak fixture, every member of which must agree, and one with that
    fixture first, where the cross-pass rule must catch a member after it."""
    root, overlay = pol.root / "fixtures-run", devoverlay.load(pol)
    consts = dataclasses.replace(consts, published=consts.published | {
        "assembly": consts.published["assembly"] | ({"header": overlay.header} if overlay else {}),
        "sampling": consts.published["sampling"] | {"cut_n": 0}})
    reduced = consts.published["status"]["legacy"] == "environment-unavailable"
    suffix = consts.published["assembly"]["suffix_regex"]
    with tmpdir(pol, "set"):
        _fresh(root / "env")
        entries = [entry for entry in ingest.parse(pol.root / "fixtures-src/planted/entries.json", suffix)
                   if not (reduced and entry.decl == "planted_mismatch")]
        planted, pairs = _batch(pol, consts, root / "planted", entries,
                                ("pin",) if reduced else ("pin", "legacy"))
        built = _aggregate(planted, pairs, today)
        found = {record["pair_id"]: record for record in records.build(
            {"draw": pairs}, pairs, planted.progress, planted.results, planted.table, consts)}
        write_atomic(planted.results / "records.jsonl", records.dump(list(found.values())))

        files = sorted((REPO / "fixtures/assembler").glob("*.jsonl"), key=lambda path: (path.name != LEAK, path.name))
        lines = [json.loads(line) for path in files for line in path.read_text().splitlines() if line[:1] == "{"]
        write_atomic(release := root / "assembler.json", json.dumps(lines).encode())
        positive = [entry for entry in ingest.parse(release, suffix) if entry.proofs and not entry.refusal]
        assembler, fixtures = _batch(pol, consts, root / "assembler", positive, ("pin",))
        clean = len(aggregate.members(assembler.progress, fixtures, assembler.results))
        agree = _aggregate(assembler, fixtures[1:], today)
        _aggregate(assembler, fixtures, today)  # the scope-leak fixture first: what it removes is read below
    crossed = agree is not None and any(  # with no member removed before it, every removal is the leak's
        override["source"] == "crosspass-d21" and pair != fixtures[0]["pair_sha256"]
        for pair, override in assembler.progress.data.get("harness_overrides", {}).items())

    verdicts = {}
    for proof in ("1", "2", "3", "3b"):
        mine = [(pair_id, row) for pair_id, row in EXPECTED.items() if row[0] == proof and (row[3] or not reduced)]
        passed = all(pair_id in found and (found[pair_id]["legs"]["pin"]["outcome"], found[pair_id]["class"])
                     == (row[1], row[3 if reduced else 2]) for pair_id, row in mine)
        evidence = "; ".join(f"{pair_id}: {found[pair_id]['class'] if pair_id in found else 'absent'}"
                             for pair_id, _ in mine)
        if proof == "3b":
            caught = passed and found["planted_victim__p0"]["overrides"]["harness"]["source"] == "crosspass-d21"
            passed = caught and found["#7__p0"]["refusal"] == "name-collision" and crossed
            evidence += (f"; the scope-leak pair {'caught' if caught else 'not caught'} by the cross-pass rule; the "
                         f"planted batch {'failed' if built is None else 'passed'}; assembler set: {clean} of "
                         f"{len(fixtures)} clean at the pin, without the scope-leak fixture "
                         f"{'agreeing' if agree else 'disagreeing'}, with it first "
                         f"{'disagreeing by' if crossed else 'not caught by'} the cross-pass rule")
        verdicts[f"d21-proof-{proof}"] = passed, evidence
    return FixtureReport(verdicts, reduced)
