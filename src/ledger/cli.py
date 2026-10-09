"""The command line: python -m ledger <command> --policy <file>. Every command loads the named policy
first and checks every path it writes, then (if it does run work) creates its run directory and takes the
run lock, then confines its own writes before reading any input, except publish, the operator's push at a
terminal; a pipeline command that does run work then tests that confinement from inside it, and every
command that does run work starts its children's state fresh. A failed precondition, or any other
error, prints its reason, goes into the run report, and exits 2."""

import argparse
import hashlib
import json
import os
import re
import shutil
import sys
import time
import traceback
from collections import Counter
from dataclasses import asdict
from datetime import date, datetime
from pathlib import Path

from ledger import (REPO, aggregate, assemble, classify, confine, constants, datefree, envbuild, fixtures, frame,
                    freeze, gatefile, ingest, legs, measure, modes, pilot, policy, preflight, probes, progress, publish,
                    rebuild, records, report, sample, stage)
from ledger.types import LedgerStop

# Each takes the run lock itself.
LOCK_TAKERS = {"preflight", "oneoff", "ingest", "frame", "sample", "assemble", "env", "probe", "measure", "fixtures",
               "freeze", "pilot", "report", "stage", "publish", "withdraw", "nightly", "pass1", "aggregate", "rebuild",
               "run"}
OPERATOR = {"stage", "publish", "withdraw"}  # run at a terminal, whose security label can fail the self-test
NIGHTS = {"nightly", "rebuild"}  # each started by its timer, every night; on contention a skipped night, exit 0
LOCK_WAIT_S = 600  # how long a rebuild waits for the run lock
RUN_ID = re.compile(r"\d{4}-\d{2}-\d{2}T\d{6}")  # a run's name, runs/<run-id>/ and tmp/<run-id>/
SKIPPED = re.compile(r"lock held by pid (\d+|unknown); cause=(\S+)")  # a skipped-night line's reason
PROOF1B_FIRST_S = 2 * 3600  # over it, proof 1b's D+14 timing puts it first on D+21, after the freeze
AFTER_PROOF1B = {"d21-proof-1", "d21-proof-2", "d21-proof-3", "d21-proof-3b", "d21-pilot"}
GLOSS = {  # a name in a run report that a morning reader could take for a fault of this host
    "environment-mismatch": "environment-mismatch: the proof checks under the legacy toolchain it declares, not the "
                            "pin's; version skew, not a fault of this host",
    "oom": "oom is the leg's own memory ceiling, not the host running out of memory"}


def _attempt(env: str, n: int) -> list[str]:
    return ["env", "build", "--env", env, "--attempt", str(n)]


# The dated one-offs: instance -> (the command it runs, the ceiling gate line its milestone needs first).
# A numbered instance's number is its build attempt.
ONEOFF = {
    "probe-d7": (["probe", "d7"], "ceiling:d7-probes"),
    **{f"mathlib-{n}": (_attempt("pin", n), "ceiling:d14-measurement") for n in (1, 2, 3)},
    "mathlib-seeded": (_attempt("pin-seeded", 1), "ceiling:d14-stop-loss"),
    "measure-d14": (["measure", "d14"], "ceiling:d14-measurement"),
    **{f"legacy-{n}": (_attempt("legacy", n), "ceiling:d21-legacy") for n in (1, 2, 3)},
    "freeze": (["freeze"], "ceiling:d21-pilot"),
    "fixtures": (["fixtures"], "ceiling:d21-pilot"),
    "proof1b": (["fixtures", "--proof1b"], "ceiling:d21-pilot"),
    "pilot-d21": (["pilot", "d21"], "ceiling:d21-pilot"),
    "pilot-d21-replay": (["pilot", "d21", "--replay"], "ceiling:d21-pilot"),
}


def _run_dir(root: Path) -> Path:
    """Create this run's directory, runs/<YYYY-MM-DD>T<HHMMSS>/ under the root. A run starting in a second
    that already has one waits for the next second, so every run has its own."""
    (root / "runs").mkdir(exist_ok=True)
    while True:
        run = root / "runs" / datetime.now().strftime("%Y-%m-%dT%H%M%S")
        try:
            run.mkdir()
            return run
        except FileExistsError:
            time.sleep(1 - time.time() % 1)


def _host(pol: policy.Policy) -> str:
    """Free space where the run writes, and the memory and swap available, now."""
    mount = pol.values["disk_floor_mount"] if pol.kind == "operator" else str(pol.root)
    found = preflight.meminfo()
    try:
        disk = f"{confine.free_gb(mount):.0f} GB free on {mount}"
    except LedgerStop as stop:  # reported as the run's state, as the stop it causes is
        disk = str(stop)
    return (f"{disk}, MemAvailable {found['MemAvailable'] / preflight.GIB_KB:.1f} GiB, "
            f"SwapFree {found['SwapFree'] / preflight.GIB_KB:.1f} GiB")


def _counts(counted) -> str:
    return ", ".join(f"{key} {n}" for key, n in sorted(counted.items())) if counted else "none"


def _grouped(counted: Counter) -> str:
    """Pairs by their legs' outcomes, the largest group first."""
    return "; ".join(f"{n} with {pattern}" for pattern, n in counted.most_common())


def _glosses(text: str) -> list[str]:
    """A gloss of each name in `text` that could read as a fault of this host."""
    named = set(re.findall(r"[\w-]+", text))
    return [gloss for key, gloss in GLOSS.items() if key in named]


def _classes(counted: Counter) -> str:
    """The pairs by class, one line for the success class and one for each other class, each class's pairs by
    their legs' outcomes, and under a class its glosses."""
    if not counted:
        return "none"
    by_class = {}
    for (cls, pattern), n in counted.items():
        by_class.setdefault(cls, Counter())[pattern] = n
    found = {cls: f"{cls} {n.total()} ({_grouped(n)})" for cls, n in sorted(by_class.items())}
    lines = [f"passed: {found.pop('reproduced', 'none')}",
             *(f"not reproduced: {line}" for line in found.values() or ["none"])]
    return _pairs(counted.total()) + "".join(f"\n  - {line}" + "".join(f"\n    - {gloss}" for gloss in _glosses(line))
                                             for line in lines)


def _pairs(n: int) -> str:
    return f"{n} pair{'s' * (n != 1)}"


def _report(pol: policy.Policy, run: Path, command: str, result: str, confinement: str, facts: dict) -> None:
    """Write the run's report.md, never over an existing file: one line each for what ran and why, how it ended and
    whether that needs the operator and why, the legs it ran by outcome and the pairs it completed by class, pass 1's
    progress where it ran, what was skipped, the ceiling, the host at start and end, the confinement, the code commit
    and the recipe identifiers."""
    operator = (f"yes: the run {result}" if result.startswith("stopped") else
                facts.get("operator", "no: only a stop needs the operator, and this run did not stop"))
    lines = [f"command: `ledger {command}`", f"mode: {facts.get('mode', 'the command itself')}", f"result: {result}",
             f"needs the operator: {operator}",
             f"attempted: {facts.get('attempted', 'no legs')}", f"leg outcomes: {_counts(facts.get('outcomes'))}",
             f"classes of the pairs completed: {_classes(facts.get('classes'))}",
             *([f"pass 1: {facts['pass 1']}"] if "pass 1" in facts else []),
             f"skipped: {facts.get('skipped', 'nothing')}", f"ceiling: {facts.get('ceiling', 'not reached')}",
             f"host at start: {facts.get('host', 'not read')}", f"host at end: {_host(pol)}",
             f"confinement: {confinement}", f"code_commit: {facts.get('code_commit', 'not read')}",
             f"recipe_ids: {facts.get('recipe_ids', 'not read')}"]
    with open(run / "report.md", "x", encoding="utf-8") as f:
        f.write("# Run report\n\n" + "".join(f"- {line}\n" for line in lines))


def _fresh_state(root: Path, run: Path) -> None:
    """Nothing a child wrote in an earlier run is input to this one: xdg-cache/ starts empty, an earlier run's own
    tmp/<run-id>/ is removed, and TMPDIR, which children inherit, is this run's own tmp/<run-id>/."""
    cache = root / "xdg-cache"
    if cache.exists():
        shutil.rmtree(cache)
    cache.mkdir()
    for old in (root / "tmp").glob("*"):
        if RUN_ID.fullmatch(old.name):
            shutil.rmtree(old)
    (tmp := root / "tmp" / run.name).mkdir(parents=True)
    os.environ["TMPDIR"] = str(tmp)


def _cause(holder: str) -> str:
    """What holds the lock, by its command line: a D+30 rebuild, the D+21 pilot replay, or another run."""
    try:
        argv = Path(f"/proc/{holder}/cmdline").read_bytes().split(b"\0")
    except OSError:  # the holder has ended, or never named itself
        return "lock"
    return "d30-rebuild" if b"rebuild" in argv else "d21-replay" if {b"--replay", b"pilot-d21-replay"} & set(argv) \
        else "lock"


def contended(pol: policy.Policy, run: Path, command: str, holder: str, confinement: str, facts: dict) -> int:
    """Another run holds the lock. nightly and rebuild record a skipped night in the gate file, naming the holder and
    what it is, and exit 0; every other command exits 1. The run report names the holder either way."""
    night = command in NIGHTS
    if night:
        gatefile.append(pol, "skipped-night", "skipped", "pipeline",
                        f"lock held by pid {holder}; cause={_cause(holder)}", date.today())
    facts["skipped"] = f"the night's work: the run lock is held by pid {holder}" if night else "everything"
    _report(pol, run, command, f"not started: the run lock is held by pid {holder}", confinement, facts)
    return 0 if night else 1


def _preflight(pol: policy.Policy, args) -> int:
    for line in preflight.check(pol, constants.load(REPO)):
        print("ok ", line)
    return 0


def _ingest(pol: policy.Policy, args) -> int:
    consts = constants.load(REPO)
    for line in preflight.check(pol, consts):
        print("ok ", line)
    entries = list(ingest.parse(ingest.fetch(consts, pol), consts.published["assembly"]["suffix_regex"]))
    print(f"revision {consts.source['revision']}, sha256 {consts.source['sha256']}, "
          f"record unit {consts.source['record_unit']}, {len(entries)} records, splits {dict(Counter(e.split for e in entries))}")
    refused = Counter(e.refusal for e in entries)
    print("refusals: " + ", ".join(f"{r} {refused[r]}" for r in ingest.REFUSALS))
    print(f"entries.jsonl {ingest.write(entries, pol.root / 'work')}")
    return 0


def _frame(pol: policy.Policy, args) -> int:
    consts = constants.load(REPO)
    for line in preflight.check(pol, consts):
        print("ok ", line)
    built = frame.build(pol.root / "work" / "entries.jsonl", consts)
    s = built.summary
    print(f"records {s['records_total']}, splits {s['split_counts']}, proofless {s['proofless_excluded']}, "
          f"proof-bearing {s['proof_bearing']}")
    print(f"within-entry exact duplicates removed {s['within_entry_exact_duplicates_removed']} "
          f"(of {s['proof_elements_raw']} elements), multiplier "
          f"mean {s['multiplier']['mean']:.2f}, median {s['multiplier']['median']}, max "
          f"{s['multiplier']['max']} at {s['multiplier']['max_entry']}")
    print(f"drawable pairs before cross-entry dedupe {s['drawable_pairs_before_cross_dedupe']}; cross-entry "
          f"duplicates removed {s['cross_entry_duplicates_removed']}, eligible entries {s['eligible_entries']}, "
          f"drawable pairs {s['drawable_pairs']}")
    print(f"refused {s['refused']}")
    print(f"frame.json {frame.write(built, pol.root / 'work')}")
    return 0


def _sample(pol: policy.Policy, args) -> int:
    consts = constants.load(REPO)
    for line in preflight.check(pol, consts):
        print("ok ", line)
    work = pol.root / "work"
    built = frame.build(work / "entries.jsonl", consts)
    frame.published(built, work)
    drawn = sample.draw(built, consts.published)
    print(f"seed {drawn['seed']}, drawable frame {drawn['drawable_frame_size']}, drawn {len(drawn['draw'])}, "
          f"distinct entries {drawn['distinct_entries']}")
    print(f"sample.json {sample.write(drawn, work)}")
    return 0


def _assemble(pol: policy.Policy, args) -> int:
    consts = constants.load(REPO)
    for line in preflight.check(pol, consts):
        print("ok ", line)
    work = pol.root / "work"
    drawn = json.loads((work / "sample.json").read_bytes())
    built = frame.build(work / "entries.jsonl", consts)
    digest, refused = assemble.write_pairs(drawn, built, consts.published["assembly"], work)
    print(f"{len(drawn['draw'])} pairs assembled, every element digest equal to the frame's; texts {refused[None]}; "
          "refusals " + ", ".join(f"{kind} {refused[kind]}" for kind in assemble.REFUSALS))
    print(f"assembled.jsonl {digest}")
    return 0


def _env(pol: policy.Policy, args) -> int:
    consts = constants.load(REPO)
    for line in preflight.check(pol, consts):
        print("ok ", line)
    envbuild.check_attempt(pol.root, consts, args.env, args.tree, args.attempt)  # before the fetch removes a tree
    logs = args.run_dir / "logs"
    logs.mkdir()
    envbuild.fetch(pol, consts, logs, args.env, args.tree)
    print(json.dumps(asdict(envbuild.build(pol, consts, logs, args.env, args.tree, args.attempt))))
    return 0


def _probe(pol: policy.Policy, args) -> int:
    consts = constants.load(REPO)
    for line in preflight.check(pol, consts):
        print("ok ", line)
    (logs := args.run_dir / "logs").mkdir()
    found = probes.d7(pol, consts, logs, args.self_test)
    for letter, (met, evidence) in found.items():
        print(f"({letter}) {'met' if met else 'unmet'}: {evidence}")
    return 0 if all(met for met, _ in found.values()) else 2


def _report_records(pol: policy.Policy, args) -> int:
    """Write results/records.jsonl from the leg results, the progress file and the table, then summary.json and
    index.json from it, and the README and FINDING_REPORT.md once the project has a public name and publisher,
    and print each one's sha256.
    --reclassify: derive every stored leg outcome again with the table instead, and name the legs it changed.
    --from-records: derive a records.jsonl again from its own records and the table, and print its sha256 and its
    canonical subset's."""
    consts = constants.load(REPO)
    table = classify.load(REPO, consts)
    if args.from_records:
        data = records.from_records(args.from_records, table, consts)
        print(f"{args.from_records.name}: every record derived again, byte for byte; "
              f"sha256:{hashlib.sha256(data).hexdigest()}; canonical subset "
              f"{report.canonical_subset([json.loads(line) for line in data.splitlines()])}")
        return 0
    results = pol.root / "results"
    if not (results / "progress.json").exists():
        raise LedgerStop("results/progress.json does not exist: there are no leg results to report")
    if args.reclassify:
        drawn = (pol.root / "work/sample.json").read_bytes()
        prog = progress.load(results / "progress.json", "sha256:" + hashlib.sha256(drawn).hexdigest())
        changed = legs.reclassify(prog, results, table, consts)
        print(f"{len(changed)} leg outcomes changed" + "".join(f"\n  {rel}" for rel in changed))
        return 0
    written = report.run(pol, consts)
    for name, digest in written.items():
        print(name, digest)
    if "README.md" not in written:
        print("README.md and FINDING_REPORT.md not rendered: public_name or publisher empty in recipe/constants.toml")
    return 0


def _measure(pol: policy.Policy, args) -> int:
    """The D+14 measurement over the draw, the preflight and the legacy environment's probes first."""
    consts = constants.load(REPO)
    (logs := args.run_dir / "logs").mkdir()
    print(json.dumps(measure.d14(pol, consts, pol.root / "work", pol.root / "results", logs, date.today())))
    return 0


def _fixtures(pol: policy.Policy, args) -> int:
    """Proofs 1, 2, 3 and 3b in the fixture run, with the branch reduction where the legacy environment is
    unavailable; with --proof1b, proof 1b alone, which, where its D+14 timing exceeded 2 hours, runs first on D+21:
    on the freeze's day, before any proof or pilot line; a repeat after a failed proof runs on a later night. Either
    runs once the freeze lines are recorded. Each verdict is a gate line; a failed one exits 1."""
    consts, today = constants.load(REPO), date.today()
    for line in preflight.check(pol, consts):
        print("ok ", line)
    if not freeze.frozen(pol):
        raise LedgerStop("the fixtures run under the frozen classifier table and per-pair limit: freeze first")
    if args.proof1b:
        timing = json.loads((pol.root / measure.DIR / "proof1b.json").read_text())["timing_s"]
        rows = gatefile.rows(pol)  # the limit-freeze line is the freeze's alone, never the re-freeze's
        if timing > PROOF1B_FIRST_S and (today.isoformat(), "limit-freeze") in {row[:2] for row in rows} and any(
                row[1] in AFTER_PROOF1B for row in rows):
            raise LedgerStop(f"proof 1b's D+14 timing, {timing:.0f} s, exceeded 2 hours: on the freeze's day it runs "
                             "first, before any proof or pilot line; a repeat runs on a later night")
        report = fixtures.run_proof1b(pol, timing, today)
        verdicts = {"d21-proof-1b": (report.passed, report.evidence)}
    else:
        found = fixtures.run_fixture_set(pol, consts, today)
        verdicts = found.verdicts
        if found.reduced:
            gatefile.append(pol, "branch-reduction", "proofs 1, 2 and 3 reduced", "pipeline", "legacy "
                            "environment-unavailable: each planted entry classified at the pin alone, proof 3 by its "
                            "undeclared entry alone", today)
    for gate, (passed, evidence) in verdicts.items():
        gatefile.append(pol, gate, "pass" if passed else "fail", "pipeline", gatefile.sanitize(pol, evidence, 400),
                        today)
        print(gate, "pass" if passed else "fail", evidence)
    return 0 if all(passed for passed, _ in verdicts.values()) else 1


def _freeze(pol: policy.Policy, args) -> int:
    """The D+21 freeze; with --rows, a failed proof's one re-freeze to table-v2.toml, changed in those rows alone."""
    consts = constants.load(REPO)
    for line in preflight.check(pol, consts):
        print("ok ", line)
    results, work = pol.root / "results", pol.root / "work"
    prog = progress.load(results / "progress.json",
                         "sha256:" + hashlib.sha256((work / "sample.json").read_bytes()).hexdigest())
    if args.rows:
        print(json.dumps(freeze.refreeze(pol, consts, prog, results, args.rows, date.today())))
    else:
        print(json.dumps(asdict(freeze.freeze(pol, consts, prog, results, date.today()))))
    return 0


def _pilot(pol: policy.Policy, args) -> int:
    """The D+21 pilot over the draw; with --replay, its replay alone, in its own unit."""
    consts = constants.load(REPO)
    for line in preflight.check(pol, consts):
        print("ok ", line)
    unavailable = consts.published["status"]["legacy"] == "environment-unavailable"
    (logs := args.run_dir / "logs").mkdir()
    run = legs.prepare(pol, consts, pol.root / "work", pol.root / "results", logs,
                       ("pin",) if args.replay or unavailable else ("pin", "legacy"))
    pairs = [json.loads(line) for line in (pol.root / "work/assembled.jsonl").read_text().splitlines()]
    print(pilot.d21_replay(run, pairs, date.today()) if args.replay else asdict(pilot.d21(run, pairs, date.today())))
    return 0


def _ready(pol: policy.Policy, consts, args, envs: tuple[str, ...], replay: bool = False) -> legs.Run:
    """The preflight, then the run of legs in `envs` over the draw; the progress file takes the gate file's skipped
    nights, which a night that found the lock held could not write while another process held it."""
    for line in preflight.check(pol, consts, replay):
        print("ok ", line)
    (logs := args.run_dir / "logs").mkdir()
    run = legs.prepare(pol, consts, pol.root / "work", pol.root / "results", logs, envs)
    args.facts |= legs.identity(run)
    nights = [{"date": row[0], **({"holder_pid": int(found[1])} if found[1].isdigit() else {}), "cause": found[2]}
              for row in gatefile.rows(pol) if row[1] == "skipped-night" and (found := SKIPPED.fullmatch(row[4]))]
    if nights != run.progress.data.get("skipped_nights", []):
        run.progress.data["skipped_nights"] = nights
        run.progress.save()
    return run


def _pass1(pol: policy.Policy, args) -> int:
    """Pass 1, resumed, until the ceiling (--ceiling, in hours; by default the run ceiling): every leg each pair of the
    draw needs, in draw order. The run report counts the legs it ran by outcome and the pairs it completed by class
    and their legs' outcomes, the pairs of the sample complete, and the pairs it left for pass 1's next night: those
    the ceiling kept it from reaching, and those left to retry, each leg to retry with its attempt and the bound."""
    consts = constants.load(REPO)
    unavailable = consts.published["status"]["legacy"] == "environment-unavailable"
    run = _ready(pol, consts, args, ("pin",) if unavailable else ("pin", "legacy"))
    pairs = [json.loads(line) for line in (pol.root / "work/assembled.jsonl").read_text().splitlines()]

    def results() -> dict:  # each leg's latest result, by pair digest and environment
        return {(sha, env): state["leg"] for sha, envs in run.progress.data["legs"].items() for env, state in envs.items()}
    before = results()
    truncated = legs.pass1(run, pairs, args.ceiling * 3600 if args.ceiling else
                           consts.published["limits"]["run_ceiling_s"])
    ran = {key: leg for key, leg in results().items() if leg != before.get(key)}
    outcomes = {key: json.loads((run.results / leg).read_text())["outcome"] for key, leg in ran.items()}
    touched = {sha for sha, _ in ran}
    sampled = pairs[:consts.published["sampling"]["cut_n"] or None]
    pending = {pair["pair_sha256"] for pair, _ in run.progress.pending_pairs(sampled, list(run.trees))}
    states, bound = run.progress.data["legs"], consts.published["limits"]["attempt_bound"]

    def legs_of(sha: str, retrying: bool, cls: str | None = None) -> str:  # its legs, or those left to retry
        return records.legs_text({
            env: json.loads((run.results / state["leg"]).read_text())["outcome"] +
            (f" on attempt {state['attempts'] - state.get('reopened_at', 0)} of {bound}" if retrying else "")
            for env, state in states[sha].items() if not (retrying and state["terminal"])}, cls,
            {kind: run.progress.data.get(f"{kind}_overrides", {}).get(sha) for kind in ("replay", "harness")}, True)
    retry = Counter(legs_of(sha, True) for sha in pending & touched)
    grouped = _grouped(retry)
    skipped = f"{_pairs(len(pending - touched))} not reached before the run ceiling"
    left_to_retry = f"{_pairs(retry.total())} left to retry"
    left = ([skipped] if truncated else []) + ([left_to_retry] if retry else [])
    classes = Counter((cls, legs_of(sha, False, cls)) for sha in touched - pending
                      for cls in [records.pair_class(run.progress, run.results, sha, consts.published)])
    needs = (f"{' and '.join(left)}; pass 1 picks up what is left on its next night" if left
             else "nothing needs you today")
    if any(cls != "reproduced" for cls, _ in classes):
        needs += "; the classes not reproduced so far are results for you to weigh on the notice day"
    args.facts |= {"attempted": f"legs {len(ran)} ({_counts(Counter(env for _, env in ran))}), pairs {len(touched)}",
                   "outcomes": Counter(outcomes.values()), "classes": classes,
                   "pass 1": f"{len(sampled) - len(pending)} of {len(sampled)} pairs complete" +
                             (f"; {left_to_retry} ({'; '.join([grouped, *_glosses(grouped)])})" if retry else ""),
                   "ceiling": truncated or "not reached",
                   "operator": f"no: {needs}",
                   "skipped": skipped if truncated else "nothing"}
    print(truncated or f"pass 1: {len(ran)} legs run")
    return 0


def _aggregate(pol: policy.Policy, args) -> int:
    """One night of the D+44 check, from the state the progress file records, with D+14's figures; the preflight
    holds the replay's memory floor."""
    consts = constants.load(REPO)
    run = _ready(pol, consts, args, ("pin",), replay=True)
    pairs = [json.loads(line) for line in (pol.root / "work/assembled.jsonl").read_text().splitlines()]
    d14 = json.loads((pol.root / measure.DIR / "projection.json").read_text())
    before = run.progress.aggregate()["state"]
    # E and m are None only on the replay-unavailable branch, where no replay runs to use them
    after = aggregate.step(run, pairs, date.today(), d14["Eb"], d14["mb"], d14["E"] or 0, d14["m"] or 0)
    args.facts["attempted"] = f"the D+44 check, from state {before} to {after}"
    print(after)
    return 0


def _nightly(pol: policy.Policy, args) -> int:
    """The night's one action from the mode table, taken before the lock (main: an exit takes no lock)."""
    return (_pass1 if args.action.mode == "pass1" else _aggregate)(pol, args)


def _rebuild(pol: policy.Policy, args) -> int:
    """One D+30 rebuild attempt, its deadline counted from this process's start; with --allowance, main prints the
    attempt's allowance instead and takes no lock."""
    result = rebuild.attempt(_ready(pol, constants.load(REPO), args, ("pin",)), date.today(), args.started)
    args.facts["attempted"] = f"a D+30 rebuild attempt: {result}"
    print(result)
    return 0


def _run(pol: policy.Policy, args) -> int:
    """The date-free command: the whole sample, or with --pair that pair alone."""
    consts = constants.load(REPO)
    for line in preflight.check(pol, consts):
        print("ok ", line)
    return datefree.run(pol, consts, args.run_dir, args.facts, pair=args.pair, with_legacy=args.with_legacy)


def _overrun(root: Path, today: date) -> str | None:
    """The PID of a rebuild that has held the run lock since an earlier night, or None. The lock's holder writes its PID
    into the lock file as it takes it, so the file's mtime is when it was taken. A symlink in the lock's place is
    refused, as preflight.lock refuses it."""
    try:
        fd = os.open(root / "lock", os.O_RDONLY | os.O_NONBLOCK | os.O_CLOEXEC | os.O_NOFOLLOW)
    except FileNotFoundError:
        return None
    with open(fd, "rb") as lock:
        taken, holder = date.fromtimestamp(os.fstat(fd).st_mtime), lock.read(32).strip()
    return holder.decode() if taken < today and holder.isdigit() and _cause(holder.decode()) == "d30-rebuild" else None


def _tonight(pol: policy.Policy, args) -> str | None:
    """Why tonight is not this unit's, read before the lock, so that neither unit logs a false skipped night: once a
    kill is recorded, every night; for rebuild, any night but a rebuild night; for the nightly, its action from the
    mode table (set on args), an exit on a rebuild night among them. A rebuild night whose lock a rebuild attempt begun
    on an earlier night still holds is a skipped night, and the nightly writes its line, cause d30-rebuild. None when
    the night is this unit's."""
    if (d0 := gatefile.d0(pol)) is None:
        raise LedgerStop("the gate file records no d0 line: no night has a day after D+0")
    path, today = pol.root / "results/progress.json", date.today()
    state, day = json.loads(path.read_text()) if path.exists() else {}, (today - d0).days
    if any(row[1] == "kill" for row in gatefile.rows(pol)):
        args.action = modes.Action("exit", f"D+{day}: a kill is recorded")
    elif args.command == "rebuild":
        return None if modes.rebuild_night(day, state) else f"D+{day}: not a rebuild night"
    elif modes.rebuild_night(day, state) and (holder := _overrun(pol.root, today)):
        gatefile.append(pol, "skipped-night", "skipped", "pipeline", f"lock held by pid {holder}; cause=d30-rebuild",
                        today)
        args.action = modes.Action(
            "exit", f"D+{day}: the rebuild attempt begun on an earlier night holds the run lock, pid {holder}")
    else:
        args.action = modes.action(today, d0, state)
    args.facts["mode"] = f"{args.action.mode}, {args.action.reason}"
    return args.action.reason if args.action.mode == "exit" else None


def _gate(pol: policy.Policy, args) -> int:
    """Append the line, and once the public tree holds the gate file, commit it there, and nothing else."""
    gatefile.append(pol, args.gate, args.verdict, args.evaluator, args.reason, date.today())
    if pol.kind == "operator" and (public := Path(pol.values["public_tree"])).joinpath("gates/GATES.md").exists():
        stage.commit(public, pol.values["identity"], f"Gate line: {args.gate}", ("gates/GATES.md",))
    return 0


def _stage(pol: policy.Policy, args) -> int:
    report = stage.stage(pol, constants.load(REPO), dry_run=args.dry_run)
    for rel in report.skipped:
        print("skipped, absent from the development repository:", rel)
    for rel in report.held:
        print("taken from the public tree, its only home since a gate line recorded its change:", rel)
    if report.late:
        print("results not staged, the published ones unchanged:", report.late)
    print("dry run: the public tree is unchanged" if args.dry_run
          else "committed" if report.committed else "nothing to commit")
    return 0


def _publish(pol: policy.Policy, args) -> int:
    print(publish.publish(pol, tag=args.tag, dry_run=args.dry_run))
    return 0


def _withdraw(pol: policy.Policy, args) -> int:
    print(publish.withdraw(pol, constants.load(REPO), args.pair, date.today(), args.party_class, args.ground))
    return 0


def _oneoff(pol: policy.Policy, args) -> int:
    """The instance's command, once its milestone's ceiling line is recorded, in this run."""
    argv, ceiling = ONEOFF[args.instance]
    if not any(row[1] == ceiling for row in gatefile.rows(pol)):
        raise LedgerStop(f"no `{ceiling}` gate line: a milestone without its ceiling line does not start")
    chosen = _parser().parse_args([*argv, "--policy", str(args.policy)])
    chosen.run_dir, chosen.self_test, chosen.facts = args.run_dir, args.self_test, args.facts
    return chosen.run(pol, chosen)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="ledger")
    commands = parser.add_subparsers(dest="command", required=True)

    def command(name: str, run) -> argparse.ArgumentParser:
        sub = commands.add_parser(name)
        sub.add_argument("--policy", type=Path, required=True)
        sub.set_defaults(run=run)
        return sub

    command("preflight", _preflight)
    command("ingest", _ingest)
    command("frame", _frame)
    command("sample", _sample)
    command("assemble", _assemble)
    gate = command("gate", _gate)
    for field in ("--gate", "--verdict", "--evaluator", "--reason"):
        gate.add_argument(field, required=True)
    command("oneoff", _oneoff).add_argument("instance", choices=ONEOFF)
    command("nightly", _nightly).set_defaults(ceiling=None)
    command("pass1", _pass1).add_argument("--ceiling", type=float)
    command("aggregate", _aggregate)
    command("rebuild", _rebuild).add_argument("--allowance", action="store_true")
    running = command("run", _run)
    running.add_argument("--pair")
    running.add_argument("--with-legacy", action="store_true")
    command("probe", _probe).add_argument("action", choices=["d7"])
    command("measure", _measure).add_argument("action", choices=["d14"])
    command("fixtures", _fixtures).add_argument("--proof1b", action="store_true")
    command("freeze", _freeze).add_argument("--rows", nargs="+")
    piloting = command("pilot", _pilot)
    piloting.add_argument("action", choices=["d21"])
    piloting.add_argument("--replay", action="store_true")
    env = command("env", _env)
    env.add_argument("action", choices=["build"])
    env.add_argument("--env", choices=["pin", "pin-seeded", "legacy"], required=True)
    env.add_argument("--attempt", type=int)
    env.add_argument("--tree", choices=["pin", "rebuild"], default="pin")
    report = command("report", _report_records).add_mutually_exclusive_group()
    report.add_argument("--reclassify", action="store_true")
    report.add_argument("--from-records", type=Path)
    command("stage", _stage).add_argument("--dry-run", action="store_true")
    publishing = command("publish", _publish)
    publishing.add_argument("--operator", action="store_true", required=True)
    publishing.add_argument("--dry-run", action="store_true")
    publishing.add_argument("--tag")
    withdrawing = command("withdraw", _withdraw)
    for field in ("--pair", "--party-class", "--ground"):
        withdrawing.add_argument(field, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    args.started = time.monotonic()  # the unit's start, near enough: a rebuild attempt's deadline counts from it
    name = " ".join([args.command, *([args.instance] if args.command == "oneoff" else [])])
    run, test, confinement = None, None, "not applied"  # run: created once every path is checked, before any write
    args.facts = {}  # what the run report says beyond the command and its result
    try:
        if args.command == "publish" and not (os.isatty(0) and os.isatty(1)):
            raise LedgerStop("publish runs only at the operator's terminal: stdin and stdout must both be TTYs")
        pol = policy.load(args.policy)
        preflight.paths(pol)
        if args.command == "rebuild" and args.allowance:
            consts, drawn = constants.load(REPO), (pol.root / "work/sample.json").read_bytes()
            prog = progress.load(pol.root / "results/progress.json", "sha256:" + hashlib.sha256(drawn).hexdigest())
            print(f"{rebuild.allowance(pol, consts, prog):.0f} s")
            return 0
        if args.command in LOCK_TAKERS:
            run = _run_dir(pol.root)
            args.facts["host"] = _host(pol)
        if args.command in NIGHTS and (idle := _tonight(pol, args)):
            args.facts["skipped"] = f"the night's work: {idle}"
            _report(pol, run, name, "exit 0, before the run lock", "not applied: the night is not this unit's",
                    args.facts)
            return 0
        holder = preflight.lock(pol.root, LOCK_WAIT_S if args.command == "rebuild" else 0) if run else None
        if args.command == "publish":
            landlock, confinement = None, "not applied: publish is the operator's push at a terminal"
        else:
            landlock = confinement = confine.apply_fs(pol)
        if holder is not None:
            return contended(pol, run, name, holder, confinement, args.facts)
        if run and landlock and args.command not in OPERATOR and pol.values["confinement"] != "none":
            confine.stop_leftover_scopes(pol.root)
            test = confine.self_test(pol)
            confinement += f", self-test {'passed' if test.ok else 'failed'}"
            if not test.ok:
                failed = ", ".join(check for check, ok in test.checks.items() if not ok)
                raise LedgerStop(f"confinement self-test failed (label {test.label}): {failed}")
        if run:
            _fresh_state(pol.root, run)
        args.run_dir, args.self_test = run, test  # test: the run's own self-test, if one ran
        code = args.run(pol, args)
        if run:
            _report(pol, run, name, f"exit {code}", confinement, args.facts)
        return code
    except LedgerStop as stop:
        reason = str(stop)
    except Exception as error:
        traceback.print_exc()
        reason = f"{type(error).__name__}: {error}"
    print(f"ledger {name}: stopped: {reason}", file=sys.stderr)
    if run:
        _report(pol, run, name, f"stopped: {reason}", confinement, args.facts)
    return 2
