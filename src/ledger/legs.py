"""Legs: one environment's check of one pair. The compile, then at the pin the pair's own replay, then the axiom
audit, each started through confine.run in the environment's tree under the per-pair wall-clock limit and the
leg memory ceiling, the compile writing only the pair's own scratch directory and the replay and audit nothing;
the outcome from the decision table; one result file per attempt. And the walks over the draw that run legs:
pass 1 and the D+14 serial pilot, both resumable across runs."""

import contextlib
import dataclasses
import hashlib
import json
import math
import os
import re
import shutil
import stat
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

from ledger import REPO, classify, confine, constants, devoverlay, diagnostics, envbuild, preflight, progress
from ledger.types import Digest, LedgerStop, canonical, write_atomic

STEPS = {"pin": 3, "legacy": 2}  # compile, replay (the pin's alone) and audit, each under the per-pair limit
PILOT_PAIRS, PILOT_LINE_S = 50, 25 * 3600
REJECTED = re.compile(r"while replaying declaration '(.+)':")  # to the line's final ':, so primed names are whole
MAX_RSS = re.compile(r"Maximum resident set size \(kbytes\): (\d+)")


@dataclass(frozen=True)
class Tree:
    """An environment's tree as its passed build left it."""
    name: str  # env/<name>: pin, pin-seeded or legacy
    toolchain: Path
    audit: Path  # the ledger-audit its passed build built
    out: str  # the root package's output root, relative to the tree: the build report's lean_path_root
    recipe_id: Digest
    provenance: str | None  # the pin's: from-source, or cache-seeded under the stop-loss


@dataclass(frozen=True)
class Run:
    """What every leg of one run shares, read once as the run starts."""
    pol: object
    consts: object
    work: Path  # sample.json and pairs/<pair_id>.lean
    results: Path  # progress.json and legs/
    logs: Path  # where no call writes
    progress: progress.Progress
    table: list
    trees: dict  # env -> Tree: the environments whose legs this run takes
    workers: int
    code_commit: str
    dev_overlay: bool


def prepare(pol, consts, work: Path, results: Path, logs: Path, envs: tuple[str, ...]) -> Run:
    """Read once what the legs in `envs` share. Stops unless each environment's tree has a passed build report
    and its toolchain is the one installed, unless its audit executable is the one that build built, and unless
    the pin's tree (the stop-loss's once that is in force) still has the artifact set its build from source
    recorded: a tree changed since, by a cache download or anything else, is not an environment the pipeline
    verified."""
    trees = {}
    for env in envs:
        name = consts.tree(env)
        path, report = pol.root / "env" / name, pol.root / "measure" / f"build-{name}.json"
        if not report.exists():
            raise LedgerStop(f"env/{name} has no passed build report, so no leg runs in it")
        built = json.loads(report.read_text())
        toolchain = envbuild.installed_toolchain(pol.root, consts.repo / "recipe" / name)[0]
        if env == "pin" and envbuild.artifact_set_digest(path, toolchain) != built["artifact_set_digest"]:
            raise LedgerStop(f"env/{name}: its artifact set is not the one its passed build recorded")
        audit = pol.root / "env" / f"audit-{env}" / envbuild.AUDIT_BIN
        digest = "sha256:" + hashlib.sha256(audit.read_bytes()).hexdigest() if audit.is_file() else None
        if digest is None or digest != built.get("audit_digest"):
            raise LedgerStop(f"env/audit-{env}: ledger-audit is not the executable env/{name}'s passed build built")
        trees[env] = Tree(name, toolchain, audit, built["lean_path_root"], constants.recipe_id(consts.repo, name),
                          {"pin": "from-source", "pin-seeded": "cache-seeded"}.get(name))
    commit = confine.run(["git", "rev-parse", "HEAD"], cwd=REPO, writes=[])
    if commit.exit != 0:
        raise LedgerStop(f"the code's commit is unreadable: {commit.output.strip()}")
    (results / "legs").mkdir(parents=True, exist_ok=True)
    sample = "sha256:" + hashlib.sha256((work / "sample.json").read_bytes()).hexdigest()
    workers = preflight.headroom(envbuild.WORKER_PEAK_KB, consts.published["limits"]["memory_floor_gib"])
    return Run(pol, consts, work, results, logs, progress.load(results / "progress.json", sample),
               classify.load(consts.repo, consts), trees, workers, commit.output.strip(), devoverlay.load(pol) is not None)


def identity(*runs: Run) -> dict:
    """What a run report names of runs of legs: the code commit and each tree's recipe identifier."""
    return {"code_commit": runs[0].code_commit,
            "recipe_ids": ", ".join(f"{tree.name} {tree.recipe_id}" for run in runs for tree in run.trees.values())}


def _regular(path: Path) -> bool:
    """Whether `path` is a regular file itself, not a link, FIFO or directory: the pair's scratch directory holds
    whatever its compile left there, an unreadable directory included."""
    try:
        return stat.S_ISREG(os.lstat(path).st_mode)
    except OSError:
        return False


class _PairMade(Exception):
    """An error in reading what the pair's own code made: its leg is harness, while any other error stops the run."""


@contextlib.contextmanager
def _pair_made():
    try:
        yield
    except LedgerStop:
        raise
    except Exception as error:
        raise _PairMade(f"{type(error).__name__}: {error}") from error


def _check(run: Run, env: str, name: str, stem: str, rss: bool, leg: dict, bypass: bool) -> None:
    """Compile, replay at the pin unless `bypass`, and audit the pair `name` in env's tree, each step only after the
    last ended with exit 0, filling in the leg result. The compile writes only the attempt's own fresh scratch
    directory, from which its olean and ilean are moved into the tree, each only if it is a regular file (otherwise
    the compile's output_missing), and of its timing report at most the first 64 KiB is read; the replay and audit write
    nothing, and none of the three changes a file's mode, owner, timestamps or extended attributes, so no pair's
    code can change another pair's olean; nor reads anything but the system's, the toolchain, the tree, the audit
    executable and the attempt's scratch directory."""
    root, tree, limits = run.pol.root, run.trees[env], run.consts.published["limits"]
    path = root / "env" / tree.name
    out = path / tree.out / "Pairs"
    scratch = envbuild.run_tmp(root) / stem
    scratch.mkdir()
    (path / "Pairs").mkdir(exist_ok=True)
    shutil.copy(run.work / "pairs" / f"{name}.lean", path / "Pairs")
    out.mkdir(parents=True, exist_ok=True)

    def step(label: str, writes: list[Path], *cmd: str) -> tuple[dict, str]:
        call = envbuild.lake(run.pol, run.consts, tree.name, tree.toolchain, path, "env", *cmd)
        proc = confine.run(**call | {"writes": writes, "timeout_s": limits["per_pair_wall_clock_s"]},
                           no_meta=True, reads=[tree.toolchain, path, tree.audit],
                           memory_max_mb=limits["leg_memory_max_mb"],
                           unit_name=confine.scope_name(root, f"{stem}-{label}".replace(".", "-")),
                           log=run.logs / f"{stem}.{label}.log")
        with _pair_made():
            text, residue = diagnostics.rewrite_paths(proc.output, [path, root, REPO])
        leg["path_residue"] |= residue
        return ({"exit": proc.exit, "killed": proc.killed, "oom_kill": proc.oom_kill or 0,
                 "wall_s": round(proc.wall_s, 3), "peak_mem_kb": proc.peak_mem_kb,
                 "output_truncated": proc.output_truncated}, text)

    timing = scratch / "time"
    done, text = step("compile", [scratch], *(["/usr/bin/time", "-v", "-o", str(timing)] if rss else []),
                      "lean", "--root=.", "-o", f"{scratch}/{name}.olean", "-i", f"{scratch}/{name}.ilean",
                      f"Pairs/{name}.lean")
    leg["compile"] = done | {"peak_mem_source": "largest-process" if run.pol.kind == "container" else "cgroup",
                             "diagnostics": text, "output_missing": False}
    if rss:  # /usr/bin/time writes nothing when it is killed with the compile
        leg["compile"]["max_rss_kb"] = None
        try:
            if _regular(timing):
                with open(timing, "rb") as report:  # its first 64 KiB: the pair may have grown it
                    found = MAX_RSS.search(report.read(64 * 1024).decode(errors="replace"))
                leg["compile"]["max_rss_kb"] = found and int(found[1])
        except (OSError, ValueError):  # the pair recreated it unreadable, or wrote a number too long for int()
            pass  # no maximum resident set
    if done["exit"] or done["killed"]:
        return
    outputs = [scratch / f"{name}.{ext}" for ext in ("olean", "ilean")]
    if not all(map(_regular, outputs)):
        leg["compile"]["output_missing"] = True
        return
    for output in outputs:
        shutil.move(output, out / output.name)
    if env == "pin" and not bypass:
        done, text = step("replay", [], "leanchecker", "-v", f"Pairs.{name}")
        found = REJECTED.search(text)
        leg["replay"] = done | {"rejected_constant": found and found[1], "output": text}
        if done["exit"] or done["killed"]:
            return
    done, text = step("audit", [], str(tree.audit), "audit", "--module", f"Pairs.{name}", "--decl", name)
    lines = text.splitlines()
    with _pair_made():
        decls = [json.loads(line) for line in lines if line.startswith("{")]
        disagreement = classify.audit_flags(decls, run.consts.published["audit"]["allowlist"])[2]
    leg["audit"] = done | {"stderr": "\n".join(line for line in lines if not line.startswith("{")), "decls": decls,
                           "disagreement": disagreement}


def _headed(run: Run, pair: dict) -> bool:
    """Whether the pair's text begins with the run's header, the recipe's or the dev overlay's, byte for byte."""
    overlay = devoverlay.load(run.pol)
    headers = [run.consts.published["assembly"]["header"].encode(), *([overlay.header.encode()] if overlay else [])]
    with open(run.work / "pairs" / f"{pair['pair_id']}.lean", "rb") as text:
        start = text.read(max(map(len, headers)))
    return any(start.startswith(header) for header in headers)


def run_leg(run: Run, pair: dict, env: str, rss: bool = False, bypass: bool = False) -> dict:
    """One attempt at one leg of `pair`, a line of work/assembled.jsonl, counted before any command runs. A
    refused pair's outcome comes from its refusal; any other is compiled, replayed at the pin and audited, and
    its outcome read from the table. An error in reading what the pair's code made (its output, timing report and
    audit lines, and the facts and outcome read from them) makes the leg harness, terminal, the error its
    diagnostic; any other error, the orchestrator's own setup, calls and moves, stops the run. With `rss`,
    /usr/bin/time -v also measures the compile's largest process.
    The result is written to results/legs/<pair hex>.<env>.<attempt>.json, and then the progress file points
    at it: terminal unless the outcome is retryable and attempts remain, counted from the leg's last reopening. A leg
    at the bound runs no command: its latest result file since then is made terminal, or, if every attempt since was
    killed before it had an outcome, it is written terminal as unclassified.
    `bypass`, which skips the per-pair replay, is honoured only in a fixture run, whose root is fixtures-run/ under
    its policy's root; and a pair's text must begin with the run's header, the recipe's or the dev overlay's, so no
    pair under any other header, a core-only one included, runs in a real run. Either refused stops the run before
    an attempt is counted."""
    fixture = run.pol.root == Path(run.pol.values["root"]).absolute() / "fixtures-run"
    if bypass and not fixture or pair["refusal"] is None and not _headed(run, pair):
        raise LedgerStop(f"{pair['pair_id']}: a real run refuses the per-pair replay bypass and any other header")
    sha, limits = pair["pair_sha256"], run.consts.published["limits"]
    base = run.progress.reopened_at(sha, env)
    killed = run.progress.attempts(sha, env) - base >= limits["attempt_bound"]
    numbered = {int(path.stem.rsplit(".", 1)[1]): path for path in (run.results / "legs").glob(
        f"{sha.removeprefix('sha256:')}.{env}.*.json")} if killed else {}
    last = numbered[max(numbered)] if max(numbered, default=0) > base else None
    if last:
        leg = json.loads(last.read_text()) | {"terminal": True}
        write_atomic(last, canonical(leg))
        run.progress.finish(sha, env, f"legs/{last.name}", True)
        return leg
    attempt = run.progress.attempts(sha, env) if killed else run.progress.start_attempt(sha, env)
    tree = run.trees[env]
    stem = f"{sha.removeprefix('sha256:')}.{env}.{attempt}"
    leg = {"schema": "leg/1", "pair_id": pair["pair_id"], "pair_sha256": sha, "env": env, "recipe_id": tree.recipe_id,
           "code_commit": run.code_commit, "classifier_version": run.consts.published["classifier"]["version"],
           "attempt": attempt, "provenance": tree.provenance,
           "limits": {"wall_clock_limit_s": limits["per_pair_wall_clock_s"],
                      "memory_ceiling_mb": limits["leg_memory_max_mb"], "worker_count": run.workers,
                      "heartbeats": run.consts.published["assembly"]["max_heartbeats"]},
           "refusal": pair["refusal"], "path_residue": False, "compile": None, "replay": None, "audit": None,
           "dev_overlay": run.dev_overlay}
    if killed:
        leg |= classify.KILLED
    else:
        try:
            if pair["refusal"] is None:
                _check(run, env, pair["pair_id"], stem, rss, leg, bypass)
            with _pair_made():
                leg["outcome"], leg["table_row"] = classify.leg_outcome(
                    classify.facts_of(leg, run.consts.published["audit"]["allowlist"]), run.table)
        except _PairMade as error:  # this leg's own result: no single pair stops the run
            text, residue = diagnostics.rewrite_paths(str(error),
                                                      [run.pol.root / "env" / tree.name, run.pol.root, REPO])
            leg |= {"outcome": "harness", "table_row": None, "diagnostic": text,
                    "path_residue": leg["path_residue"] or residue}
        except LedgerStop:
            raise
        except Exception as error:  # the orchestrator's own work failed, which every pair would meet: the run stops
            raise LedgerStop(f"{stem}: {type(error).__name__}: {error}") from error
    leg["terminal"] = leg["outcome"] not in classify.RETRYABLE or attempt - base >= limits["attempt_bound"]
    write_atomic(run.results / "legs" / f"{stem}.json", canonical(leg))
    run.progress.finish(sha, env, f"legs/{stem}.json", leg["terminal"])
    return leg


def pass1(run: Run, pairs: list[dict], ceiling_s: float, clock=time.monotonic) -> str | None:
    """Pass 1, resumed from the progress file: the pairs in draw order (the first cut_n once a cut is set), each
    with every leg it still needs among the run's environments, pin first, one pair per worker. A pair starts
    only while the time elapsed plus its worst case, the per-pair limit for every step its legs still take,
    fits the ceiling; otherwise nothing more starts, the pairs under way finish, and the cause is returned. Once a
    leg has raised nothing more starts either, and the first exception is raised once every pair started has
    finished."""
    limits = run.consts.published["limits"]
    queue = run.progress.pending_pairs(pairs[:run.consts.published["sampling"]["cut_n"] or None], list(run.trees))
    start, free, failed, started, truncated = clock(), threading.Semaphore(run.workers), threading.Event(), [], None

    def finished(future) -> None:
        if future.exception():
            failed.set()
        free.release()
    with ThreadPoolExecutor(run.workers) as pool:
        for pair, envs in queue:
            free.acquire()
            if failed.is_set():
                break
            worst = limits["per_pair_wall_clock_s"] * sum(STEPS[env] for env in envs)
            if (elapsed := clock() - start) + worst > ceiling_s:
                truncated = (f"run-truncated: {elapsed:.0f} s elapsed and {pair['pair_id']}'s worst case of {worst} s "
                             f"would pass the {ceiling_s:.0f} s ceiling")
                break
            started.append(pool.submit(lambda pair=pair, envs=envs: [run_leg(run, pair, env) for env in envs]))
            started[-1].add_done_callback(finished)
    for future in started:
        future.result()
    return truncated


def complete(run: Run, pairs: list[dict], deadline: float = math.inf) -> str | None:
    """Pass 1 over `pairs` until every leg is terminal, a retryable one retried to the attempt bound; or, once no pair
    fits what remains before `deadline` (a time.monotonic()), pass 1's cause, returned."""
    while run.progress.pending_pairs(pairs, list(run.trees)):
        if truncated := pass1(run, pairs, deadline - time.monotonic()):
            return truncated
    return None


def serial_pilot(run: Run, pairs: list[dict]) -> list[dict]:
    """The D+14 serial pilot: the first 50 pairs of the draw, one at a time, the pin leg alone, each compile also
    measured by /usr/bin/time -v. It stops at the pair boundary where the compile and replay wall-clocks summed
    reach the 25-hour line. The pairs attempted, which are the pilot, and the sum are recorded in the progress
    file, and a restarted pilot resumes from them, past every pair whose pin leg is terminal."""
    run, legs = dataclasses.replace(run, workers=1), []
    pilot = run.progress.data["d14_pilot"]
    attempted, spent = list(pilot["attempted"]), pilot["spent_s"]
    for pair, _ in run.progress.pending_pairs(pairs[:PILOT_PAIRS], ["pin"]):
        if spent >= PILOT_LINE_S:
            break
        legs.append(leg := run_leg(run, pair, "pin", rss=True))
        if leg["attempt"] == run.progress.attempts(pair["pair_sha256"], "pin"):  # not an earlier attempt's, counted
            spent += sum(leg[step]["wall_s"] for step in ("compile", "replay") if leg[step])
        if pair["pair_sha256"] not in attempted:
            attempted.append(pair["pair_sha256"])
        run.progress.pilot(attempted, spent, spent >= PILOT_LINE_S)
    return legs


def reclassify(prog: progress.Progress, results: Path, table: list, consts) -> list[str]:
    """`report --reclassify`: derive the outcome of every leg the progress file points at again, from the facts
    its result stores, with `table`; a leg killed on every attempt has no facts and keeps its outcome. A changed
    leg's result is rewritten with its new outcome, row and terminal state, never terminal while the result is from
    before the leg was reopened, and the progress file follows, saved once, also when a leg stops the walk. Returns
    the changed results, relative to `results`."""
    changed, bound, allowlist = [], consts.published["limits"]["attempt_bound"], consts.published["audit"]["allowlist"]
    try:
        for envs in prog.data["legs"].values():
            for state in envs.values():
                leg = json.loads((results / state["leg"]).read_text()) if state["leg"] else None
                if leg and (found := classify.rederive(leg, table, allowlist)) != (leg["outcome"], leg["table_row"]):
                    leg["outcome"], leg["table_row"] = found
                    since = leg["attempt"] - state.get("reopened_at", 0)  # 0 or less: awaiting its re-run
                    leg["terminal"] = since > 0 and (leg["outcome"] not in classify.RETRYABLE or since >= bound)
                    write_atomic(results / state["leg"], canonical(leg))
                    state["terminal"] = leg["terminal"]
                    changed.append(state["leg"])
    finally:
        if changed:
            prog.save()
    return changed
