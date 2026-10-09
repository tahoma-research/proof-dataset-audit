"""The date-free command, `ledger run`: the published sample re-executed from the published recipe, or one pair of it,
in a run directory of its own, through the same code the units call. It decides nothing by the date, reading neither
D+0 nor the published progress, and takes nothing from the published records; its published inputs are
results/summary.json and results/withdrawals.jsonl, and once its own records are made it compares them with the
published results/records.jsonl.
One environment at a time: the pin's toolchain, the release, the redraw, the pin tree and every pin leg, the
aggregate's build and replay, then the legacy toolchain, tree and legs; then its own records, whose canonical-subset
hash against the published one is proof 4b's verdict."""

import dataclasses
import hashlib
import json
import os
import shutil
import sys
from collections import Counter
from datetime import date
from pathlib import Path

from ledger import (aggregate, assemble, classify, confine, devoverlay, envbuild, frame, ingest, legs, probes,
                    progress, records, report, sample)
from ledger.types import LedgerStop, write_atomic

NEEDS_DECLARED = 3  # the exit of `run --pair` whose class needs the declared environment
MACHINE = {"timed-out", "resource-exhausted"}  # classes that turn on the machine's time and memory as well as the pair


def _own(pol, consts, name: str):
    """The run's own root and constants: ./stranger-run/ under the container's policy, made afresh, or
    <root>/run-<name>/ under the operator's; its own elan binary and TMPDIR, the published gate lines as its gate
    file's first and the published withdrawals as its own. Where the development overlay is in force, the root takes
    the overlay, and the pairs its header."""
    root, elan = pol.root / ("stranger-run" if pol.kind == "container" else f"run-{name}"), probes.elan_binary(pol.root)
    if root.exists():
        shutil.rmtree(root)
    for directory in ("elan/bin", "gates", "results", "work", "xdg-cache", f"tmp/{name}"):
        (root / directory).mkdir(parents=True)
    shutil.copy2(elan, root / "elan/bin")
    for rel in ("gates/GATES.md", "results/withdrawals.jsonl"):
        if (consts.repo / rel).exists():
            shutil.copy(consts.repo / rel, root / rel)
    os.environ["TMPDIR"] = str(root / "tmp" / name)
    if overlay := devoverlay.load(pol):
        shutil.copy(pol.root / devoverlay.FILE, root)
        os.environ["LEDGER_DEV_ROOT"] = str(root)
        consts = dataclasses.replace(consts, published=consts.published | {
            "assembly": consts.published["assembly"] | {"header": overlay.header}})
    own = dataclasses.replace(pol, root=root, values={k: v for k, v in pol.values.items() if k != "public_tree"})
    return own, consts


def _outcomes(prog: progress.Progress, results: Path, pair: dict) -> dict[str, str]:
    """The outcome of each leg the pair has, by environment."""
    return {env: json.loads((results / state["leg"]).read_text())["outcome"]
            for env, state in prog.data["legs"][pair["pair_sha256"]].items()}


def run(pol, consts, run_dir: Path, facts: dict, *, pair: str | None = None, with_legacy: bool = False) -> int:
    """Re-execute the sample, or with `pair`, a pair_id or pair digest, that pair at the pin alone, under its own root
    (see _own), and print the verdict; `facts` gathers what the run report says. The redraw must be the published
    sample. A pair whose pin outcome leaves its class to the declared environment prints so and returns 3, unless
    `with_legacy`, which runs its legacy leg too where the legacy environment stands. The full run, where the disk
    holds one environment's tree at a time, deletes the pin's before building the legacy one; it prints the canonical
    subset hash of its own records beside the published one, then `4b: EQUAL` exactly when they are equal, and after
    `4b: DIFFERENT` a line of its own when the published records differ from its own only in pairs MACHINE on one
    side, or when they cannot be compared. Under the
    operator's policy, however it ends, everything under its root is deleted but results/records.jsonl, a symlink
    as a link, never its target, and an entry that cannot be deleted named on stderr; its report is in `run_dir`."""
    summary = json.loads((consts.repo / "results/summary.json").read_text())
    pol, consts = _own(pol, consts, run_dir.name)
    try:
        return _run(pol, consts, summary, run_dir, facts, pair, with_legacy)
    finally:
        if pol.kind == "operator":
            results = pol.root / "results"
            for path in [*pol.root.iterdir(), *results.iterdir()]:
                if path not in (results, results / "records.jsonl"):
                    try:
                        shutil.rmtree(path) if path.is_dir() and not path.is_symlink() else path.unlink()
                    except OSError as error:  # the rest is still deleted, and the run's own outcome stands
                        print(f"ledger run: not deleted: {error}", file=sys.stderr)


def _run(pol, consts, summary: dict, run_dir: Path, facts: dict, pair: str | None, with_legacy: bool) -> int:
    work, results, logs = pol.root / "work", pol.root / "results", run_dir / "logs"
    logs.mkdir()
    probes.install_toolchain(pol, consts, "pin", logs)
    ingest.write(ingest.parse(ingest.fetch(consts, pol), consts.published["assembly"]["suffix_regex"]), work)
    built = frame.build(work / "entries.jsonl", consts)
    frame.write(built, work)
    if (drawn := sample.write(sample.draw(built, consts.published), work)) != summary["sample_sha256"]:
        raise LedgerStop(f"the redraw is sample {drawn}, not the published sample {summary['sample_sha256']}")
    assemble.write_pairs(json.loads((work / "sample.json").read_text()), built, consts.published["assembly"], work)
    pairs = [json.loads(line) for line in (work / "assembled.jsonl").read_text().splitlines()]
    if pair and not (pairs := [p for p in pairs if pair in (p["pair_id"], p["pair_sha256"])]):
        raise LedgerStop(f"{pair} is not a pair of the sample")
    tree = consts.tree("pin")
    envbuild.fetch(pol, consts, logs, tree)
    envbuild.build(pol, consts, logs, tree)
    legs.complete(pin := legs.prepare(pol, consts, work, results, logs, ("pin",)), pairs)
    facts |= legs.identity(pin)
    standing = consts.published["status"]["legacy"] != "environment-unavailable"
    if pair:
        outcome = _outcomes(pin.progress, results, pairs[0])["pin"]
        print(f"pair_sha256 {pairs[0]['pair_sha256']}\npin outcome {outcome}")
        if outcome in classify.FAILS and standing and not with_legacy:
            facts |= {"attempted": "1 pair", "outcomes": Counter([outcome])}
            print("class needs the declared environment")
            return NEEDS_DECLARED
    else:
        aggregate.check(pin, pairs, date.today())
    if standing and (with_legacy or not pair):
        mount = pol.values["disk_floor_mount"] if pol.kind == "operator" else pol.root
        if confine.free_gb(mount) - pol.values["disk_floor_gb"] < consts.published["budgets"]["legacy_env_gb"]:
            shutil.rmtree(pol.root / "env" / tree)
        probes.install_toolchain(pol, consts, "legacy", logs)
        envbuild.fetch(pol, consts, logs, "legacy")
        envbuild.build(pol, consts, logs, "legacy")
        legs.complete(legacy := legs.prepare(pol, consts, work, results, logs, ("legacy",)), pairs)
        facts |= legs.identity(pin, legacy)
    prog = progress.load(results / "progress.json", pin.progress.data["sample_sha256"])
    if pair:
        found = _outcomes(prog, results, pairs[0])
        cls = classify.derive(found["pin"], found.get("legacy"), None, None,
                              "standing" if "legacy" in found else "unavailable")
        facts |= {"attempted": "1 pair", "outcomes": Counter(found.values()),
                  "classes": Counter([(cls, records.legs_text(found))])}
        print(f"class {cls}")
        return 0
    made = records.build(json.loads((work / "sample.json").read_text()), pairs, prog, results,
                         classify.load(consts.repo, consts), consts)
    data = records.dump(made)
    write_atomic(results / "records.jsonl", data)
    mine, published = report.canonical_subset(made), summary["canonical_subset_sha256"]
    facts |= {"attempted": f"{len(made)} pairs",
              "classes": Counter((r["class"], records.legs_text({env: leg["outcome"] for env, leg in r["legs"].items()
                                                                 if leg}, r["class"], r["overrides"])) for r in made),
              "outcomes": Counter(leg["outcome"] for r in made for leg in r["legs"].values() if leg)}
    print(f"records.jsonl sha256:{hashlib.sha256(data).hexdigest()} (its timings and code commit differ between "
          f"any two runs: for information)\ncanonical subset {mine}\npublished canonical subset {published}\n"
          f"4b: {'EQUAL' if mine == published else 'DIFFERENT'}")
    if mine != published:
        try:
            if _machine_only(made, consts.repo):
                print("4b: only in timed-out or resource-exhausted classes, which turn on the machine's time and memory")
        except (OSError, ValueError, LookupError, TypeError) as e:
            print(f"4b: the published records.jsonl cannot be compared with this run's: {type(e).__name__}: {e}")
    return 0


def _machine_only(made: list[dict], repo: Path) -> bool:
    """Whether every pair whose class or axiom list differs between the run's own records and the published
    records.jsonl is MACHINE on one side, and is in both."""
    if not (path := repo / "results/records.jsonl").exists():
        return False
    ours, theirs = ({sha: rest for sha, *rest in report.subset(recs)}
                    for recs in (made, [json.loads(line) for line in path.read_text().splitlines()]))
    differ = {sha for sha in ours.keys() | theirs.keys() if ours.get(sha) != theirs.get(sha)}
    return bool(differ) and all(sha in ours and sha in theirs and MACHINE & {ours[sha][0], theirs[sha][0]}
                                for sha in differ)
