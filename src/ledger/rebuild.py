"""The D+30 rebuild: the pinned environment built again from scratch in env/rebuild, within 1.5 times the wall-clock of
the build D+14 measured, its artifact set compared with the one that build recorded, and the attempted D+14 pilot
pairs' pin legs run again against it, whose outcome hash decides the attempt. A divergent artifact set with matching
outcomes passes, with a note that characterises the divergence and establishes nothing. Three failed attempts are not
a kill."""

import dataclasses
import json
import shutil
import time
from datetime import date
from pathlib import Path

from ledger import envbuild, gatefile, legs, progress, records
from ledger.types import LedgerStop, write_atomic

BUDGET = 1.5  # the build's allowance, in D+14 build wall-clocks
MARGIN_S = 60  # how far before systemd's bound the attempt's own deadline falls: time to hash, record and write


def allowance(pol, consts, prog: progress.Progress) -> float:
    """1.5 times the D+14 build's wall-clock, plus the 50-pair outcome check's allowance: the attempted D+14 pilot
    pairs' pin-leg compile, replay and audit wall-clocks, each leg's from its latest result where it has run since it
    was last reopened (so a leg the freeze reopened counts its re-run's), and otherwise, a leg reopened and not yet run
    again, the frozen per-pair limit itself, once."""
    built = json.loads((pol.root / "measure" / f"build-{consts.tree('pin')}.json").read_text())
    total, limit = BUDGET * built["wall_s"], consts.published["limits"]["per_pair_wall_clock_s"]
    for pair in prog.data["d14_pilot"]["attempted"]:
        if prog.attempts(pair, "pin") > prog.reopened_at(pair, "pin"):
            leg = json.loads((pol.root / "results" / prog.data["legs"][pair]["pin"]["leg"]).read_text())
            total += sum(leg[step]["wall_s"] for step in ("compile", "replay", "audit") if leg[step])
        else:
            total += limit
    return total


def _outcomes(prog: progress.Progress, results: Path, pairs: list[str]) -> str:
    """The outcome hash of `pairs`: each one's pin leg outcome, before any aggregate override, and axiom list."""
    found = [json.loads((results / prog.data["legs"][pair]["pin"]["leg"]).read_text()) for pair in pairs]
    return records.subset_sha256([(leg["pair_sha256"], leg["outcome"], records.axioms(leg["pair_id"], leg["audit"]))
                                  for leg in found])


def _note(pol, consts, env: str, n: int, d14: str, rebuilt: str) -> tuple[Path, int]:
    """measure/d30/divergence-<n>.md: the package oleans that differ between the D+14 tree and the rebuilt one, the
    packages they belong to and the recipe inputs those packages come from. Returns its path and the count."""
    paths = envbuild.divergence(pol.root / "env" / env, pol.root / "env/rebuild")
    recipe = consts.repo / "recipe" / env
    manifest = {p["name"]: p for p in json.loads((recipe / "lake-manifest.json").read_text())["packages"]}
    packages = sorted({path.split("/")[2] for path in paths})
    text = "\n".join([
        f"# D+30 rebuild attempt {n}: the artifact set diverged", "",
        "This note characterises the divergence and establishes nothing: the 50-pair outcome hash decides the attempt.",
        "", f"- artifact set recorded at D+14: {d14}", f"- artifact set rebuilt: {rebuilt}",
        f"- toolchain: {(recipe / 'lean-toolchain').read_text().strip()}", "", f"## Packages ({len(packages)})", "",
        *(f"- {name}: " + (f"{p['url']} at {p['rev']}" if (p := manifest.get(name)) else "not in the recipe's manifest")
          for name in packages), "", f"## Diverging package oleans ({len(paths)})", "",
        *(f"- {path}" for path in paths), ""])
    (note := pol.root / "measure/d30" / f"divergence-{n}.md").parent.mkdir(parents=True, exist_ok=True)
    write_atomic(note, text.encode())
    return note, len(paths)


def attempt(main: legs.Run, today: date, start: float) -> str:
    """One D+30 attempt over `main`, legs.prepare's run of the pin, numbered after those the progress file records and
    counted there as failed as its fetch starts. Its deadline is its unit's: `start`, the time.monotonic() the unit
    started, plus the allowance, MARGIN_S before systemd's. The build part, 1.5 times the D+14 build's wall-clock from
    `start`, holds the lock wait, the preflight, the fetch and both builds: env/rebuild fetched and built from scratch
    with the pin's recipe, or the stop-loss's while it is in force (envbuild refuses a non-empty Lake cache). Its
    artifact-set digest is compared with D+14's, a divergence note written where they differ; then, before the
    deadline, the attempted D+14 pilot pairs' pin legs run again under the frozen constants against the rebuilt tree,
    into measure/d30/attempt-<n>/, a retryable outcome retried to the attempt bound, and their outcome hash is
    compared with the main tree's. The result: fail where anything raised, the build or the re-run not done in its
    part among the causes, or where the hashes differ; artifact-divergent-outcome-match where only the artifact sets
    do; otherwise pass. It is recorded in the progress file, then as the d30-attempt-<n> line naming its cause, with a
    d30-divergence-note line where a note was written, and an error other than the pipeline's own stop is raised
    after. Returns it."""
    pol, consts, prog, root = main.pol, main.consts, main.progress, main.pol.root
    env, note = consts.tree("pin"), None
    n = len(prog.data.get("rebuild", {}).get("attempts", [])) + 1
    d14 = json.loads((root / "measure" / f"build-{env}.json").read_text())
    built_by, deadline = start + BUDGET * d14["wall_s"], start + allowance(pol, consts, prog) - MARGIN_S
    result, reason = "fail", "the attempt was interrupted"
    prog.rebuild_attempt(n, "fail", today)
    try:
        envbuild.fetch(pol, consts, main.logs, env, "rebuild", timeout_s=built_by - time.monotonic())
        built = envbuild.build(pol, consts, main.logs, env, "rebuild", deadline=built_by)
        divergent = built.artifact_set_digest != d14["artifact_set_digest"]
        if divergent:
            note = _note(pol, consts, env, n, d14["artifact_set_digest"], built.artifact_set_digest)
        out = root / "measure/d30" / f"attempt-{n}"
        if out.exists():
            shutil.rmtree(out)
        (out / "legs").mkdir(parents=True)
        tree = dataclasses.replace(main.trees["pin"], name="rebuild", out=built.lean_path_root,
                                   audit=root / "env/audit-rebuild" / envbuild.AUDIT_BIN)
        whole = consts.published | {"sampling": consts.published["sampling"] | {"cut_n": 0}}  # every pilot pair
        rerun = dataclasses.replace(main, consts=dataclasses.replace(
            consts, published=whole, env=consts.env | {"rebuild": consts.env[env]}), results=out,
                                    progress=progress.load(out / "progress.json", prog.data["sample_sha256"]),
                                    trees={"pin": tree})
        attempted = prog.data["d14_pilot"]["attempted"]
        lines = [json.loads(line) for line in (root / "work/assembled.jsonl").read_text().splitlines()]
        if truncated := legs.complete(rerun, [pair for pair in lines if pair["pair_sha256"] in attempted], deadline):
            raise LedgerStop(f"the 50-pair re-run: {truncated}")
        kept, again = _outcomes(prog, root / "results", attempted), _outcomes(rerun.progress, out, attempted)
        result = "fail" if kept != again else "artifact-divergent-outcome-match" if divergent else "pass"
        reason = (f"build {built.wall_s:.0f} s of {BUDGET * d14['wall_s']:.0f} s; artifact set "
                  f"{'diverged' if divergent else 'matched'}; outcome hash {again} rebuilt, {kept} main tree")
    except Exception as error:  # whatever raised, the attempt failed, and its line says why
        reason = gatefile.sanitize(pol, str(error) if isinstance(error, LedgerStop) else
                                   f"{type(error).__name__}: {error}", 300)
        if not isinstance(error, LedgerStop):
            raise
    finally:
        prog.rebuild_attempt(n, result, today)
        gatefile.append(pol, f"d30-attempt-{n}", result, "pipeline", reason, today)
        if note:
            gatefile.append(pol, "d30-divergence-note", "written", "pipeline",
                            f"measure/d30/{note[0].name}: {note[1]} package oleans differ", today)
    return result
