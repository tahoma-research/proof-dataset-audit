"""The D+7 probe: six conditions, each met or not with its evidence, all met before any Mathlib build starts; the
install step, the one call that writes a toolchain directory; and the D+14 probes of the legacy environment, its
upstream cache and its axiom collector, before its build is attempted."""

import json
import os
import shutil
import time
import tomllib
from datetime import date
from pathlib import Path
from typing import Literal

from ledger import REPO, aggregate, confine, envbuild, fixtures, frame, gatefile, ingest, sample
from ledger.types import Env, LedgerStop

LIMIT_S = 3600  # any one probe call; a toolchain download is the longest
REQUIREMENTS = REPO / "requirements-dev.txt"  # the venv's test runner, every package pinned by wheel hash
STORAGE_CONF = "containers/storage.conf"  # podman's own storage configuration, beneath its config directory
TOY = "Toy.Entry"
FRAME_FLOOR = 200  # below it the source is swapped for the named alternate
D14_LINE_S = 4 * 3600  # the legacy cache probe and collector, and the proof-1b timing
CACHE_MODULE = "Mathlib/Logic/Basic.lean"  # a low layer of the declared Mathlib: its cache and its imports


def _fresh(path: Path) -> Path:
    if path.exists():
        shutil.rmtree(path)
    path.mkdir(parents=True)
    return path


def _alone(home: Path, log: Path) -> dict:
    """The arguments of a call that may write `home` alone, which is also its HOME, TMPDIR and ELAN_HOME."""
    return {"cwd": home, "writes": [home], "timeout_s": LIMIT_S, "log": log,
            "env": {"PATH": "/usr/bin:/bin", "HOME": str(home), "TMPDIR": str(home), "ELAN_HOME": str(home)}}


def _ok(proc: confine.Proc, what: str) -> str:
    """The call's output; stop unless it exited 0."""
    if proc.exit != 0:
        last = proc.output.strip().splitlines()[-1:]
        raise LedgerStop(f"{what} exited {proc.exit} (killed {proc.killed}): {' '.join(last)}")
    return proc.output


def elan_binary(root: Path) -> Path:
    """<root>/elan/bin/elan; stops where it is missing."""
    if not (elan := root / "elan/bin/elan").is_file():
        raise LedgerStop(f"{elan} is missing: elan is placed at provisioning, and nothing in the pipeline installs it")
    return elan


def install_toolchain(pol, consts, env: Env | Literal["venv"], logs: Path) -> str:
    """The install step, with network; returns the evidence. "venv": a fresh project venv holding the hash-pinned
    test runner. An environment: elan installs the toolchain its recipe names into a fresh staging directory, the
    only path the call may write; the legacy's first resolves the declared Mathlib tag, writing nothing, and stops
    unless it names the commit the recipe pins. The staged toolchain's digest is recorded, and must equal one
    already recorded under its name, and the toolchain is then moved under elan/toolchains, replacing any earlier
    install, so that no other call writes a toolchain directory."""
    if env == "venv":
        venv = _fresh(pol.root / "venv")
        _ok(confine.run([confine.PY, "-m", "venv", str(venv)], **_alone(venv, logs / "venv.log")), "python -m venv")
        _ok(confine.run([str(venv / "bin/python"), "-m", "pip", "install", "--no-cache-dir", "--only-binary", ":all:",
                         "--require-hashes", "-r", str(REQUIREMENTS)], net=True, **_alone(venv, logs / "pip.log")),
            "pip install")
        pinned = [line.split()[0] for line in REQUIREMENTS.read_text().splitlines() if line and line[0] != "#"]
        return f"venv with {', '.join(pinned)}"
    elan = elan_binary(pol.root)
    evidence = []
    if env == "legacy":
        tag, ref = consts.source["declared"]["mathlib"], f"refs/tags/{consts.source['declared']['mathlib']}"
        packages = json.loads((consts.repo / "recipe/legacy/lake-manifest.json").read_text())["packages"]
        mathlib = next(p for p in packages if p["name"] == "mathlib")
        tmp = Path(os.environ["TMPDIR"])
        listed = _ok(confine.run([confine.GIT, "ls-remote", mathlib["url"], ref, ref + "^{}"], cwd=tmp, writes=[],
                                 net=True, timeout_s=LIMIT_S, log=logs / "mathlib-tag.log",
                                 env={"PATH": "/usr/bin:/bin", "HOME": str(tmp)}), "git ls-remote")
        refs = dict(line.split("\t")[::-1] for line in listed.splitlines() if "\t" in line)
        commit = refs.get(ref + "^{}", refs.get(ref))  # an annotated tag's commit is its peeled ref
        if commit != mathlib["rev"]:
            raise LedgerStop(f"Mathlib tag {tag} resolves to {commit}, not the recipe's {mathlib['rev']}")
        evidence.append(f"Mathlib tag {tag} resolves to the recipe's commit {commit}")
    name = (consts.repo / "recipe" / env / "lean-toolchain").read_text().strip()
    final = envbuild.toolchain_dir(pol.root, name)
    staging = _fresh(pol.root / "elan/staging")
    _ok(confine.run([str(elan), "toolchain", "install", name], net=True,
                    **_alone(staging, logs / f"install-{env}.log")), f"elan toolchain install {name}")
    staged = staging / "toolchains" / final.name
    if staged.is_symlink():
        raise LedgerStop(f"elan toolchain install {name} staged {staged.relative_to(pol.root)} as a symbolic link")
    if not staged.is_dir():
        raise LedgerStop(f"elan toolchain install {name} exited 0 but staged no {staged.relative_to(pol.root)}")
    digest = envbuild.record_toolchain(pol.root, staged)
    if final.exists():
        shutil.rmtree(final)
    final.parent.mkdir(exist_ok=True)
    staged.rename(final)
    shutil.rmtree(staging)
    return "; ".join([*evidence, f"{name} installed", f"digest {digest}"])


def _installed(pol, consts, logs: Path, test: confine.ConfineReport | None) -> str:
    """(a) The pinned toolchain installed under the root, the run's own confinement self-test passed (cli.main
    stops the run on a failure; none runs without a Landlock layer), and podman's graph root an existing directory
    under the root, read from the storage.conf podman reads: podman cannot run inside the confinement, and reads
    are not confined."""
    evidence = install_toolchain(pol, consts, "pin", logs)
    evidence += (f"; confinement self-test passed (label {test.label})" if test else
                 "; no confinement self-test: the run has no Landlock layer of its own, the container stands in")
    conf = Path(os.environ.get("CONTAINERS_STORAGE_CONF") or
                Path(os.environ.get("XDG_CONFIG_HOME") or Path.home() / ".config") / STORAGE_CONF)
    try:
        graph = tomllib.loads(conf.read_text())["storage"]["graphroot"]
    except (OSError, tomllib.TOMLDecodeError, KeyError) as e:
        raise LedgerStop(f"{evidence}; podman's graph root not read from {conf}: {e!r}") from e
    resolved = Path(os.path.realpath(graph))
    if not (Path(graph).is_absolute() and resolved.is_relative_to(os.path.realpath(pol.root)) and resolved.is_dir()):
        raise LedgerStop(f"{evidence}; podman's graph root {graph!r} ({conf}) is not an existing directory under "
                         "the ledger root")
    return f"{evidence}; podman graph root {graph}"


def _toy(pol, consts, logs: Path) -> str:
    """(b) The toy project, built fresh at the pin, replays its one module with `leanchecker -v --fresh`, which
    names the module it replayed."""
    tree = pol.root / "env/toy"
    if tree.exists():
        shutil.rmtree(tree)
    shutil.copytree(REPO / "fixtures/toy", tree)
    shutil.copy(consts.repo / "recipe/pin/lean-toolchain", tree)
    toolchain = envbuild.installed_toolchain(pol.root, tree)[0]
    _ok(confine.run(**envbuild.lake(pol, consts, "pin", toolchain, tree, "build") | {"timeout_s": LIMIT_S},
                    log=logs / "toy-build.log"), "lake build of the toy")
    proc = confine.run(**envbuild.lake(pol, consts, "pin", toolchain, tree, "env", "leanchecker", "-v", "--fresh", TOY)
                       | {"timeout_s": LIMIT_S}, log=logs / "toy-env.log")
    replayed = f"replaying {TOY} with --fresh"
    if proc.exit != 0 or replayed not in proc.output.splitlines():
        raise LedgerStop(f"leanchecker exited {proc.exit} without the line `{replayed}`; see toy-env.log")
    return f"`lake --no-cache env leanchecker -v --fresh {TOY}` exited 0: {replayed}"


def _fixture_set(pol, consts, logs: Path) -> str:
    """(f) The assembler's fixture set (every test marked `assembler`) is green, run by the pytest of the project
    venv, which this condition installs."""
    evidence = install_toolchain(pol, consts, "venv", logs)
    tmp = Path(os.environ["TMPDIR"])
    proc = confine.run([str(pol.root / "venv/bin/python"), "-m", "pytest", "-p", "no:cacheprovider", "-q", "-m",
                        "assembler", "tests/unit"], cwd=REPO, writes=[tmp], timeout_s=LIMIT_S,
                       log=logs / "fixtures.log", env={"PATH": "/usr/bin:/bin", "HOME": str(tmp), "TMPDIR": str(tmp)})
    return f"{evidence}; pytest -m assembler tests/unit: {_ok(proc, 'pytest').strip().splitlines()[-1]}"


def d7(pol, consts, logs: Path, test: confine.ConfineReport | None) -> dict[str, tuple[bool, str]]:
    """The six D+7 conditions, (a) to (f), each met or not with its evidence; each is probed whatever the others
    found, and a probe's error is its own condition's evidence. `test` is the run's own confinement self-test.
    Writes the d7-frame line once the frame is measured, the d7-sample line once the sample is drawn, then the d7
    line: met, or the first unmet condition."""
    work, today, frames, found = pol.root / "work", date.today(), [], {}

    def measure() -> str:
        """(d) The frame at the pinned revision; below FRAME_FLOOR drawable pairs it is not drawn from."""
        ingest.write(ingest.parse(ingest.fetch(consts, pol), consts.published["assembly"]["suffix_regex"]), work)
        built = frame.build(work / "entries.jsonl", consts)
        frame.write(built, work)
        s, m = built.summary, built.summary["multiplier"]
        figures = {"records": s["records_total"], **{f"split_{k}": v for k, v in s["split_counts"].items()},
                   "card_lean_workbook": s["card_count_lean_workbook"],
                   "reconciliation": s["reconciliation"].rsplit(" ", 1)[1], "proof_bearing": s["proof_bearing"],
                   "proofless": s["proofless_excluded"], "drawable_pairs": s["drawable_pairs"],
                   "multiplier_mean": m["mean"], "multiplier_median": m["median"], "multiplier_max": m["max"]}
        reason = "; ".join(f"{k}={v}" for k, v in figures.items())
        small = s["drawable_pairs"] < FRAME_FLOOR
        swap = f"frame<{FRAME_FLOOR}: swap-to-alternate"
        gatefile.append(pol, "d7-frame", swap if small else "measured", "pipeline", reason, today)
        if small:
            raise LedgerStop(f"{swap}: {reason}")
        if figures["reconciliation"] != "true":
            raise LedgerStop(f"the split counts do not sum to the record count: {reason}")
        frames.append(built)
        return reason

    def draw() -> str:
        """(e) The seeded draw over that frame: the whole frame when it is below the sample size."""
        if not frames:
            raise LedgerStop("not drawn: the frame is unmet")
        drawn = sample.draw(frames[0], consts.published)
        sample.write(drawn, work)
        whole = drawn["drawable_frame_size"] < drawn["sample_size"]
        reason = f"seed={drawn['seed']}; pairs={len(drawn['draw'])}; distinct_entries={drawn['distinct_entries']}"
        gatefile.append(pol, "d7-sample", "drawn: the whole frame" if whole else "drawn", "pipeline", reason,
                        today)
        return reason + ("; the whole frame, below the sample size" if whole else "")

    probes = (lambda: _installed(pol, consts, logs, test), lambda: _toy(pol, consts, logs),
              lambda: install_toolchain(pol, consts, "legacy", logs), measure, draw,
              lambda: _fixture_set(pol, consts, logs))
    for letter, probe in zip("abcdef", probes):
        try:
            found[letter] = (True, probe())
        except Exception as error:  # the condition's evidence: printed, and the run exits 2
            found[letter] = (False, str(error) if isinstance(error, LedgerStop) else f"{type(error).__name__}: {error}")
    unmet = [k for k, (met, _) in found.items() if not met]
    gatefile.append(pol, "d7", f"unmet: ({unmet[0]})" if unmet else "met", "pipeline",
                    "; ".join(f"{k}={'unmet' if k in unmet else 'met'}" for k in found), today)
    return found


def d14_cache_probe(pol, consts, logs: Path) -> bool:
    """Whether the declared revision's upstream cache serves: env/legacy fetched fresh without it, then, with network,
    `lake exe cache get` for one low module alone, which serves when it exits 0 leaving that module's olean; the two
    within the 4-hour line. Writes legacy-cache-probe; a cache that does not serve leaves the legacy environment to
    be built from source, under the same cap (envbuild.fetch reads the line)."""
    start = time.monotonic()
    envbuild.fetch(pol, consts, logs, "legacy", timeout_s=D14_LINE_S)  # no cache: no probe line yet says it serves
    tree, toolchain = pol.root / "env/legacy", envbuild.installed_toolchain(pol.root, consts.repo / "recipe/legacy")[0]
    got = confine.run(**envbuild.lake(pol, consts, "legacy", toolchain, tree, "exe", "cache", "get", CACHE_MODULE)
                      | {"timeout_s": D14_LINE_S - (time.monotonic() - start)}, net=True, log=logs / "cache-probe.log")
    olean = (tree / ".lake/packages/mathlib/.lake/build/lib" / CACHE_MODULE).with_suffix(".olean").is_file()
    serves = got.exit == 0 and olean
    gatefile.append(pol, "legacy-cache-probe", "serves" if serves else "does not serve", "pipeline",
                    f"cache get {CACHE_MODULE}: exit={got.exit}; killed={got.killed}; olean={olean}", date.today())
    return serves


def d14_legacy_collector(pol, consts, logs: Path) -> bool:
    """Whether the legacy audit project, the collector written against the declared toolchain's API, elaborates
    there. Writes legacy-collector; one that does not makes the legacy environment environment-unavailable at once,
    in the constants and in a legacy-status line, as a trip of its cap does."""
    toolchain = envbuild.installed_toolchain(pol.root, consts.repo / "recipe/legacy")[0]
    code, executable = envbuild.build_audit(pol, consts, logs, "legacy", toolchain, D14_LINE_S)
    elaborates, reason = (code, executable) == (0, True), f"collector_exit={code}; collector_executable={executable}"
    gatefile.append(pol, "legacy-collector", "elaborates" if elaborates else "does not elaborate", "pipeline", reason,
                    date.today())
    if not elaborates:
        envbuild.set_constant(consts, "legacy", '"environment-unavailable"')
        gatefile.append(pol, "legacy-status", "environment-unavailable", "pipeline",
                        f"trigger=collector; attempts=0; {reason}; cache_probe=see the legacy-cache-probe line",
                        date.today())
    return elaborates


def d14_proof1b_timing(pol) -> float:
    """The proof-1b fixture's core-only --fresh replay, timed once: the fixture project made ready as proof 1b makes
    it, its aggregate over every fixture pair, the plant's included, built, then replayed under /usr/bin/time -v,
    the two within the 4-hour line. Returns the replay's wall-clock, a rejection of the plant included, or 4 hours
    when the run reaches the line; any other end gives no figure and stops."""
    with fixtures.tmpdir(pol):
        if isinstance(made := fixtures.project(pol, "timing"), str):
            raise LedgerStop(made)
        run, pairs = made
        (run.pol.root / "env/proof1b" / aggregate.BUILD).mkdir(parents=True)  # the build writes only beneath it
        aggregate.write_membership(run.results, [pair["pair_id"] for pair in pairs])
        start, step = time.monotonic(), "build"
        proc = aggregate.build(run, aggregate.text(run, pairs)[0], D14_LINE_S, "timing-")
        if proc.exit == 0:
            step = "replay"
            proc = aggregate.replay(run, D14_LINE_S - (time.monotonic() - start), "timing-")[0]
            if not proc.killed and aggregate.FRESH in proc.output:
                return proc.wall_s
    if proc.killed == "wall-clock":
        return D14_LINE_S
    raise LedgerStop(f"the proof-1b timing's {step} exited {proc.exit} (killed {proc.killed}); "
                     f"see aggregate-timing-{step}.log")
