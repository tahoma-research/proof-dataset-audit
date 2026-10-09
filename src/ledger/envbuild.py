"""Environment build. A fetch step with network creates an environment's tree fresh from the recipe; a build step
with none compiles it, and a pin build is accepted only on its artifacts: no build.barrel file, no olean older
than the start marker, and an empty Lake artifact cache beforehand. No toolchain binary runs unless the
toolchain's digest is the one its install step recorded. The numbered attempts of the one-off builds are
recorded in measure/env-attempts.json and decide the stop-loss and the legacy cap."""

import hashlib
import json
import os
import re
import shutil
import time
from dataclasses import asdict, dataclass
from datetime import date
from pathlib import Path

from ledger import confine, devoverlay, gatefile, preflight
from ledger.types import Digest, Env, LedgerStop, canonical, write_atomic

MARKER = ".ledger-build-start"
ATTEMPTS = "measure/env-attempts.json"
TOOLCHAINS = "measure/toolchains.json"  # toolchain directory name -> its digest, written by the install step
LIMIT = {"pin": 3, "legacy": 3, "pin-seeded": 1}  # numbered attempts the PRD allows
LINE_S = 24 * 3600  # one pin or stop-loss build
LEGACY_CAP_S = 36 * 3600  # summed over the legacy attempts
TARGETS = ["Mathlib", "Aesop"]
AUDIT_BIN = ".lake/build/bin/ledger-audit"  # in env/audit-<role>
WORKER_PEAK_KB = 4 * preflight.GIB_KB  # 05 § preflight: per Lake build worker, every environment, until D+14


@dataclass(frozen=True)
class BuildReport:
    exit: int
    wall_s: float
    peak_mem_kb: int | None  # the build scope's memory.peak; None under a container policy
    swap_delta_kb: int  # the host's swap in use after the build less before it
    workers: int  # LEAN_NUM_THREADS, which bounds Lake's workers (probed: Lake has no job flag)
    disk_kb: int
    olean_count: int
    artifact_set_digest: Digest
    lean_path_root: str  # the root package's LEAN_PATH entry, relative to the tree: where legs compile
    audit_digest: Digest  # the sha256 of env/audit-<role>/AUDIT_BIN as this build built it, which legs run


def _write(path: Path, value) -> None:
    path.parent.mkdir(exist_ok=True)
    write_atomic(path, canonical(value))


def _tree(root: Path, env: Env, tree: str) -> Path:
    return root / "env" / (tree if tree == "rebuild" else env)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _toolchain_lines(toolchain: Path) -> list[str]:
    """One "toolchain:<path>\t<sha256>" line per file of the toolchain directory, and "toolchain:<path>\tlink:<target>"
    per link, to a file or a directory, never followed; sorted by path: bin/ holds launchers, and the compiler,
    kernel and prelude oleans are under lib/ (04 § 11). A link that resolves outside the toolchain stops."""
    entries = {}
    for d, dirs, files in os.walk(toolchain):
        for name in dirs + files:
            path = Path(d, name)
            rel = path.relative_to(toolchain).as_posix()
            if path.is_symlink():
                if not path.resolve().is_relative_to(toolchain.resolve()):
                    raise LedgerStop(f"toolchain {toolchain.name}: {rel} links outside the toolchain")
                entries[rel] = f"link:{os.readlink(path)}"
            elif name in files:
                entries[rel] = _sha256(path)
    return [f"toolchain:{rel}\t{entries[rel]}\n" for rel in sorted(entries)]


def _digest(lines: list[str]) -> Digest:
    return "sha256:" + hashlib.sha256("".join(lines).encode()).hexdigest()


def toolchain_digest(toolchain: Path) -> Digest:
    return _digest(_toolchain_lines(toolchain))


def record_toolchain(root: Path, toolchain: Path) -> Digest:
    """The install step's record of a toolchain it installed (C5): its digest, by directory name. A digest already
    recorded under that name is the trust anchor: a different one is refused, never written over; replacing it is
    the operator's deliberate act."""
    path = root / TOOLCHAINS
    recorded = json.loads(path.read_text()) if path.exists() else {}
    digest = toolchain_digest(toolchain)
    if recorded.setdefault(toolchain.name, digest) != digest:
        raise LedgerStop(f"toolchain {toolchain.name}: this install's digest {digest} is not the one recorded, "
                         f"{recorded[toolchain.name]}; the recorded one stands until the operator removes it from "
                         f"{TOOLCHAINS}")
    _write(path, recorded)
    return digest


def toolchain_dir(root: Path, name: str) -> Path:
    """Where elan keeps the toolchain a lean-toolchain file names `name`, under the root's elan home."""
    return root / "elan/toolchains" / name.replace("/", "--").replace(":", "---")


def installed_toolchain(root: Path, source: Path,
                        verified: tuple[Path, list[str]] | None = None) -> tuple[Path, list[str]]:
    """The installed toolchain directory named by the lean-toolchain file in `source`, never a default, and its
    lines, only when its digest now is the one the install step recorded. A directory `verified` already names
    is not hashed again."""
    try:
        name = (source / "lean-toolchain").read_text().strip()
    except OSError as e:
        raise LedgerStop(f"{source.name}: no readable lean-toolchain: {e.strerror}") from e
    path = toolchain_dir(root, name)
    if not path.is_dir():
        raise LedgerStop(f"toolchain {name!r} is not installed")
    if verified and verified[0] == path:
        return verified
    recorded = json.loads((root / TOOLCHAINS).read_text()) if (root / TOOLCHAINS).exists() else {}
    if path.name not in recorded:
        raise LedgerStop(f"toolchain {name!r}: no digest recorded in {TOOLCHAINS}")
    if _digest(lines := _toolchain_lines(path)) != recorded[path.name]:
        raise LedgerStop(f"toolchain {name!r}: its digest is not the one recorded at install")
    return path, lines


def run_tmp(root: Path) -> Path:
    """The run's own tmp/<run-id>/, the TMPDIR the run set."""
    tmp = Path(os.environ.get("TMPDIR", ""))
    if tmp.parent != root / "tmp":
        raise LedgerStop(f"TMPDIR {tmp} is not a run's own directory under {root / 'tmp'}")
    return tmp


def lake(pol, consts, env: Env, toolchain: Path, cwd: Path, *args: str, workers: int | None = None) -> dict:
    """The arguments of a `confine.run` of `lake` from `toolchain` in `cwd`: the environment's flags, and a child
    environment that sends every cache directory beneath the root, scratch to the run's own tmp/<run-id>/, and
    bounds the workers; bounded by the run ceiling unless the caller replaces it."""
    root, cache, bin_, tmp = pol.root, pol.root / "xdg-cache", toolchain / "bin", run_tmp(pol.root)
    settings = consts.env[env]
    environment = {"PATH": f"{bin_}:/usr/bin:/bin", "HOME": str(root / "runtime"), "TMPDIR": str(tmp),
                   "ELAN_HOME": str(root / "elan"), "XDG_CACHE_HOME": str(cache), "LAKE_CACHE_DIR": str(cache / "lake"),
                   "MATHLIB_CACHE_DIR": str(cache / "mathlib"), **settings["env"],
                   **({"LEAN_NUM_THREADS": str(workers)} if workers else {})}
    return {"cmd": [str(bin_ / "lake"), *settings["lake_flags"], *args], "cwd": cwd, "env": environment,
            "writes": [cwd, tmp, cache], "timeout_s": consts.published["limits"]["run_ceiling_s"]}


def fetch(pol, consts, logs: Path, env: Env, tree: str = "pin", timeout_s: float | None = None) -> None:
    """With network: create the tree fresh (a fetch never runs in a tree a build wrote), copy the recipe in and
    let Lake clone every package at its manifest revision, then check each HEAD against the manifest. Where the
    recipe permits a cache, `lake exe cache get` follows, for legacy only once the D+14 probe recorded that the cache
    serves: that environment is otherwise built from source. The clone and the cache's get together have `timeout_s`,
    by default the run ceiling."""
    recipe, path = consts.repo / "recipe" / env, _tree(pol.root, env, tree)
    toolchain = installed_toolchain(pol.root, recipe)[0]
    if path.exists():
        shutil.rmtree(path)
    path.mkdir(parents=True)
    for source in recipe.iterdir():
        if source.name != "env.toml":
            shutil.copy(source, path)
    call = lake(pol, consts, env, toolchain, path, "env", "true")
    bound = timeout_s or call["timeout_s"]
    end = time.monotonic() + bound
    resolved = confine.run(**call | {"timeout_s": bound}, net=True, log=logs / f"fetch-{env}.log")
    if resolved.exit != 0:
        raise LedgerStop(f"fetch {env}: lake exited {resolved.exit}; see fetch-{env}.log")
    for package in json.loads((path / "lake-manifest.json").read_text())["packages"]:
        head = confine.run([confine.GIT, "rev-parse", "HEAD"], cwd=path / ".lake/packages" / package["name"],
                           writes=[], timeout_s=confine.GIT_CHECK_S)
        if head.exit != 0 or head.output.strip() != package["rev"]:
            raise LedgerStop(f"{package['name']}: HEAD is {head.output.strip()!r} (exit {head.exit}, killed "
                             f"{head.killed}), the manifest says {package['rev']}")
    served = env != "legacy" or ("legacy-cache-probe", "serves") in (row[1:3] for row in gatefile.rows(pol))
    if consts.env[env]["cache"] != "forbidden" and served:
        cached = confine.run(**lake(pol, consts, env, toolchain, path, "exe", "cache", "get")
                             | {"timeout_s": end - time.monotonic()}, net=True, log=logs / f"cache-{env}.log")
        if cached.exit != 0:
            raise LedgerStop(f"fetch {env}: cache get exited {cached.exit}; see cache-{env}.log")


def _oleans(top: Path):
    """Every .olean file beneath `top`, except Lake's configuration oleans (.lake/config)."""
    for directory, names, files in os.walk(top):
        names[:] = [n for n in names if n != ".git" and not (n == "config" and directory.endswith("/.lake"))]
        yield from (Path(directory, f) for f in files if f.endswith(".olean"))


def _hashes(path: Path) -> dict[str, str]:
    """sha256 of every olean of every package, by path relative to the tree. The root package's own oleans
    (the pairs, the aggregate) change every run and are not here."""
    return {o.relative_to(path).as_posix(): _sha256(o) for o in _oleans(path / ".lake/packages")}


def _artifact_lines(path: Path, toolchain_lines: list[str]) -> list[str]:
    """One "<path>\\t<sha256>" line per package olean, sorted by path, then the toolchain's lines."""
    return [f"{rel}\t{digest}\n" for rel, digest in sorted(_hashes(path).items())] + toolchain_lines


def artifact_set_digest(path: Path, toolchain: Path) -> Digest:
    return _digest(_artifact_lines(path, _toolchain_lines(toolchain)))


def divergence(first: Path, second: Path) -> list[str]:
    """The package oleans, sorted, that differ between two trees or are in only one."""
    a, b = _hashes(first), _hashes(second)
    return sorted(p for p in a.keys() | b.keys() if a.get(p) != b.get(p))


def _wipe(path: Path, whole: bool) -> None:
    """Remove every .lake/build (the root package's alone unless `whole`) and every build.barrel* beneath the
    tree, then stop unless no olean is left to be mistaken for this build's."""
    for build in list(path.glob("**/.lake/build") if whole else [path / ".lake/build"]):
        if build.exists():
            shutil.rmtree(build)
    for barrel in path.rglob("build.barrel*"):
        barrel.unlink()
    if any(_oleans(path if whole else path / ".lake/build")):
        raise LedgerStop(f"{path.name}: oleans remain after the wipe")


def _check_artifacts(path: Path, whole: bool) -> None:
    """Stop on any build.barrel* file, or any olean older than the start marker (the root package's alone
    unless `whole`: a seeded build's dependency layers come from a cache and predate it). Never reads a log."""
    marker = (path / MARKER).stat().st_mtime
    barrels = list(path.rglob("build.barrel*"))
    if barrels:
        raise LedgerStop(f"{len(barrels)} build.barrel files after the build, first {barrels[0].relative_to(path)}")
    stale = [o for o in _oleans(path if whole else path / ".lake/build") if o.stat().st_mtime < marker]
    if stale:
        raise LedgerStop(f"{len(stale)} oleans older than the start marker, first {stale[0].relative_to(path)}")


def _disk_kb(path: Path) -> int:
    return sum(os.lstat(os.path.join(d, n)).st_blocks for d, _, names in os.walk(path) for n in names) // 2


def _attempts(root: Path) -> dict:
    path = root / ATTEMPTS
    return json.loads(path.read_text()) if path.exists() else {env: [] for env in LIMIT}


def check_attempt(root: Path, consts, env: Env, tree: str, n: int | None) -> float:
    """Stop unless this build may start: a rebuild tree is the pin's (or the stop-loss's), unnumbered; numbered
    attempt `n` is the one after the last recorded, within the limit, for the stop-loss only after three failed
    pin attempts, for legacy only while the environment stands and hours of the cap remain. Returns the seconds
    the build is given: an unnumbered pin or stop-loss build the 24 h line, an unnumbered legacy build the cap's
    36 h, neither recorded."""
    if tree == "rebuild" and (env == "legacy" or n is not None):
        raise LedgerStop("a rebuild tree is built for the pin or the stop-loss, and has no numbered attempts")
    if n is None:
        return LEGACY_CAP_S if env == "legacy" else LINE_S
    done = _attempts(root)
    if n != len(done[env]) + 1 or n > LIMIT[env]:
        raise LedgerStop(f"{env}: attempt {n} is out of order, repeated or above {LIMIT[env]}")
    if env == "pin-seeded" and not (len(done["pin"]) == 3 and all(a["result"] != "ok" for a in done["pin"])):
        raise LedgerStop("stop-loss: it needs three recorded pin attempts, none ok")
    if env == "legacy" and consts.published["status"]["legacy"] == "environment-unavailable":
        raise LedgerStop("legacy: the environment is already environment-unavailable")
    left = LEGACY_CAP_S - sum(a["wall_s"] for a in done["legacy"]) if env == "legacy" else LINE_S
    if left <= 0:
        raise LedgerStop(f"{env}: attempt {n}: the 36 hours are spent")
    return left


def _begin(root: Path, env: Env, n: int) -> None:
    """Record numbered attempt `n` as failed, so that an attempt that never finishes counts."""
    done = _attempts(root)
    done[env].append({"n": n, "date": date.today().isoformat(), "wall_s": 0, "result": "fail"})
    _write(root / ATTEMPTS, done)


def set_constant(consts, key: str, value: str) -> None:
    """Set the published constants' first `key = ` line, a [status] key or [sampling]'s cut_n, to `value`, leaving
    the line's comment."""
    path = consts.repo / "recipe/constants.toml"
    text, found = re.subn(rf"^({key} = )\S+", rf"\g<1>{value}", path.read_text(), count=1, flags=re.M)
    if not found:
        raise LedgerStop(f"recipe/constants.toml has no {key}")
    write_atomic(path, text.encode())


def _finish(pol, consts, env: Env, n: int, result: str, wall_s: float, collector: tuple[int, bool] | None) -> None:
    """Record the numbered attempt's result, then what it decides: the stop-loss attempt's success switches the
    published recipe and its failure is the kill. A legacy attempt that fails because its audit project (the
    collector; `collector` is Lake's exit and whether an executable exists) does not elaborate, or as the third,
    or with the hours spent, abandons the legacy environment; the gate line names the trigger, the collector's
    result and the line that holds the cache probe's."""
    done = _attempts(pol.root)
    done[env][-1].update(wall_s=wall_s, result=result)
    _write(pol.root / ATTEMPTS, done)
    reason = f"attempt {n}; result={result}; wall_s={wall_s:.0f}"
    if env == "pin-seeded":
        if result == "ok":
            set_constant(consts, "stop_loss", "true")
        gate, verdict = (("stop-loss", "cache-seeded recipe in force") if result == "ok"
                         else ("kill", "stop-loss failed"))
        gatefile.append(pol, gate, verdict, "pipeline", reason, date.today())
    elif env == "legacy" and result != "ok":
        used = sum(a["wall_s"] for a in done["legacy"])
        trigger = ("collector" if collector not in (None, (0, True)) else "attempts" if n == LIMIT["legacy"]
                   else "hours" if used >= LEGACY_CAP_S else None)
        if trigger:
            code, executable = collector or ("not run", "not run")
            set_constant(consts, "legacy", '"environment-unavailable"')
            gatefile.append(pol, "legacy-status", "environment-unavailable", "pipeline",
                            f"trigger={trigger}; attempts={n}; wall_s={used:.0f}; collector_exit={code}; "
                            f"collector_executable={executable}; cache_probe=see the legacy-cache-probe line",
                            date.today())


def _audit_dir(env: Env, tree: str) -> str:
    """The tree an environment's audit executable is built in: a rebuild's own, never the one pass 1 runs."""
    return "audit-rebuild" if tree == "rebuild" else f"audit-{'legacy' if env == 'legacy' else 'pin'}"


def build_audit(pol, consts, logs: Path, env: Env, toolchain: Path, timeout_s: float | None = None,
                tree: str = "pin") -> tuple[int, bool]:
    """Build the audit project of `env` (lean/audit-<role>, its toolchain verified) into env/audit-<role>, or a
    rebuild's into env/audit-rebuild, with no network, within `timeout_s` (by default the run ceiling). Returns
    Lake's exit and whether ledger-audit exists: it elaborates only on (0, True), since a project with no default
    target builds nothing and exits 0."""
    role = "legacy" if env == "legacy" else "pin"
    source, dest = consts.repo / "lean" / f"audit-{role}", pol.root / "env" / _audit_dir(env, tree)
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(source, dest, ignore=shutil.ignore_patterns(".lake"))
    call = lake(pol, consts, env, toolchain, dest, "build")
    built = confine.run(**call | {"timeout_s": timeout_s or call["timeout_s"]}, log=logs / f"audit-{role}.log")
    return built.exit, (dest / AUDIT_BIN).is_file()


def _check_cache_empty(root: Path, cache: str) -> None:
    """Stop unless Lake's artifact cache, and Mathlib's where the recipe forbids any cache, is empty (v16)."""
    for name in {"forbidden": ("lake", "mathlib"), "dependencies": ("lake",), "permitted": ()}[cache]:
        if any((root / "xdg-cache" / name).glob("*")):
            raise LedgerStop(f"xdg-cache/{name}: the cache is not empty, so the build would not be from source")


def _lean_path_root(pol, consts, env: Env, toolchain: Path, path: Path, logs: Path) -> str:
    """The root package's entry of Lake's LEAN_PATH, relative to the tree: the output root legs compile into."""
    printed = confine.run(**lake(pol, consts, env, toolchain, path, "env", "printenv", "LEAN_PATH"),
                          log=logs / f"lean-path-{env}.log")
    tree = path.resolve()
    own = [(tree / e).resolve() for e in printed.output.strip().rsplit("\n", 1)[-1].split(":") if e]
    own = [e for e in own if e.is_relative_to(tree / ".lake/build")]
    if printed.exit != 0 or len(own) != 1:
        raise LedgerStop(f"{env}: Lake's LEAN_PATH names no single output root of the tree; see lean-path-{env}.log")
    return own[0].relative_to(tree).as_posix()


def _swap_used_kb() -> int:
    meminfo = preflight.meminfo()
    return meminfo["SwapTotal"] - meminfo["SwapFree"]


def build(pol, consts, logs: Path, env: Env, tree: str = "pin", attempt: int | None = None,
          deadline: float | None = None) -> BuildReport:
    """The build step, with no network. `attempt` is the one-offs' number (pin tree only); an unnumbered build
    is neither checked against an attempt count nor recorded. Every precondition is checked before an attempt
    is recorded. Stops, naming why, unless the build passes within the line its attempt has, or with `deadline`, a
    time.monotonic() its audit project's build is bound by too, before it; a passed build's report is persisted at
    measure/build-<tree>.json, and the lines its digest hashes at measure/artifacts-<tree>.txt."""
    root, legacy, settings = pol.root, env == "legacy", consts.env[env]
    whole = env != "pin-seeded"  # a seeded build's dependency layers come from a cache
    timeout_s = check_attempt(root, consts, env, tree, attempt)
    path, role = _tree(root, env, tree), "legacy" if legacy else "pin"
    toolchain, lines = verified = installed_toolchain(root, consts.repo / "recipe" / env)
    audit_toolchain = installed_toolchain(root, consts.repo / "lean" / f"audit-{role}", verified)[0]
    if not (path / "lake-manifest.json").is_file():
        raise LedgerStop(f"{path}: not fetched")
    if not (threads := os.environ.get("LEAN_NUM_THREADS", "0")).isdecimal():
        raise LedgerStop(f"LEAN_NUM_THREADS={threads!r} is not a whole number")
    (report_path := root / "measure" / f"build-{path.name}.json").unlink(missing_ok=True)
    (list_path := root / "measure" / f"artifacts-{path.name}.txt").unlink(missing_ok=True)
    _check_cache_empty(root, settings["cache"])
    if not legacy:
        _wipe(path, whole)
        (path / MARKER).write_text("")
    if attempt is not None:
        _begin(root, env, attempt)
    result, wall_s, collector = "fail", 0.0, None
    try:
        collector = build_audit(pol, consts, logs, env, audit_toolchain,  # minutes, where the build is hours
                                None if deadline is None else deadline - time.monotonic(), tree)
        if collector != (0, True):
            raise LedgerStop(f"{env} build: the audit project does not elaborate into an executable "
                             f"(lake exit {collector[0]}, executable {collector[1]})")
        audit_digest = "sha256:" + _sha256(root / "env" / _audit_dir(env, tree) / AUDIT_BIN)
        overlay = devoverlay.load(pol)
        everything_mb = os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE") >> 20  # the slice is the bound
        targets = overlay.build_targets if overlay else TARGETS
        workers = preflight.headroom(WORKER_PEAK_KB, consts.published["limits"]["memory_floor_gib"])
        workers = min(workers, int(threads) or workers)  # the host's own cap, where set; 0 sets none
        _check_cache_empty(root, settings["cache"])  # immediately before: the audit build used the same cache
        swap = _swap_used_kb()
        proc = confine.run(**lake(pol, consts, env, toolchain, path, "build", *targets, workers=workers)
                           | {"timeout_s": timeout_s if deadline is None else deadline - time.monotonic()},
                           log=logs / f"build-{env}.log", memory_max_mb=everything_mb)
        wall_s = proc.wall_s
        if proc.killed == "wall-clock":
            result = "cap" if legacy else "timeout"
        if proc.exit != 0 or proc.killed:
            raise LedgerStop(f"{env} build: lake exited {proc.exit}, killed {proc.killed}, "
                             f"peak {proc.peak_mem_kb} kB, {wall_s:.0f} s")
        if not legacy:
            _check_artifacts(path, whole)
        digest = write_atomic(list_path, "".join(_artifact_lines(path, lines)).encode())
        report = BuildReport(proc.exit, wall_s, proc.peak_mem_kb, _swap_used_kb() - swap, workers, _disk_kb(path),
                             sum(1 for _ in _oleans(path)), digest,
                             _lean_path_root(pol, consts, env, toolchain, path, logs), audit_digest)
        _write(report_path, asdict(report))
        result = "ok"
        return report
    finally:
        if attempt is not None:
            _finish(pol, consts, env, attempt, result, wall_s, collector)
