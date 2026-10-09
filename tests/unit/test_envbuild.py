"""Environment build against synthetic trees. confine.run is replaced by a recorder that leaves behind what
Lake would, so the checks, the attempt record and the status changes under test are the code's own."""

import contextlib
import dataclasses
import hashlib
import json
import os
import shutil
import time
from datetime import date
from pathlib import Path
from types import SimpleNamespace

import pytest
from helpers import CLI, PY, REPO, in_unit

from ledger import confine, constants, envbuild, gatefile, preflight
from ledger.types import LedgerStop

TOOLCHAINS = {"pin": "leanprover--lean4---v4.34.0", "legacy": "leanprover--lean4---v4.8.0-rc1"}
DAY = 24 * 3600
CAP = 36 * 3600
LAKE_BUILD = ".lake/build/lib/lean"
FAILED = [("fail", 1), ("timeout", DAY), ("fail", 1)]  # three failed pin attempts: a timeout counts
TOOLCHAIN_FILES = ("bin/lean", "bin/lake", "lib/lean/libleanshared.so", "lib/lean/Init/Prelude.olean")


def write(path: Path, text: str = "x", mtime: float | None = None) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    if mtime is not None:
        os.utime(path, (mtime, mtime))
    return path


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def leave_oleans(tree: Path) -> None:
    """What a Lake build leaves: the root package's olean and two dependency packages'."""
    write(tree / f"{LAKE_BUILD}/Root.olean", "root")
    write(tree / f".lake/packages/dep/{LAKE_BUILD}/Dep.olean", "dep")
    write(tree / f".lake/packages/mathlib/{LAKE_BUILD}/Mathlib/Foo.olean", "foo")


class FakeRun:
    """Stands in for confine.run. `exits` is the exit status of a build of an environment tree and of an audit
    project; `on_audit` and `on_build` act as those builds start. The memory peak is None, as in a container."""

    def __init__(self):
        self.calls, self.exits, self.killed, self.wall_s = [], {"tree": 0, "audit": 0}, None, 100.0
        self.on_audit, self.on_build, self.audit_executable = (lambda: None), leave_oleans, True
        self.wrong_revision = False

    def builds(self, name):
        return [c for c in self.calls if "build" in c.cmd and c.cwd.name == name]

    def __call__(self, cmd, *, cwd, writes, net=False, env=None, memory_max_mb=None, log=None, timeout_s=None):
        call = SimpleNamespace(cmd=[Path(cmd[0]).name, *cmd[1:]], cwd=cwd, writes=writes, net=net, env=env,
                               memory_max_mb=memory_max_mb, timeout_s=timeout_s)
        self.calls.append(call)
        if call.cmd[0] == "git":
            manifest = "legacy" if cwd.parents[2].name == "legacy" else "pin"
            packages = json.loads((REPO / f"recipe/{manifest}/lake-manifest.json").read_text())["packages"]
            rev = next(p["rev"] for p in packages if p["name"] == cwd.name)
            return confine.Proc(0, None, None, 0.1, None, "0" * 40 if self.wrong_revision else rev)
        if "printenv" in call.cmd:
            return confine.Proc(0, None, None, 0.1, None, f"{cwd}/.lake/packages/dep/{LAKE_BUILD}:{cwd}/{LAKE_BUILD}\n")
        if "build" in call.cmd:
            audit = cwd.name.startswith("audit-")
            if audit:
                self.on_audit()
                if self.audit_executable:
                    write(cwd / envbuild.AUDIT_BIN)
            else:
                self.on_build(cwd)
            return confine.Proc(self.exits["audit" if audit else "tree"], self.killed, 0, self.wall_s, None,
                                "✔ [1/1] Built Mathlib")
        return confine.Proc(0, None, None, 0.1, None, "")


@pytest.fixture
def world(ready, monkeypatch, tmp_path):
    """A policy and recipe, both toolchains installed and recorded, the audit projects, every tree fetched, the
    run's TMPDIR; the build's worker count is 3 when it asks for 4 GiB per worker."""
    pol, consts = ready()
    toolchains = {}
    for env, name in TOOLCHAINS.items():
        toolchains[env] = pol.root / "elan/toolchains" / name
        for file in TOOLCHAIN_FILES:
            write(toolchains[env] / file, f"{name} {file}")
        envbuild.record_toolchain(pol.root, toolchains[env])
        audit = consts.repo / "lean" / f"audit-{env}"
        write(audit / "lean-toolchain", (consts.repo / "recipe" / env / "lean-toolchain").read_text())
    for name in ("pin", "rebuild", "pin-seeded", "legacy"):
        write(pol.root / "env" / name / "lake-manifest.json", "{}")
    (pol.root / "xdg-cache").mkdir()
    (tmp := pol.root / "tmp/run-1").mkdir(parents=True)
    monkeypatch.setenv("TMPDIR", str(tmp))
    (logs := tmp_path / "logs").mkdir()
    run = FakeRun()
    monkeypatch.setattr(confine, "run", run)
    monkeypatch.setattr(preflight, "headroom", lambda kb, floor: 3 if kb == 4 * preflight.GIB_KB else pytest.fail(kb))
    monkeypatch.delenv("LEAN_NUM_THREADS", raising=False)
    return SimpleNamespace(pol=pol, consts=consts, logs=logs, run=run, toolchains=toolchains, root=pol.root, tmp=tmp)


def build(world, env, attempt=None, tree="pin"):
    return envbuild.build(world.pol, world.consts, world.logs, env, tree, attempt)


def recorded(world, **envs) -> None:
    """Write env-attempts.json with, per environment, attempts ending as the given (result, wall_s)."""
    write(world.root / envbuild.ATTEMPTS, json.dumps({env: [{"n": n, "date": "2026-10-01", "wall_s": w, "result": r}
                                                            for n, (r, w) in enumerate(envs.get(env, []), 1)]
                                                      for env in envbuild.LIMIT}))


def gates(world) -> list[str]:
    return [row[1] for row in gatefile.rows(world.pol)]


def status(world, key) -> object:
    return constants.load(world.consts.repo).published["status"][key]


def test_pin_build_command_and_report(world, monkeypatch):
    """The audit project first, then `lake --no-cache build Mathlib Aesop` with no network, a memory scope, the
    24 h line, LEAN_NUM_THREADS the worker count and the run's TMPDIR, once every .lake/build, build.barrel* and
    olean outside .lake/config is gone and a marker exists; the report (peak None when unmeasured, LEAN_PATH
    output root) is persisted, and the sorted lines its digest hashes beside it. An unnumbered build records no
    attempt and writes no gate line. LEAN_NUM_THREADS set in the orchestrator's environment caps the workers; 0
    sets no cap, and a value not a whole number stops."""
    # covers: test_wipe_removes_all_builds_and_barrels, test_rebuild_and_unnumbered_builds_not_recorded,
    # covers: test_unnumbered_call_changes_no_status
    path, seen = world.root / "env/pin", []
    for left in (".lake/build/lib/old.olean", f".lake/packages/dep/{LAKE_BUILD}/Dep.olean", ".lake/config/m/a.olean",
                 ".lake/packages/dep/.lake/build.barrel", ".lake/packages/dep/build.barrel.part"):
        write(path / left)
    world.run.on_build = lambda tree: (seen.extend(p.relative_to(tree).as_posix() for p in tree.rglob("*")
                                                   if p.is_file()), leave_oleans(tree))
    report = build(world, "pin")
    assert sorted(seen) == sorted([".lake/config/m/a.olean", "lake-manifest.json", envbuild.MARKER])
    audit, call, lean_path = world.run.calls  # the audit project first: minutes, where the build is hours
    assert call.cmd == ["lake", "--no-cache", "build", "Mathlib", "Aesop"] and call.cwd == path
    assert not call.net and call.timeout_s == DAY and call.memory_max_mb > 0
    assert call.env["MATHLIB_NO_CACHE_ON_UPDATE"] == "1" and call.env["LEAN_NUM_THREADS"] == "3" == str(report.workers)
    assert call.env["TMPDIR"] == str(world.tmp) and world.tmp in call.writes and world.root / "tmp" not in call.writes
    assert Path(call.env["LAKE_CACHE_DIR"]).is_relative_to(world.root / "xdg-cache")
    assert lean_path.cmd == ["lake", "--no-cache", "env", "printenv", "LEAN_PATH"]
    assert (report.exit, report.wall_s, report.peak_mem_kb, report.lean_path_root) == (0, 100.0, None, LAKE_BUILD)
    assert report.olean_count == 3 and report.disk_kb > 0
    assert report.artifact_set_digest == envbuild.artifact_set_digest(path, world.toolchains["pin"])
    listing = (world.root / "measure/artifacts-pin.txt").read_bytes()
    assert report.artifact_set_digest == "sha256:" + hashlib.sha256(listing).hexdigest()
    assert listing.decode().splitlines()[:3] == [f".lake/packages/dep/{LAKE_BUILD}/Dep.olean\t{sha('dep')}",
                                                 f".lake/packages/mathlib/{LAKE_BUILD}/Mathlib/Foo.olean\t{sha('foo')}",
                                                 f"toolchain:bin/lake\t{sha(TOOLCHAINS['pin'] + ' bin/lake')}"]
    assert json.loads((world.root / "measure/build-pin.json").read_text()) == dataclasses.asdict(report)
    assert audit.cmd == ["lake", "--no-cache", "build"] and audit.cwd == world.root / "env/audit-pin"
    assert report.audit_digest == "sha256:" + hashlib.sha256((audit.cwd / envbuild.AUDIT_BIN).read_bytes()).hexdigest()
    assert not (world.root / envbuild.ATTEMPTS).exists() and gates(world) == []
    for threads, workers in (("2", 2), ("0", 3)):
        monkeypatch.setenv("LEAN_NUM_THREADS", threads)
        assert build(world, "pin").workers == workers
    monkeypatch.setenv("LEAN_NUM_THREADS", "four")
    with pytest.raises(LedgerStop, match="LEAN_NUM_THREADS='four'"):
        build(world, "pin")


@pytest.mark.parametrize("env, plant, before, fails", [
    ("pin", ".lake/packages/dep/.lake/build.barrel", False, True),
    ("pin", f".lake/packages/dep/{LAKE_BUILD}/Old.olean", False, True),
    ("pin-seeded", f".lake/packages/dep/{LAKE_BUILD}/Old.olean", True, False),  # a cached layer: the wipe keeps it
    ("pin-seeded", f"{LAKE_BUILD}/Old.olean", False, True),
], ids=["test_barrel_present_fails", "test_stale_olean_fails", "seeded-dependency", "seeded-root"])
def test_artifact_checks_fail_the_build(world, env, plant, before, fails):
    """A barrel, or an olean older than the start marker (the stop-loss: the root package's alone), fails the
    build though its own output claims every module was built (the log is never read)."""
    # covers: test_log_text_never_consulted, test_seeded_checks_root_package_only
    def old(tree):
        write(tree / plant, mtime=time.time() - DAY)
    if before:
        old(world.root / "env" / env)
    world.run.on_build = lambda tree: (leave_oleans(tree), before or old(tree))
    left = [write(world.root / "measure" / name) for name in (f"build-{env}.json", f"artifacts-{env}.txt")]
    with pytest.raises(LedgerStop, match="barrel|older than") if fails else contextlib.nullcontext():
        build(world, env)
    assert (world.root / "env" / env / plant).exists() and all(path.exists() is not fails for path in left)


@pytest.mark.parametrize("env, cache, refused", [
    ("pin", "lake", True), ("pin", "mathlib", True), ("pin-seeded", "lake", True), ("pin-seeded", "mathlib", False),
])
def test_nonempty_lake_cache_refuses(world, env, cache, refused):
    """The Lake artifact cache, and Mathlib's where the recipe forbids any cache, is checked empty immediately
    before the main build: what the audit build leaves there stops it."""
    world.run.on_audit = lambda: write(world.root / "xdg-cache" / cache / "artifacts/1.olean")
    with pytest.raises(LedgerStop, match="cache") if refused else contextlib.nullcontext():
        build(world, env)
    assert bool(world.run.builds(env)) is not refused


@pytest.mark.parametrize("break_it, toolchain", [
    (lambda world: (world.consts.repo / "recipe/pin-seeded/lean-toolchain").unlink(), True),
    (lambda world: shutil.rmtree(world.toolchains["pin"]), True),
    (lambda world: (world.root / envbuild.TOOLCHAINS).unlink(), True),
    (lambda world: write(world.toolchains["pin"] / "lib/lean/libleanshared.so", "another compiler"), True),
    (lambda world: write(world.toolchains["pin"] / "lib/lean/Extra.olean"), True),
    (lambda world: shutil.rmtree(world.consts.repo / "lean/audit-pin"), False),
    (lambda world: shutil.rmtree(world.root / "env/pin-seeded"), False),
    (lambda world: write(world.root / "xdg-cache/lake/artifacts/1.olean"), False),
], ids=["test_missing_toolchain_fails_not_defaults", "not-installed", "no-recorded-digest", "changed-library",
        "added-file", "no-audit-sources", "not-fetched", "cache-not-empty"])
def test_setup_error_runs_nothing_and_spends_no_attempt(world, break_it, toolchain):
    """A toolchain unnamed, not installed, unrecorded or not as recorded (any file changed or added), missing
    audit sources, an unfetched tree, a Lake cache not empty: the stop-loss attempt runs nothing, spends
    nothing, writes no kill. The fetch step refuses on the toolchain checks too."""
    recorded(world, pin=FAILED)
    break_it(world)
    with pytest.raises(LedgerStop, match="toolchain|audit-pin|not fetched|cache"):
        build(world, "pin-seeded", attempt=1)
    assert world.run.calls == [] and envbuild._attempts(world.root)["pin-seeded"] == [] and gates(world) == []
    if toolchain:
        with pytest.raises(LedgerStop, match="toolchain"):
            envbuild.fetch(world.pol, world.consts, world.logs, "pin-seeded")
        assert world.run.calls == []


def test_artifact_set_digest_sorted_and_includes_toolchain(world):
    """sha256 of sorted "<path>\\t<sha256>" lines per package olean (no pair or aggregate), then a sorted
    "toolchain:<path>" line per toolchain file, which alone make the toolchain digest; diverging oleans are named."""
    # covers: test_divergent_rebuild_reports_loudly, test_digest_excludes_pairs_and_aggregate_oleans
    first, second, toolchain = world.root / "env/pin", world.root / "env/rebuild", world.toolchains["pin"]
    modules = [(f"p{i}", f"M{i}", str(i)) for i in (5, 2, 7, 0, 3, 6, 1, 4)]  # written out of order
    for path in (first, second):
        for package, module, text in modules:
            write(path / f".lake/packages/{package}/{LAKE_BUILD}/{module}.olean", text)
    tools = "".join(f"toolchain:{file}\t{sha(TOOLCHAINS['pin'] + ' ' + file)}\n" for file in sorted(TOOLCHAIN_FILES))
    body = "".join(f".lake/packages/{package}/{LAKE_BUILD}/{module}.olean\t{sha(text)}\n"
                   for package, module, text in sorted(modules))
    digest = envbuild.artifact_set_digest(first, toolchain)
    assert digest == "sha256:" + sha(body + tools) and envbuild.toolchain_digest(toolchain) == "sha256:" + sha(tools)
    write(first / f"{LAKE_BUILD}/Pairs/P.olean", "pair")
    write(first / f"{LAKE_BUILD}/Aggregate.olean", "aggregate")
    assert envbuild.artifact_set_digest(first, toolchain) == digest and envbuild.divergence(first, second) == []
    write(second / f".lake/packages/p0/{LAKE_BUILD}/M0.olean", "different")
    write(second / f".lake/packages/p0/{LAKE_BUILD}/Extra.olean", "extra")
    assert envbuild.divergence(first, second) == [f".lake/packages/p0/{LAKE_BUILD}/Extra.olean",
                                                  f".lake/packages/p0/{LAKE_BUILD}/M0.olean"]
    assert envbuild.artifact_set_digest(second, toolchain) != digest


def test_toolchain_links_hashed_as_links_inside_the_toolchain(world, tmp_path):
    """A link in the toolchain, to a file or a directory, is hashed as its target, never followed or skipped; a
    link that resolves outside the toolchain stops."""
    toolchain = world.toolchains["pin"]
    (toolchain / "lib/lean/libalias.so").symlink_to("libleanshared.so")
    (toolchain / "lib/init").symlink_to("lean/Init")
    tools = sorted([*(f"toolchain:{file}\t{sha(TOOLCHAINS['pin'] + ' ' + file)}\n" for file in TOOLCHAIN_FILES),
                    "toolchain:lib/lean/libalias.so\tlink:libleanshared.so\n", "toolchain:lib/init\tlink:lean/Init\n"])
    assert envbuild.toolchain_digest(toolchain) == "sha256:" + sha("".join(tools))
    (toolchain / "lib/out").symlink_to(tmp_path)
    with pytest.raises(LedgerStop, match="lib/out links outside"):
        envbuild.toolchain_digest(toolchain)


@pytest.mark.parametrize("env, served, cache_calls", [
    ("pin", False, 0), ("pin-seeded", False, 1), ("legacy", False, 0), ("legacy", True, 1)])
def test_fetch_creates_its_tree_fresh_and_checks_revisions(world, env, served, cache_calls):
    """A fetch replaces its tree with the recipe (not env.toml), resolves with network, and stops on a HEAD that
    is not the manifest's; the cache call exists only where the recipe permits it, in the fetch step, and for the
    legacy environment only once the D+14 probe recorded that its cache serves; no build step call has network."""
    # covers: test_seeded_cache_call_only_in_fetch_step_net_permitted
    if served:
        gatefile.append(world.pol, "legacy-cache-probe", "serves", "pipeline", "probed", date(2026, 11, 16))
    path = world.root / "env" / env
    write(path / ".lake/build/lib/stale.olean")
    packages = json.loads((REPO / f"recipe/{env}/lake-manifest.json").read_text())["packages"]
    envbuild.fetch(world.pol, world.consts, world.logs, env)
    assert sorted(p.name for p in path.iterdir()) == sorted(p.name for p in (REPO / "recipe" / env).iterdir()
                                                            if p.name != "env.toml")
    resolve, *checks = world.run.calls
    assert resolve.cmd[-2:] == ["env", "true"] and resolve.net and len(checks) == len(packages) + cache_calls
    fetched = len(world.run.calls)
    build(world, env)
    cache = [i for i, c in enumerate(world.run.calls) if c.cmd[-3:] == ["exe", "cache", "get"]]
    assert len(cache) == cache_calls and all(i < fetched and world.run.calls[i].net for i in cache)
    assert not any(c.net for c in world.run.calls[fetched:])
    world.run.wrong_revision = True
    with pytest.raises(LedgerStop, match="HEAD"):
        envbuild.fetch(world.pol, world.consts, world.logs, env)


def test_seeded_recipe_distinct_id(code_repo):
    """The stop-loss recipe has an identifier of its own, and it covers the pin's audit sources."""
    audit = write(code_repo / "lean/audit-pin/Main.lean", "a")
    seeded = constants.recipe_id(code_repo, "pin-seeded")
    assert seeded != constants.recipe_id(code_repo, "pin")
    write(audit, "b")
    assert constants.recipe_id(code_repo, "pin-seeded") != seeded


UNAVAILABLE = {"status": "environment-unavailable"}


@pytest.mark.parametrize("env, tree, n, done, outcome", [
    ("pin", "pin", None, {"pin": [("ok", 1)] * 3}, DAY), ("pin", "rebuild", None, {}, DAY),  # unnumbered: unchecked
    ("pin-seeded", "pin", None, {}, DAY), ("legacy", "pin", None, {"legacy": FAILED} | UNAVAILABLE, CAP),
    ("pin", "pin", 1, {}, DAY), ("pin", "pin", 2, {}, "out of order"),
    ("pin", "pin", 1, {"pin": [("ok", 1)]}, "out of order"), ("pin", "pin", 4, {"pin": FAILED}, "out of order"),
    ("pin", "rebuild", 1, {}, "rebuild"), ("legacy", "rebuild", None, {}, "rebuild"),
    ("pin-seeded", "pin", 1, {"pin": FAILED[:2]}, "stop-loss"),
    ("pin-seeded", "pin", 1, {"pin": [("fail", 1), ("ok", 1), ("fail", 1)]}, "stop-loss"),
    ("pin-seeded", "pin", 1, {"pin": FAILED}, DAY), ("pin-seeded", "pin", 2, {"pin": FAILED}, "out of order"),
    ("pin-seeded", "pin", 1, {"pin": FAILED, "pin-seeded": [("fail", 1)]}, "out of order"),
    ("legacy", "pin", 2, {"legacy": [("fail", 20 * 3600)]}, CAP - 20 * 3600),
    ("legacy", "pin", 3, {"legacy": [("fail", 20 * 3600), ("cap", 16 * 3600)]}, "36 hours"),
    ("legacy", "pin", 2, {"legacy": [("fail", 1)]} | UNAVAILABLE, "unavailable"),
])
def test_check_attempt(world, env, tree, n, done, outcome):
    """Which builds may start, and the seconds each is given (an unnumbered pin-family build the 24 h line, an
    unnumbered legacy build the 36 h cap, whatever is recorded)."""
    # covers: test_attempt_out_of_order_refused, test_seeded_refused_before_three_failures,
    # covers: test_timeout_counts_as_failed_attempt, test_seeded_unnumbered_not_checked,
    # covers: test_legacy_unnumbered_not_capped, test_seeded_second_attempt_refused
    world.consts.published["status"]["legacy"] = done.get("status", "pending")
    recorded(world, **{k: v for k, v in done.items() if k != "status"})
    with pytest.raises(LedgerStop, match=outcome) if isinstance(outcome, str) else contextlib.nullcontext():
        assert envbuild.check_attempt(world.root, world.consts, env, tree, n) == outcome


@pytest.mark.parametrize("exits, gate, flag", [
    ({}, "stop-loss", True), ({"tree": 1}, "kill", False), ({"audit": 1}, "kill", False),
], ids=["succeeds", "build-fails", "audit-fails"])
def test_stop_loss_switches_recipe_everywhere(world, exits, gate, flag):
    """The numbered stop-loss attempt's success sets status.stop_loss and writes the stop-loss gate line; its
    failure, in its build or its audit project, writes kill and the flag stays false."""
    recorded(world, pin=FAILED)
    world.run.exits.update(exits)
    try:
        build(world, "pin-seeded", attempt=1)
    except LedgerStop:
        assert exits
    assert gates(world)[-1] == gate and status(world, "stop_loss") is flag


def test_pin_killed_at_its_line_recorded_timeout(world):
    """A numbered pin build killed at its 24 h line is recorded as `timeout`, not `fail` (04 § 7a)."""
    world.run.exits["tree"], world.run.killed = -9, "wall-clock"
    with pytest.raises(LedgerStop, match="wall-clock"):
        build(world, "pin", attempt=1)
    assert [a["result"] for a in envbuild._attempts(world.root)["pin"]] == ["timeout"]


@pytest.mark.parametrize("plan, timeouts, last, trigger", [
    ([(1.0, None)] * 3, [CAP, CAP - 1, CAP - 2], "fail", "attempts"),
    ([(20 * 3600, None), (16 * 3600, "wall-clock")], [CAP, 16 * 3600], "cap", "hours"),
], ids=["three-attempts", "36-hours"])
def test_legacy_cap_36h_three_attempts_unavailable(world, plan, timeouts, last, trigger):
    """Three failed attempts, or 36 hours summed over fewer (the fake's wall-clock), make legacy
    environment-unavailable in the gate file, with the trigger, the collector's exit and the cache probe's
    line, and in the constants; each attempt is given the hours that remain."""
    for n, (wall, killed) in enumerate(plan, 1):
        assert "legacy-status" not in gates(world)  # only the last attempt trips the cap
        world.run.exits["tree"], world.run.wall_s, world.run.killed = 1, wall, killed
        with pytest.raises(LedgerStop):
            build(world, "legacy", attempt=n)
    row = next(row for row in gatefile.rows(world.pol) if row[1] == "legacy-status")
    assert row[2] == "environment-unavailable" and status(world, "legacy") == "environment-unavailable"
    assert row[4].startswith(f"trigger={trigger}; attempts={len(plan)}; ") and "collector_exit=0" in row[4]
    assert "cache_probe=see the legacy-cache-probe line" in row[4]
    assert [c.timeout_s for c in world.run.builds("legacy")] == timeouts
    assert [a["result"] for a in envbuild._attempts(world.root)["legacy"]][-1] == last


@pytest.mark.parametrize("exit, executable", [(1, True), (0, False)], ids=["lake-fails", "builds-nothing"])
def test_legacy_collector_failure_unavailable_at_once(world, exit, executable):
    """A legacy audit project that does not elaborate (Lake fails, or builds no executable) makes legacy
    unavailable on the first attempt, and the hours-long build never starts."""
    world.run.exits["audit"], world.run.audit_executable = exit, executable
    with pytest.raises(LedgerStop, match="audit"):
        build(world, "legacy", attempt=1)
    assert gates(world)[-1] == "legacy-status" and status(world, "legacy") == "environment-unavailable"
    reason = gatefile.rows(world.pol)[-1][4]
    assert reason.startswith("trigger=collector; attempts=1; ") and f"collector_exit={exit}" in reason
    assert [c.cmd for c in world.run.calls] == [["lake", "build"]]


@pytest.mark.parametrize("args, tree", [
    (["--env", "pin", "--attempt", "2"], "pin"),
    (["--env", "legacy", "--tree", "rebuild"], "rebuild"),
    (["--env", "pin", "--tree", "rebuild", "--attempt", "1"], "rebuild"),
], ids=["out-of-order", "legacy-rebuild", "numbered-rebuild"])
def test_refused_build_leaves_the_tree_alone(make_policy, root, code_repo, args, tree):
    """`ledger env build` refuses an out-of-order attempt, or a legacy or numbered rebuild, before the fetch."""
    planted = write(root / f"env/{tree}/.lake/build/lib/keep.olean")
    run = in_unit(PY, "-c", CLI, code_repo, "env", "build", *args, "--policy", make_policy())
    assert run.code == 2 and ("out of order" in run.err or "rebuild" in run.err), run.err
    assert planted.exists()
