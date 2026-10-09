import fcntl
import json
import os
import re
import shutil
from pathlib import Path

import pytest
from helpers import PY, REPO, in_unit, write_policy

pytestmark = pytest.mark.integration

# Record the toolchains as the install step would, fetch a pin tree (network), build the overlay's small target
# twice (none), from a systemd user unit with the run's TMPDIR; print every confine.run call's network flag, a
# connect attempted through Lake's build environment, each build's report, and the artifact list's sha256, its
# line count and the package oleans it should list.
SMALL = """
import dataclasses, hashlib, json, os, sys
from pathlib import Path
from ledger import REPO, confine, constants, envbuild, policy
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
consts = dataclasses.replace(constants.load(REPO), repo=Path(sys.argv[2]))
logs = pol.root / "runs/c6-small/logs"
logs.mkdir(parents=True, exist_ok=True)
(tmp := pol.root / "tmp/c6-small").mkdir(parents=True, exist_ok=True)
os.environ["TMPDIR"] = str(tmp)
calls, real = [], confine.run
def spy(cmd, **kwargs):
    calls.append([Path(cmd[0]).name, kwargs.get("net", False)])
    return real(cmd, **kwargs)
confine.run = spy
for toolchain in (pol.root / "elan/toolchains").iterdir():
    envbuild.record_toolchain(pol.root, toolchain)
envbuild.fetch(pol, consts, logs, "pin", "rebuild")
fetched = len(calls)
tree = pol.root / "env/rebuild"
reports = [dataclasses.asdict(envbuild.build(pol, consts, logs, "pin", "rebuild")) for _ in range(2)]
toolchain = envbuild.installed_toolchain(pol.root, consts.repo / "recipe/pin")[0]
probe = real(**envbuild.lake(pol, consts, "pin", toolchain, tree, "env", sys.executable, "-c",
                              "import socket; socket.create_connection(('127.0.0.1', 9), timeout=5)"))
listing = (pol.root / "measure/artifacts-rebuild.txt").read_bytes()
print(json.dumps({"calls": calls, "fetched": fetched, "reports": reports,
                  "probe": [probe.exit, "PermissionError" in probe.output],
                  "listing": ["sha256:" + hashlib.sha256(listing).hexdigest(), listing.count(b"\\n"),
                              sum(1 for _ in envbuild._oleans(tree / ".lake/packages"))
                              + len(envbuild._toolchain_lines(toolchain))]}))
"""
AUDIT = """
import dataclasses, os, sys
from pathlib import Path
from ledger import REPO, confine, constants, envbuild, policy
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
consts = dataclasses.replace(constants.load(REPO), repo=Path(sys.argv[2]))
logs = pol.root / "runs/c6-audit/logs"
logs.mkdir(parents=True, exist_ok=True)
(tmp := pol.root / "tmp/c6-audit").mkdir(parents=True, exist_ok=True)
os.environ["TMPDIR"] = str(tmp)
for env in ("pin", "legacy"):
    toolchain = envbuild.installed_toolchain(pol.root, consts.repo / f"lean/audit-{env}")[0]
    print(env, *envbuild.build_audit(pol, consts, logs, env, toolchain))
"""
def code_repo(path):
    """A copy of the recipe and the audit projects."""
    for top in ("recipe", "lean"):
        shutil.copytree(REPO / top, path / top, ignore=shutil.ignore_patterns(".lake"))
    return path


@pytest.fixture(scope="module", autouse=True)
def locked_dev_root():
    """The development environment, held under an exclusive flock for this module, so concurrent builders
    cannot rebuild or delete its trees under each other's runs."""
    if not os.environ.get("LEDGER_DEV_ROOT"):
        pytest.skip("LEDGER_DEV_ROOT is unset: integration tests need the development environment")
    fd = os.open(dev_root := Path(os.environ["LEDGER_DEV_ROOT"]), os.O_RDONLY)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
        yield dev_root
    finally:
        os.close(fd)


@pytest.fixture(scope="module")
def own_root(locked_dev_root, tmp_path_factory):
    """A root of this module's own beside the development environment, holding its recorded toolchains, linked, and
    its dev overlay: every tree the module builds, the audit projects' among them, is built there, never over the
    shared root's executables that its legs run."""
    root = locked_dev_root / "tmp" / f"envbuild-{tmp_path_factory.mktemp('root').name}"
    shutil.copytree(locked_dev_root / "elan", root / "elan", symlinks=True, copy_function=os.link)
    for name in ("measure", "xdg-cache"):  # the toolchains' record, and the cache Lake's calls may write
        (root / name).mkdir()
    shutil.copy(locked_dev_root / "measure/toolchains.json", root / "measure")
    shutil.copy(locked_dev_root / "dev-overlay.toml", root)
    yield root
    shutil.rmtree(root)


@pytest.fixture(scope="module")
def small(tmp_path_factory, own_root):
    """One fetch and two builds of the overlay's small target in env/rebuild of the module's own root, as the
    development environment, which its dev overlay requires."""
    work = tmp_path_factory.mktemp("small")
    run = in_unit(PY, "-c", SMALL, write_policy(work / "policy.toml", own_root), code_repo(work / "repo"),
                  env={"LEDGER_DEV_ROOT": own_root}, timeout=3000)
    assert run.code == 0, run.err[-3000:]
    return json.loads(run.out.splitlines()[-1]), own_root


def test_small_target_from_source_netless(small):
    """The small target is fetched with network and built without: zero barrels, an olean count equal to the
    build's own count of built modules, a connect through Lake's build environment refused, the scope's memory
    peak, the worker count and the LEAN_PATH output root reported, the report persisted, and the artifact list
    beside it, one line per package olean and toolchain file, its sha256 the digest."""
    # covers: test_small_target_from_source_netless
    result, dev_root = small
    tree = dev_root / "env/rebuild"
    assert [net for _, net in result["calls"][:1]] == [True]  # lake env true
    assert not any(net for _, net in result["calls"][result["fetched"]:])
    assert result["probe"] == [1, True]
    assert list(tree.rglob("build.barrel*")) == []
    built = len(re.findall(r"Built ", (dev_root / "runs/c6-small/logs/build-pin.log").read_text()))
    first = result["reports"][0]
    assert first["olean_count"] == built > 500
    assert first["peak_mem_kb"] > 0 and 1 <= first["workers"] <= os.cpu_count() - 2
    assert first["lean_path_root"] == ".lake/build/lib/lean" and first["exit"] == 0
    assert json.loads((dev_root / "measure/build-rebuild.json").read_text()) == result["reports"][1]
    digest, lines, expected = result["listing"]
    assert digest == result["reports"][1]["artifact_set_digest"] and lines == expected


@pytest.mark.slow
def test_same_recipe_twice_same_digest(small):
    """The same recipe built twice gives the same artifact-set digest."""
    first, second = small[0]["reports"]
    assert first["artifact_set_digest"] == second["artifact_set_digest"] != ""


def test_audit_project_builds_at_both_toolchains(own_root, tmp_path):
    """Each audit project elaborates and builds ledger-audit under confinement, at the pin and at the declared
    revision's toolchain, each from its own lean-toolchain, in the module's own root."""
    run = in_unit(PY, "-c", AUDIT, write_policy(tmp_path / "policy.toml", own_root), code_repo(tmp_path / "repo"),
                  timeout=900)
    assert run.out.splitlines() == ["pin 0 True", "legacy 0 True"], run.out + run.err
    assert all((own_root / f"env/audit-{env}/.lake/build/bin/ledger-audit").exists() for env in ("pin", "legacy"))
