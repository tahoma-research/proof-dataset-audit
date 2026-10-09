import math
import os
import shutil
import tempfile
from pathlib import Path

import pytest
from helpers import PY, REPO, git, hold_lock, in_unit, write_policy

from ledger import confine, constants, policy, preflight
from ledger.types import LedgerStop


def test_success_branch_first(ready):
    """A run whose every precondition holds passes preflight, one line per check."""
    pol, consts = ready()
    lines = preflight.check(pol, consts)
    assert [line.split(":")[0] for line in lines] == [
        "policy", "run lock", "dev overlay", "disk floor", "memory", "slice", "code tree"]


@pytest.mark.parametrize("override, stop", [({"disk_floor_gb": 10**9}, "disk floor"),
                                            ({"disk_floor_mount": "/absent"}, "/absent unreadable: No such file")],
                         ids=["below", "unreadable"])
def test_disk_floor_stops(ready, override, stop):
    """A run stops when free space on the floor mount is below the floor, or cannot be read."""
    with pytest.raises(LedgerStop, match=stop):
        preflight.check(*ready(**override))


@pytest.mark.parametrize("floor, field", [("memory_floor_gib", "MemAvailable"), ("swap_floor_gib", "SwapFree"),
                                          ("replay_memory_floor_mib", "replay memory")],
                         ids=["test_memory_floor_stops", "test_swap_floor_stops", "test_replay_memory_floor_stops"])
def test_memory_floor_stops(ready, monkeypatch, floor, field):
    """A run stops when MemAvailable, or free swap, is below its published floor, and the D+44 check's when
    MemAvailable is below the replay's floor."""
    monkeypatch.setattr(confine, "slice_memory_max_mb", lambda: math.inf)  # the replay's floor is its scope's cap too
    pol, consts = ready()
    consts.published["limits"][floor] = 10**6
    with pytest.raises(LedgerStop, match=field):
        preflight.check(pol, consts, replay=True)


@pytest.mark.parametrize("shown, stops", [("10737418240", True), ("infinity", False)])
def test_slice_below_largest_cap_stops(ready, tmp_path, monkeypatch, shown, stops):
    """On the host a run stops when ledger.slice's MemoryMax, as the user manager shows it, is below the largest
    memory cap the run sets on a scope; an unset MemoryMax holds any."""
    (systemctl := tmp_path / "systemctl").write_text(
        f'#!/bin/sh\ncase "$*" in *MemoryMax*) echo {shown} ;; *) exec {confine.SYSTEMCTL} "$@" ;; esac\n')
    systemctl.chmod(0o755)
    monkeypatch.setattr(confine, "SYSTEMCTL", str(systemctl))
    pol, consts = ready()
    consts.published["limits"]["agg_memory_max_mb"] = 24576
    if stops:
        with pytest.raises(LedgerStop, match="ledger.slice MemoryMax 10240 MiB is below the largest scope cap, 24576"):
            preflight.check(pol, consts)
    else:
        assert "slice: ledger.slice MemoryMax inf MiB, largest scope cap 24576 MiB" in preflight.check(pol, consts)


def test_path_resolving_to_root_stops(tmp_path):
    """On the host, a command stops when a path it writes resolves onto the root filesystem, before it
    writes anything: no lock, no run report."""
    with tempfile.TemporaryDirectory(dir="/tmp") as on_root:
        if os.stat(on_root).st_dev != os.stat("/").st_dev:
            pytest.skip("needs a directory on the root filesystem")
        path = write_policy(tmp_path / "operator.toml", Path(on_root), root_device_forbidden=True)
        run = in_unit(PY, "-m", "ledger", "oneoff", "probe-d7", "--policy", path)
        assert run.code == 2 and "root resolves to the root filesystem" in run.err, run.err
        assert list(Path(on_root).iterdir()) == []


def test_path_outside_root_stops(make_policy, root, tmp_path):
    """A command stops when a path it writes resolves outside the ledger root, before it writes anything:
    `gate`, which takes no lock, writes no gate line."""
    run = in_unit(PY, "-m", "ledger", "gate", "--gate", "d7", "--verdict", "pass", "--evaluator", "pipeline",
                  "--reason", "met", "--policy", make_policy(public_tree=str(tmp_path / "elsewhere")))
    assert run.code == 2 and "public_tree resolves outside" in run.err, run.err
    assert list(root.iterdir()) == []


def test_lock_held_refuses(make_policy, code_repo):
    """A run stops when the run lock is not held by this process."""
    pol = policy.load(make_policy())
    with hold_lock(pol.root):
        with pytest.raises(LedgerStop, match="run lock"):
            preflight.check(pol, constants.load(code_repo))


def test_stale_lock_does_not_skip(make_policy, code_repo):
    """A lock left by a killed run does not stop the next one: the kernel released it."""
    # covers: test_killed_holder_no_stale_lock
    pol = policy.load(make_policy())
    with hold_lock(pol.root) as holder:
        holder.kill()
        holder.wait()
        assert preflight.lock(pol.root) is None
    assert (pol.root / "lock").read_text() == f"{os.getpid()}\n"
    preflight.check(pol, constants.load(code_repo))


def test_container_policy_runs_every_tree_in_workdir(tmp_path, monkeypatch, code_repo):
    """The container's published policy loads as a container policy, so with none of the host's fields, and every
    path the run writes is in its working directory; preflight passes only while the free space there holds the
    run's need above the running floor, asks for no swap, which the container has none of, and holds its memory floor
    within the container's own memory.max where that is less than MemAvailable; with no memory limit, memory.max
    absent as under cgroup v1 or "max" as without --memory, or one below the largest published memory cap, it stops."""
    # covers: test_container::test_policy_has_no_host_fields
    work = tmp_path / "work"
    work.mkdir()
    shutil.copy(REPO / "recipe/policy/container.toml", work)
    monkeypatch.chdir(work)
    pol = policy.load(work / "container.toml")
    assert pol.root == work and all(p.is_relative_to(work) for p in pol.paths().values())
    preflight.paths(pol)
    assert preflight.lock(pol.root) is None
    need = pol.values["disk_floor_gb"] + pol.values["disk_need_gb"]
    monkeypatch.setattr(confine, "free_gb", lambda mount: need)
    consts = constants.load(code_repo)
    monkeypatch.setattr(preflight, "MEMORY_MAX", limit := tmp_path / "memory.max")
    for unlimited in (None, "max\n"):
        if unlimited:
            limit.write_text(unlimited)
        with pytest.raises(LedgerStop, match="the container has no memory limit, under cgroup v1 or started without "
                                             "--memory: the published memory cap cannot be enforced"):
            preflight.check(pol, consts)
    consts.published["limits"]["agg_memory_max_mb"] = 4096
    cap = max(consts.published["limits"][key] for key in preflight.CAPS)
    limit.write_text(f"{(cap - 1) << 20}\n")
    with pytest.raises(LedgerStop, match=f"slice: the container's memory limit, {cap - 1} MiB, is below the largest "
                                         f"memory cap, {cap} MiB"):
        preflight.check(pol, consts)
    limit.write_text(f"{1 << 60}\n")
    consts.published["limits"]["swap_floor_gib"] = 10**6
    assert not any("SwapFree" in line for line in preflight.check(pol, consts))
    limit.write_text(f"{4 << 30}\n")
    consts.published["limits"]["memory_floor_gib"] = 8
    with pytest.raises(LedgerStop, match="memory: memory.max 4.0 GiB is below the 8 GiB floor"):
        preflight.check(pol, consts)
    monkeypatch.setattr(confine, "free_gb", lambda mount: need - 1)
    with pytest.raises(LedgerStop, match=f"disk floor: {need - 1} GB free, below the {need} GB floor"):
        preflight.check(pol, constants.load(code_repo))


def test_headroom_from_measured_memory(tmp_path, monkeypatch):
    """The worker count follows MemAvailable as measured now, never a figure in a document, or under a cgroup memory
    limit the lesser of the two."""
    meminfo, limit = tmp_path / "meminfo", tmp_path / "memory.max"
    monkeypatch.setattr(preflight, "MEMINFO", meminfo)
    monkeypatch.setattr(preflight, "MEMORY_MAX", limit)
    gib = 1024 * 1024
    meminfo.write_text(f"MemTotal: {64 * gib} kB\nMemAvailable: {20 * gib} kB\n")
    count = preflight.headroom(4 * gib, 8.0)  # the published floor is a float; the count stays an integer
    assert type(count) is int and count == max(1, min(os.cpu_count() - 2, 3))
    limit.write_text(f"{16 * gib * 1024}\n")
    assert preflight.headroom(4 * gib, 8) == max(1, min(os.cpu_count() - 2, 2))
    limit.write_text("max\n")
    meminfo.write_text(f"MemTotal: {64 * gib} kB\nMemAvailable: {9 * gib} kB\n")
    assert preflight.headroom(4 * gib, 8) == 1


def test_dirty_public_tree_refuses(ready):
    """A run stops when the code or constants it would run differ from the commit it would record."""
    pol, consts = ready()
    with (consts.repo / "recipe/constants.toml").open("a") as f:
        f.write("\n")
    with pytest.raises(LedgerStop, match="code tree"):
        preflight.check(pol, consts)


def test_second_night_after_pass1_not_dirty(staged, stage_policy):
    """Pass 1's results in the public tree, leg files ignored and the progress file not yet committed, leave the
    code tree clean: the next night's preflight passes."""
    (staged / "results/legs").mkdir(parents=True)
    (staged / "results/legs/0a.pin.1.json").write_text("{}\n")
    (staged / "results/progress.json").write_text("{}\n")
    assert git("-C", staged, "status", "--porcelain", "--untracked-files=all") == "?? results/progress.json\n"
    consts = constants.load(staged)
    consts.published["limits"] |= {"memory_floor_gib": 0, "swap_floor_gib": 0, "leg_memory_max_mb": 0,
                                    "agg_memory_max_mb": 0}
    assert preflight.lock(stage_policy.root) is None
    assert preflight.check(stage_policy, consts)[-1] == "code tree: committed"
