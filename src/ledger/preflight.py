"""Preflight: the run lock, and the preconditions checked before any work. A run that cannot establish one
stops rather than continue degraded."""

import fcntl
import math
import os
import time
from pathlib import Path

from ledger import confine, devoverlay
from ledger.types import LedgerStop

MEMINFO = Path("/proc/meminfo")
MEMORY_MAX = Path("/sys/fs/cgroup/memory.max")  # inside a container, its own cgroup's limit
GIB_KB = 1024 * 1024
TRACKED = ("src", "lean", "recipe", "classifier", "templates")  # the code and constants a run's commit names
CAPS = ("leg_memory_max_mb", "agg_memory_max_mb", "replay_memory_floor_mib")  # the memory caps a run sets, in MiB
_held: tuple[Path, int] | None = None  # (lock file, fd): kept open for the life of this process


def lock(root: Path, wait_s: float = 0) -> str | None:
    """Take the run lock (flock on <root>/lock) for the life of this process, trying for up to `wait_s` seconds, and
    write this PID into it. Returns None, or on contention the holder's PID ("unknown" if the file holds anything
    else). The kernel releases the lock when its holder dies, so a killed run leaves nothing stale. The lock is
    taken before the confinement exists, so a symlink in its place is refused, never followed out of the root."""
    global _held
    path = root / "lock"
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    except OSError as e:
        raise LedgerStop(f"cannot open the run lock: {e.strerror}") from e
    deadline = time.monotonic() + wait_s
    while True:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            if time.monotonic() < deadline:
                time.sleep(1)
                continue
            holder = os.read(fd, 32).strip()
            os.close(fd)
            return holder.decode() if holder.isdigit() else "unknown"
    os.ftruncate(fd, 0)
    os.write(fd, f"{os.getpid()}\n".encode())
    _held = (path, fd)
    return None


def meminfo() -> dict[str, int]:
    """/proc/meminfo, in kB."""
    return {key: int(value.split()[0])
            for key, value in (line.split(":", 1) for line in MEMINFO.read_text().splitlines())}


def _policy(policy, consts) -> str:
    """The named policy file loaded and passed validation (it is loaded before anything else)."""
    return f"policy: valid {policy.kind} policy"


def _lock(policy, consts) -> str:
    """The run lock is held by this process; ledger took it itself and preflight never takes it again."""
    if _held is None or _held[0] != policy.root / "lock":
        raise LedgerStop("run lock: not held by this process")
    return "run lock: held by this process"


def _overlay(policy, consts) -> str:
    """A dev overlay applies only under LEDGER_DEV_ROOT; its file under any other root stops the run."""
    overlay = devoverlay.load(policy)
    if overlay is None and (policy.root / devoverlay.FILE).exists():
        raise LedgerStop(f"dev overlay: {devoverlay.FILE} is present outside LEDGER_DEV_ROOT")
    return f"dev overlay: {'in use, results are development-only' if overlay else 'none'}"


def _device(path: str) -> int:
    while not os.path.exists(path):
        path = os.path.dirname(path)
    return os.stat(path).st_dev


def paths(policy) -> None:
    """Every path the run writes resolves beneath the root and, on the host, off the root filesystem. Every
    command checks this before it writes anything."""
    root = os.path.realpath(policy.root)
    system = os.stat("/").st_dev
    host = policy.kind == "operator" and policy.values["root_device_forbidden"]
    for name, path in policy.paths().items():
        real = os.path.realpath(path)
        if os.path.commonpath([root, real]) != root:
            raise LedgerStop(f"paths: {name} resolves outside the root")
        if host and _device(real) == system:
            raise LedgerStop(f"paths: {name} resolves to the root filesystem")


def _disk(policy, consts) -> str:
    """Free space where the run writes is at least the floor: the host's floor, or the container's need above the
    running floor its calls stop at."""
    if policy.kind == "operator":
        mount, floor = policy.values["disk_floor_mount"], policy.values["disk_floor_gb"]
    else:
        mount, floor = policy.root, policy.values["disk_floor_gb"] + policy.values["disk_need_gb"]
    if (free := confine.free_gb(mount)) < floor:
        raise LedgerStop(f"disk floor: {free:.0f} GB free, below the {floor} GB floor")
    return f"disk floor: {free:.0f} GB free, floor {floor} GB"


def _memory(policy, consts) -> str:
    """MemAvailable, or the cgroup's memory.max where that is less, and on the host SwapFree, are each at least the
    published floor; a container has no swap."""
    measured = meminfo()
    found = []
    for key, field in (("memory_floor_gib", "MemAvailable"), ("swap_floor_gib", "SwapFree")):
        if field == "SwapFree" and policy.kind != "operator":
            continue
        floor, value = consts.published["limits"][key], measured[field]
        if field == "MemAvailable" and (limit := memory_max_kb()) < value:
            field, value = "memory.max", limit
        gib = value / GIB_KB
        if gib < floor:
            raise LedgerStop(f"memory: {field} {gib:.1f} GiB is below the {floor} GiB floor")
        found.append(f"{field} {gib:.1f} GiB (floor {floor})")
    return "memory: " + ", ".join(found)


def _replay_memory(policy, consts) -> str:
    """For the D+44 check, MemAvailable is at least the replay's floor, set at D+14 from the pilot replay's peak."""
    floor = consts.published["limits"]["replay_memory_floor_mib"]
    if (mib := meminfo()["MemAvailable"] / 1024) < floor:
        raise LedgerStop(f"replay memory: MemAvailable {mib:.0f} MiB is below the replay's {floor} MiB floor")
    return f"replay memory: MemAvailable {mib:.0f} MiB (floor {floor})"


def _slice(policy, consts) -> str:
    """On the host, ledger.slice's MemoryMax is at least the largest memory cap a run sets on a scope, so that no
    published cap is only nominal; in a container its own memory limit is the ceiling, so the container must set one
    that cgroup v2 enforces, and as large."""
    cap = max(consts.published["limits"][key] for key in CAPS)
    if policy.kind != "operator":
        if (found := memory_max_kb() / 1024) == math.inf:
            raise LedgerStop("slice: the container has no memory limit, under cgroup v1 or started without --memory: "
                             "the published memory cap cannot be enforced")
        if found < cap:
            raise LedgerStop(f"slice: the container's memory limit, {found:.0f} MiB, is below the largest memory cap, "
                             f"{cap} MiB")
        return f"slice: none, the container's memory limit {found:.0f} MiB is the ceiling, largest memory cap {cap} MiB"
    if (found := confine.slice_memory_max_mb()) < cap:
        raise LedgerStop(f"slice: ledger.slice MemoryMax {found:.0f} MiB is below the largest scope cap, {cap} MiB")
    return f"slice: ledger.slice MemoryMax {found:.0f} MiB, largest scope cap {cap} MiB"


def _clean(policy, consts) -> str:
    """The code and constants that will run are committed, so the commit a run records is the code that ran."""
    status = confine.run(["git", "--no-optional-locks", "status", "--porcelain", "--", *TRACKED], cwd=consts.repo,
                         writes=[])
    if status.exit != 0:
        raise LedgerStop("code tree: git status failed")
    if status.output.strip():
        raise LedgerStop(f"code tree: {len(status.output.splitlines())} uncommitted changes under {', '.join(TRACKED)}")
    return "code tree: committed"


CHECKS = (_policy, _lock, _overlay, _disk, _memory, _slice, _clean)


def check(policy, consts, replay: bool = False) -> list[str]:
    """Run every check in order, and with `replay`, for the D+44 check, the replay's memory floor too; return one line
    for each. The first that fails stops the run."""
    return [step(policy, consts) for step in CHECKS + ((_replay_memory,) if replay else ())]


def memory_max_kb() -> float:
    """This cgroup's memory limit (a container's own), in kB; infinite where it sets none."""
    limit = MEMORY_MAX.read_text().strip() if MEMORY_MAX.exists() else "max"
    return math.inf if limit == "max" else int(limit) // 1024


def headroom(per_worker_peak_kb: int, memory_floor_gib: float) -> int:
    """The worker count the memory available now allows, MemAvailable or, under a cgroup memory limit, the lesser of
    it and the limit: max(1, min(cores - 2, (available - floor) // per-worker peak))."""
    spare = min(meminfo()["MemAvailable"], memory_max_kb()) - memory_floor_gib * GIB_KB
    return max(1, min(os.cpu_count() - 2, int(spare // per_worker_peak_kb)))
