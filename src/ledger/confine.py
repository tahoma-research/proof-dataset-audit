"""Confinement. Every command but publish restricts its own writes with Landlock before it reads any input
(apply_fs), and `run` is the one way the pipeline starts a Lean, Lake, git or elan process: through
ledger._nonet, which adds the child layers, inside a systemd scope of its own that `run` kills before it
returns. A memory-capped scope's in-scope reporter records the memory peak and OOM kills before the scope
vanishes."""

import contextlib
import ctypes
import fcntl
import hashlib
import itertools
import json
import math
import os
import re
import resource
import signal
import subprocess
import sys
import threading
import time
import tomllib
from dataclasses import dataclass
from pathlib import Path

from ledger import REPO
from ledger.types import LedgerStop

PY = "/usr/bin/python3"
# How a call starts _nonet and _reporter, before any child layer holds: neither the user's site directory
# (beneath HOME) nor the call's cwd, both of which a child may write, is on the module path.
PY_LEDGER = (PY, "-s", "-P", "-m")
SYSTEMD_RUN = "/usr/bin/systemd-run"
SYSTEMCTL = "/usr/bin/systemctl"
GIT = "/usr/bin/git"  # the config check's own git: never the first `git` on a PATH a child may have written
GIT_CHECK_S = 30  # the config check's limit: a FIFO in place of a fetched repository's config would block it
OUTPUT_MAX = 4 << 20  # by default, the bytes of a call's output kept; the rest is read and discarded
GIT_OUTPUT_MAX = 256 << 20  # stage's and publish's git calls, whose output is the data publish sweeps
FLOOR_POLL_S = 10  # how often a running call checks free space against the policy's floor
MEMORY_EVENTS = Path("/sys/fs/cgroup/memory.events")  # inside a container, its own cgroup's
KILLED = (-signal.SIGKILL, 128 + signal.SIGKILL)  # a child SIGKILLed, and how `lake env` reports one it ran

# Landlock system calls (x86_64) and constants, from linux/landlock.h.
_CREATE_RULESET, _ADD_RULE, _RESTRICT_SELF = 444, 445, 446
_CREATE_RULESET_VERSION = 1
_RULE_PATH_BENEATH, _RULE_NET_PORT = 1, 2
_PR_SET_NO_NEW_PRIVS = 38
# Filesystem rights: every right that creates, changes or removes something. Reads are not handled.
WRITE_FILE = 1 << 1
REMOVE_DIR = 1 << 4
REMOVE_FILE = 1 << 5
MAKE_CHAR = 1 << 6
MAKE_DIR = 1 << 7
MAKE_REG = 1 << 8
MAKE_SOCK = 1 << 9
MAKE_FIFO = 1 << 10
MAKE_BLOCK = 1 << 11
MAKE_SYM = 1 << 12
REFER = 1 << 13  # link or rename into another directory
TRUNCATE = 1 << 14
IOCTL_DEV = 1 << 15  # ABI 5: an ioctl on a device, even one opened read-only
FS_WRITE = (WRITE_FILE | REMOVE_DIR | REMOVE_FILE | MAKE_CHAR | MAKE_DIR | MAKE_REG | MAKE_SOCK | MAKE_FIFO
            | MAKE_BLOCK | MAKE_SYM | REFER | TRUNCATE | IOCTL_DEV)
FILE_WRITE = WRITE_FILE | TRUNCATE | IOCTL_DEV  # the rights a rule on a single file (not a directory) may carry
READ_FILE, READ_DIR = 1 << 2, 1 << 3  # handled only by the read layer of a call that runs proof code
FS_READ = READ_FILE | READ_DIR
# What such a call reads besides its own trees (03 § 5 (h)). Of /etc, only what strace found a real compile, replay
# and audit, and the aggregate's build, audit, walk and replay, open: the dynamic linker's cache. /proc/self names
# the call's first process, as it resolves when the rule is added.
READABLE = ("/usr", "/lib", "/lib64", "/bin", "/sbin", "/proc/self", "/dev/null", "/dev/urandom", "/etc/ld.so.cache")
BIND_TCP, CONNECT_TCP = 1 << 0, 1 << 1  # ABI 4: network rights
SCOPE_SIGNAL = 1 << 1  # ABI 6: no signal to a process outside the domain
# A child's environment: these names and prefixes only, never the rest of the parent's.
ENV_NAMES = {"PATH", "HOME", "LANG", "TMPDIR", "XDG_CACHE_HOME", "XDG_RUNTIME_DIR", "ELAN_HOME", "LEAN_NUM_THREADS"}
ENV_PREFIXES = ("MATHLIB_", "LAKE_")
# The entries (key, newline, value) a repository's own config may hold; others (core.fsmonitor, filter drivers,
# core.sshCommand, remote.*.uploadpack, include.path …) can make the next git call run a command, and a fetch
# refspec but origin's default can prune refs publish keeps.
GIT_KEYS = re.compile(r"(?:core\.(?:repositoryformatversion|filemode|bare|logallrefupdates)|remote\.[^\n]+\.url"
                      r"|branch\.[^\n]+)\n.*|remote\.origin\.fetch\n\+refs/heads/\*:refs/remotes/origin/\*", re.S)


class _RulesetAttr(ctypes.Structure):
    _fields_ = [("handled_access_fs", ctypes.c_uint64), ("handled_access_net", ctypes.c_uint64),
                ("scoped", ctypes.c_uint64)]


class _PathBeneath(ctypes.Structure):
    _pack_ = 1
    _fields_ = [("allowed_access", ctypes.c_uint64), ("parent_fd", ctypes.c_int32)]


class _NetPort(ctypes.Structure):
    _fields_ = [("allowed_access", ctypes.c_uint64), ("port", ctypes.c_uint64)]


_libc = ctypes.CDLL(None, use_errno=True)
_libc.syscall.restype = ctypes.c_long


def _call(function, *args) -> int:
    """Call a libc function with integers passed as C longs; raise OSError when it returns -1."""
    result = function(*(ctypes.c_long(a) if isinstance(a, int) else a for a in args))
    if result == -1:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error))
    return result


def prctl(*args) -> int:
    return _call(_libc.prctl, *args)


def landlock_abi() -> int:
    """The kernel's Landlock ABI version; -1 when Landlock is unavailable."""
    try:
        return _call(_libc.syscall, _CREATE_RULESET, None, 0, _CREATE_RULESET_VERSION)
    except OSError:
        return -1


def handled(abi: int) -> tuple[int, int]:
    """The write rights and the scope the child layers handle at Landlock ABI `abi`: all of FS_WRITE but a rename
    or link into another directory below ABI 2 (where Landlock refuses one outright), truncate below 3 and an ioctl
    on a device below 5; the signal scope from ABI 6."""
    later = (REFER, 2), (TRUNCATE, 3), (IOCTL_DEV, 5)
    return FS_WRITE & ~sum(right for right, since in later if abi < since), SCOPE_SIGNAL if abi >= 6 else 0


def restrict(*, fs: int, scoped: int = 0, beneath: list, tcp_connect: tuple[int, ...] | None = None) -> None:
    """Add a Landlock layer to this process and every process it starts. Handled rights are denied
    except beneath each (path, rights) rule. With `tcp_connect`, a TCP connect reaches only those ports and
    no TCP bind is allowed. Sets no_new_privs first; no layer can be lifted."""
    attr = _RulesetAttr(fs, 0 if tcp_connect is None else BIND_TCP | CONNECT_TCP, scoped)
    ruleset = _call(_libc.syscall, _CREATE_RULESET, ctypes.byref(attr), ctypes.sizeof(attr), 0)
    try:
        for path, rights in beneath:
            fd = os.open(path, os.O_PATH | os.O_CLOEXEC)
            try:
                _call(_libc.syscall, _ADD_RULE, ruleset, _RULE_PATH_BENEATH,
                      ctypes.byref(_PathBeneath(rights, fd)), 0)
            finally:
                os.close(fd)
        for port in tcp_connect or ():
            _call(_libc.syscall, _ADD_RULE, ruleset, _RULE_NET_PORT, ctypes.byref(_NetPort(CONNECT_TCP, port)), 0)
        prctl(_PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)
        _call(_libc.syscall, _RESTRICT_SELF, ruleset, 0)
    finally:
        os.close(ruleset)


_container = False  # set by apply_fs under a container policy: calls run without a scope, apply_fs adds no layer
_protected: list[Path] = []  # set by apply_fs: what no call may write, the policy, the lock and the public code
_floor: tuple[str, int] | None = None  # set by apply_fs: where free space is checked, and the policy's disk_floor_gb


def apply_fs(policy) -> str:
    """Confine writes, for this process and all its children, to beneath the ledger root, /dev/shm and
    /dev/null, and record the policy's free-space floor for `run`: on its disk_floor_mount, or under a container
    policy, which adds no layer here, in the working directory. A Landlock ABI below 6, which the child layers need
    whole, stops the run; under a container policy, where they apply as handled() allows, only one below 1 does.
    Returns the confinement for the run report: the ABI, and the allowed paths or the layers each call keeps."""
    global _container, _floor
    abi = landlock_abi()
    if policy.values["confinement"] == "none":
        if abi < 1:
            raise LedgerStop(f"Landlock ABI {abi}: Landlock is unavailable; refusing to run without the write layer")
        _container, _floor = True, (str(policy.root), policy.values["disk_floor_gb"])
        return (f"Landlock ABI {abi}, each call's write layer"
                f"{' and signal scope' if abi >= 6 else ' (no signal scope below ABI 6)'} in the container")
    if abi < 6:
        raise LedgerStop(f"Landlock ABI {abi} is below 6 (-1: unavailable); refusing to run unconfined")
    public = Path(policy.values["public_tree"])
    _protected[:] = [policy.root / "policy", policy.root / "lock",
                     *(public / name for name in ("src", "lean", "recipe", "classifier", "templates"))]
    if len(os.listdir("/proc/self/task")) != 1:
        raise LedgerStop("Landlock restricts only the calling thread; apply_fs needs a process with one thread")
    beneath = [(policy.root, FS_WRITE), ("/dev/shm", FS_WRITE), ("/dev/null", FILE_WRITE)]
    try:
        restrict(fs=FS_WRITE, beneath=beneath)
    except OSError as e:
        raise LedgerStop(f"Landlock restriction failed: {e.strerror}") from e
    _floor = policy.values["disk_floor_mount"], policy.values["disk_floor_gb"]
    return f"Landlock ABI {abi}, writes beneath {', '.join(str(path) for path, _ in beneath)}"


@dataclass(frozen=True)
class Proc:
    exit: int  # negative: killed by that signal
    killed: str | None  # "oom": the scope's memory ceiling killed a process in it; "wall-clock": `timeout_s` ran out
    oom_kill: int | None  # scoped runs only
    wall_s: float
    peak_mem_kb: int | None  # the scope's memory.peak, capped runs only; a bare child's largest process's, from wait4
    output: str  # stdout and stderr together, their first output_max bytes
    raw: bytes = b""  # the same, undecoded
    output_truncated: bool = False  # the call's output ran past output_max


NO_CACHE_TREES = {"pin", "rebuild", "pin-seeded", "audit-pin", "audit-rebuild", "proof1b"}  # in env/<tree> each Lake call is --no-cache


def _no_cache_tree(cwd: Path) -> bool:
    parts = Path(cwd).resolve().parts
    return any(parts[i] == "env" and parts[i + 1] in NO_CACHE_TREES for i in range(len(parts) - 1))


def _invoking_unit() -> str:
    """The systemd user unit this process runs in."""
    cgroup = Path("/proc/self/cgroup").read_text().strip().removeprefix("0::")
    if "/user@" not in cgroup:
        raise LedgerStop("a scoped command must be started from a systemd user unit")
    return cgroup.rsplit("/", 1)[1]


def scope_name(root: Path, leg: str) -> str:
    """The systemd scope name of a leg run on `root`; the root's hash keeps each root's scopes apart."""
    return f"ledger-{hashlib.sha256(os.path.realpath(root).encode()).hexdigest()[:8]}-{leg}"


_calls = itertools.count()  # names the scope of a call that names none


def _check_git_config(cwd: Path, env: dict[str, str]) -> None:
    """Refuse a repository whose own config holds a key outside GIT_KEYS: a child that wrote the tree could
    have planted one there to run a command at the next git call, with that call's rights."""
    try:
        found = subprocess.run([GIT, "rev-parse", "--git-path", "config"], cwd=cwd, env=env,
                               stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=GIT_CHECK_S)
        if found.returncode != 0:
            return  # not inside a repository (git init, git clone): there is no repository config to read
        config = Path(cwd, found.stdout.strip())
        if not config.is_file():
            raise LedgerStop(f"git: the repository at {cwd} has a config that is not a regular file")
        listed = subprocess.run([GIT, "config", "--file", config, "--list", "-z"], cwd=cwd,
                                env=env, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=GIT_CHECK_S)
    except subprocess.TimeoutExpired:
        raise LedgerStop(f"git: reading the repository config at {cwd} took over {GIT_CHECK_S} s") from None
    keys = [entry.partition("\n")[0] for entry in listed.stdout.split("\0") if entry and not GIT_KEYS.fullmatch(entry)]
    if listed.returncode != 0 or keys:
        raise LedgerStop(f"git: the repository at {cwd} has config outside the allowlist: "
                         f"{', '.join(keys) or listed.stderr.strip()}")


def _reap(unit: str) -> None:
    """Kill whatever the call left in its scope and confirm the scope inactive, so that nothing a call
    started can write after `run` returns."""
    # The scope's KillSignal is SIGKILL. stop waits for it, and exits 5 when the scope already ended with
    # its last process; the state read below is the check either way.
    subprocess.run([SYSTEMCTL, "--user", "stop", f"{unit}.scope"], stdin=subprocess.DEVNULL, capture_output=True)
    state = subprocess.run([SYSTEMCTL, "--user", "show", "-P", "ActiveState", f"{unit}.scope"],
                           stdin=subprocess.DEVNULL, capture_output=True, text=True).stdout.strip()
    if state != "inactive":
        raise LedgerStop(f"{unit}: the call's scope is still {state or 'unreadable'} after the call")


def _peak_kb(unit: str) -> int | None:
    """The live scope's memory.peak, in kB; None once the scope has ended, as when its command exits as the
    limit passes."""
    group = subprocess.run([SYSTEMCTL, "--user", "show", "-P", "ControlGroup", f"{unit}.scope"],
                           stdin=subprocess.DEVNULL, capture_output=True, text=True).stdout.strip()
    try:
        return int(Path("/sys/fs/cgroup" + group, "memory.peak").read_text()) // 1024 if group else None
    except FileNotFoundError:
        return None


def slice_memory_max_mb() -> float:
    """ledger.slice's MemoryMax as the user manager has it, in MiB; infinite when it sets none."""
    shown = subprocess.run([SYSTEMCTL, "--user", "show", "-P", "MemoryMax", "ledger.slice"],
                           stdin=subprocess.DEVNULL, capture_output=True, text=True)
    value = shown.stdout.strip()
    if shown.returncode != 0 or not (value == "infinity" or value.isdigit()):
        raise LedgerStop(f"ledger.slice's MemoryMax unreadable: {value or shown.stderr.strip()}")
    return math.inf if value == "infinity" else int(value) / (1 << 20)


def free_gb(mount: str) -> float:
    """Free space on `mount`, in GB, as this user may use it."""
    try:
        disk = os.statvfs(mount)
    except OSError as e:
        raise LedgerStop(f"free space on {mount} unreadable: {e.strerror}") from e
    return disk.f_bavail * disk.f_frsize / 1e9


def _oom_kills() -> int | None:
    """The container cgroup's oom_kill count; None where memory.events is unreadable."""
    try:
        found = re.search(r"^oom_kill (\d+)$", MEMORY_EVENTS.read_text(), re.M)
    except OSError:
        return None
    return found and int(found[1])


def _drain(fd: int, kept: bytearray, limit: int) -> None:
    """Read the pipe `fd` to its end, then close it, keeping its first `limit` bytes and one more, which marks
    the output truncated: the rest is discarded, so no amount of output fills this process's memory."""
    with open(fd, "rb", buffering=0) as pipe:
        while chunk := pipe.read(1 << 16):
            kept += chunk[:limit + 1 - len(kept)]


def run(cmd: list[str], *, cwd: Path, writes: list[Path], net: bool = False, env: dict[str, str] | None = None,
        memory_max_mb: int | None = None, unit_name: str | None = None, log: Path | None = None,
        timeout_s: float | None = None, input: bytes | None = None, secret_fd: int | None = None,
        no_meta: bool = False, reads: list[Path] | None = None, output_max: int = OUTPUT_MAX) -> Proc:
    """Run `cmd` under the child layers: writes only beneath `writes` (none holding or within the policy, the
    lock or the public tree's code) and /dev/null, no signal out of its domain, no socket unless `net`, and
    then TCP to port 443 only; no change to any file's owner or extended attributes, and with `no_meta`, which
    every call running proof code passes, to its mode or timestamps either; with `reads`, which those calls pass
    too, reads only of READABLE, `reads` and `writes`. It runs in its own scope `unit_name`
    (see scope_name; by default one named for this call) in ledger.slice, bound to the invoking unit so it stops
    with it, and killed before `run` returns.
    The command gets only the ENV_NAMES and ENV_PREFIXES variables of `env` (default: this process's
    environment) and a UTC clock; any git it starts, a nested one too, reads no system or user config or
    attributes file and runs no hook. A git call refuses a repository whose config holds a key outside
    GIT_KEYS. `secret_fd`, a pipe holding a secret, is inherited as that same descriptor by the command. With
    `memory_max_mb` the scope's ceiling is enforced and `log` is required; no scope swaps, capped or not.
    `log`, which receives the output, must lie where no call writes; of the output only its first `output_max` bytes
    are kept, in the result and the log, the rest read and discarded and the result marked truncated. `input` is
    the command's stdin, /dev/null without it. Every call is bounded: after `timeout_s` seconds, by default the
    published per-pair limit, the result is `killed == "wall-clock"`: the scope's memory peak is read
    (memory-capped calls), then the scope is killed, so a descendant in a session of its own that holds the output
    open cannot stall the call. Under a container policy the command runs without a scope, the read layer or the
    TCP port rule, and keeps the other child layers, as handled() allows at the kernel's ABI: it writes only beneath
    `writes`, and without `net` opens no socket. Its process group is killed instead, and its memory peak is that of
    the largest process it reaped, from wait4; a command killed by SIGKILL (KILLED) while the container cgroup's
    oom_kill count rose is killed "oom", the rise its oom_kill, which is 0 for any other command and None where the
    count is unreadable. The count is the whole container's: with calls in parallel, one SIGKILLed while another's
    process is killed oom is classed oom too, the other's kill its oom_kill.
    No child dumps core.
    With LEDGER_HOST_LOCK naming an existing file in this process's environment, a call that is not a git call holds
    an exclusive flock on it from before its scope starts until the scope is reaped, so calls on a shared host run
    one at a time; a call that finds it held says so on stderr, then waits. After apply_fs, a call given no `input`
    that finds free space where apply_fs recorded below the policy's disk_floor_gb, at a check every FLOOR_POLL_S
    seconds while the child runs or its output is open, is killed and stops the run."""
    if Path(cmd[0]).name == "lake" and _no_cache_tree(cwd) and cmd[1:2] != ["--no-cache"]:
        raise LedgerStop("in a pin tree every Lake call starts `lake --no-cache`")
    if memory_max_mb is not None and log is None:
        raise LedgerStop("a memory-capped call needs a log, beside which its reporter writes")
    if log and any(log.parent.resolve().is_relative_to(Path(path).resolve()) for path in writes):
        raise LedgerStop(f"{log}: a log may not lie where the call writes")
    if any(a.resolve().is_relative_to(b.resolve()) for path in writes for kept in _protected
           for a, b in ((kept, Path(path)), (Path(path), kept))):
        raise LedgerStop(f"{', '.join(map(str, writes))}: a call may not write the policy, the lock or the "
                         "public tree's code")
    child_env = {k: v for k, v in (os.environ if env is None else env).items()
                 if k in ENV_NAMES or k.startswith(ENV_PREFIXES)}
    child_env |= {"PYTHONPATH": str(REPO / "src"), "PYTHONDONTWRITEBYTECODE": "1",
                  "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_ATTR_NOSYSTEM": "1",
                  "GIT_TERMINAL_PROMPT": "0", "GIT_CONFIG_COUNT": "2",
                  "GIT_CONFIG_KEY_0": "core.hooksPath", "GIT_CONFIG_VALUE_0": "/dev/null",
                  "GIT_CONFIG_KEY_1": "core.attributesFile", "GIT_CONFIG_VALUE_1": "/dev/null",
                  "TZ": "UTC"}  # every child: Lake runs git too
    if is_git := Path(cmd[0]).name == "git":
        _check_git_config(cwd, child_env)
    unit = unit_name or f"ledger-call-{os.getpid()}-{next(_calls)}"
    argv = [sys.executable if _container else PY, *PY_LEDGER[1:], "ledger._nonet",  # the image has no Python at PY
            *(["--container"] if _container else []), *(["--tcp"] if net else []), *(["--no-meta"] if no_meta else []),
            *(f"--read-allow={path}" for path in ([] if reads is None or _container else [*READABLE, *reads, *writes])),
            *map(str, writes), "--", *cmd]
    if _container:
        run_env, memory_max_mb = child_env, None
    else:
        if memory_max_mb is not None:
            side = log.with_name(log.name + ".reporter.json")
            side.unlink(missing_ok=True)  # only this run's reporter may supply the facts read below
            argv = [f"--property=MemoryMax={memory_max_mb}M",
                    *PY_LEDGER, "ledger._reporter", "--out", str(side), "--", *argv]
        argv = [SYSTEMD_RUN, "--user", "--scope", "--quiet", f"--unit={unit}", "--slice=ledger.slice",
                f"--property=BindsTo={_invoking_unit()}", "--property=OOMPolicy=continue",
                "--property=MemorySwapMax=0", "--property=KillSignal=SIGKILL",
                *(f"--setenv={k}={v}" for k, v in child_env.items()), *argv]
        # systemd-run reaches the user manager through the real runtime directory, and passes its own
        # environment on; the command's own variables come through --setenv.
        run_env = {"XDG_RUNTIME_DIR": f"/run/user/{os.getuid()}"}
    if timeout_s is None:
        timeout_s = tomllib.loads((REPO / "recipe/constants.toml").read_text())["limits"]["per_pair_wall_clock_s"]
    host_lock = None if is_git else os.environ.get("LEDGER_HOST_LOCK")
    try:
        held = open(host_lock, "rb") if host_lock else contextlib.nullcontext()
    except OSError as e:
        raise LedgerStop(f"the host lock {host_lock}: {e.strerror}") from e
    with held:
        if host_lock:
            try:
                fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                print(f"waiting for the host lock {host_lock}", file=sys.stderr, flush=True)
                fcntl.flock(held, fcntl.LOCK_EX)  # waits for every call under the same lock; not part of timeout_s
        start, peak, returncode, ooms = time.monotonic(), None, None, _oom_kills() if _container else None
        secret = {} if secret_fd is None else {"pass_fds": (secret_fd,)}
        # Every child inherits it; 1 byte, not 0, as publish says.
        resource.setrlimit(resource.RLIMIT_CORE, (1, 1))
        kept, (read_end, write_end) = bytearray(), os.pipe()
        reader = threading.Thread(target=_drain, args=(read_end, kept, output_max), daemon=True)
        reader.start()  # it ends once every holder of write_end has closed it
        try:
            child = subprocess.Popen(argv, cwd=cwd, env=run_env,
                                     stdin=subprocess.DEVNULL if input is None else subprocess.PIPE, stdout=write_end,
                                     stderr=subprocess.STDOUT, start_new_session=_container, **secret)
        finally:
            os.close(write_end)
        # A bare child is waited for without being reaped, so its process group outlives it until the kill decision;
        # then wait4 reaps it, its rusage the call's memory peak.
        if bare := _container and input is None:
            waiter = threading.Thread(target=os.waitid, args=(os.P_PID, child.pid, os.WEXITED | os.WNOWAIT),
                                      daemon=True)
            waiter.start()

        def reap() -> None:
            nonlocal peak
            waiter.join()  # the command has exited or been killed, so this is at once
            _, status, usage = os.wait4(child.pid, 0)
            child.returncode, peak = os.waitstatus_to_exitcode(status), usage.ru_maxrss  # ru_maxrss in kB

        def exited(wait_s: float) -> bool:  # writes the input and waits for the command's exit
            if bare:
                waiter.join(wait_s)
                return not waiter.is_alive()
            with contextlib.suppress(subprocess.TimeoutExpired):
                child.communicate(input, timeout=wait_s)
            return child.returncode is not None

        def drained(wait_s: float) -> bool:  # waits for the output's end: a descendant may hold it
            reader.join(wait_s)
            return not reader.is_alive()

        with child:
            try:
                # communicate cannot resume writing an input after a timeout, so a call given one waits once, unchecked
                poll_s = FLOOR_POLL_S if _floor and input is None else timeout_s
                for done in (exited, drained):  # checking free space between slices of each wait
                    while not done(min(poll_s, start + timeout_s - time.monotonic())):
                        if time.monotonic() >= start + timeout_s:
                            raise subprocess.TimeoutExpired(argv, timeout_s)
                        if _floor and free_gb(_floor[0]) < _floor[1]:
                            raise LedgerStop(f"free-space floor reached during {unit}")
                if bare:
                    reap()
                returncode = child.returncode
            except subprocess.TimeoutExpired:
                peak = None if _container or memory_max_mb is None else _peak_kb(unit)
            finally:  # whatever ended the wait, nothing the call started outlives it
                if not _container:
                    _reap(unit)  # every holder of the output is in the scope
                elif returncode is None:
                    os.killpg(child.pid, signal.SIGKILL)
                    if bare:
                        reap()
    reader.join(60)  # every holder is dead: EOF is near
    if reader.is_alive():
        raise LedgerStop(f"{unit}: the call's output is still open 60 s after the call was killed")
    stdout = bytes(kept[:output_max])
    truncated = len(kept) > len(stdout)
    wall_s = time.monotonic() - start
    output = stdout.decode(errors="replace")
    if log:
        with open(os.open(log, os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW, 0o600), "w") as f:
            f.write(output)
    if returncode is None:  # timed out: the reporter died with the command, so the peak is the one read before
        return Proc(-signal.SIGKILL, "wall-clock", None, wall_s, peak, output, stdout, truncated)
    if memory_max_mb is None:
        after = None if ooms is None else _oom_kills()
        oom_kill = None if after is None else after - ooms if returncode in KILLED else 0
        return Proc(returncode, "oom" if oom_kill else None, oom_kill, wall_s, peak, output, stdout, truncated)
    try:
        facts = json.loads(side.read_text())
    except FileNotFoundError:
        raise LedgerStop(f"{unit}: the scope's reporter recorded nothing (exit {returncode})") from None
    side.unlink()
    return Proc(-facts["signal"] or returncode, "oom" if facts["oom_kill"] else None, facts["oom_kill"], wall_s,
                facts["peak_mem_kb"], output, stdout, truncated)


def stop_leftover_scopes(root: Path) -> None:
    """Stop every scope a killed run on `root` left behind. Call only while holding the run lock, which
    proves no other run on `root` is live."""
    done = subprocess.run([SYSTEMCTL, "--user", "stop", scope_name(root, "*.scope")], stdin=subprocess.DEVNULL,
                          capture_output=True, text=True)
    if done.returncode != 0:
        raise LedgerStop(f"leftover scopes not stopped: {done.stderr.strip()}")


@dataclass(frozen=True)
class ConfineReport:
    label: str  # this process's AppArmor label; only "unconfined" (a systemd user unit) is evidence
    checks: dict[str, bool]

    @property
    def ok(self) -> bool:
        return self.label == "unconfined" and all(self.checks.values())

    def __str__(self) -> str:
        return "\n".join([f"label: {self.label}"] + [f"{'ok  ' if v else 'FAIL'} {k}" for k, v in self.checks.items()])


# Exits 0 only when the operation is refused with EACCES or EPERM.
_REFUSED = "import os, socket, sys\ntry:\n    {}\nexcept PermissionError:\n    sys.exit(0)\nsys.exit(1)"


def _creates(directory: Path) -> bool:
    """Whether a new file can be created in `directory`; the probe file is removed at once."""
    probe = directory / f".ledger-self-test-{os.getpid()}"
    try:
        os.close(os.open(probe, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600))
    except PermissionError:
        return False
    probe.unlink()
    return True


def _refused(directory: Path) -> bool:
    """A write the user's own permissions allow, refused by the confinement."""
    return os.access(directory, os.W_OK) and not _creates(directory)


def self_test(policy) -> ConfineReport:
    """Probe the confinement from inside it. Call after apply_fs, from a systemd user unit: an interactive
    session's own security label can let a refused operation through, so only a unit's result counts."""
    root = policy.root
    home_probe = Path.home() / f".ledger-self-test-{os.getpid()}"

    def refused_in_child(operation: str, writes: tuple[Path, ...] = ()) -> bool:
        return run([PY, "-c", _REFUSED.format(operation)], cwd=root, writes=writes).exit == 0

    bus = run([SYSTEMD_RUN, "--user", "--quiet", "/bin/true"], cwd=root, writes=[],
              env={**os.environ, "XDG_RUNTIME_DIR": f"/run/user/{os.getuid()}"})
    return ConfineReport(Path("/proc/self/attr/current").read_text().strip(), {
        "home write refused": _refused(Path.home()),
        "/var/tmp write refused": _refused(Path("/var/tmp")),
        "write outside the root refused": _refused(root.parent),
        "root write permitted": _creates(root),
        "outbound TCP refused in a net=False child":
            refused_in_child("socket.create_connection(('127.0.0.1', 9), timeout=10)"),
        "outbound UDP refused in a net=False child":
            refused_in_child("socket.socket(socket.AF_INET, socket.SOCK_DGRAM).sendto(b'x', ('127.0.0.1', 9))"),
        # the child's own layer may write home, so only the orchestrator's, inherited, can refuse it
        "home write refused in a ledger.slice scope by the inherited layer":
            refused_in_child(f"open({str(home_probe)!r}, 'x').close(); os.unlink({str(home_probe)!r})",
                             writes=(Path.home(),)),
        "systemd-run --user refused in a net=False child": bus.exit != 0 and "Permission denied" in bus.output,
        "docker socket connect refused in a net=False child":
            refused_in_child("socket.socket(socket.AF_UNIX).connect('/var/run/docker.sock')"),
    })
