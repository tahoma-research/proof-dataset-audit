import ast
import os
import re
import shutil
import site
import socket
import subprocess
import time
from pathlib import Path

import pytest
from helpers import CONTAINER, ENV, PY, SRC, in_unit, toml

from ledger import confine, policy
from ledger.types import LedgerStop

PACKAGE = SRC / "ledger"
NETWORK_STEPS = {"ingest.fetch", "envbuild.fetch", "probes.install_toolchain", "probes.d14_cache_probe", "publish.push"}

# Prints how each operation fares; run once bare, once under the child confinement.
PROBE = r"""
import ctypes, errno, fcntl, mmap, os, socket, sys, termios
libc = ctypes.CDLL(None, use_errno=True)
def io_uring_setup():
    fd = libc.syscall(425, 1, ctypes.create_string_buffer(120))
    if fd < 0:
        raise OSError(ctypes.get_errno(), "io_uring_setup")
    os.close(fd)
def connect(port):  # a refused connection still means the connect itself was permitted
    with socket.socket() as s:
        try:
            s.connect(("127.0.0.1", port))
        except ConnectionRefusedError:
            pass
def attempt(name, operation):
    try:
        operation()
        print(name, "allowed")
    except OSError as e:
        print(name, errno.errorcode[e.errno])
attempt("unix-stream", lambda: socket.socket(socket.AF_UNIX, socket.SOCK_STREAM).close())
attempt("unix-dgram", lambda: socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM).close())
def pair(kind, *then):  # Python adds SOCK_CLOEXEC to the type; SOCK_NONBLOCK is added here
    a, b = socket.socketpair(socket.AF_UNIX, kind | socket.SOCK_NONBLOCK)
    with a, b:
        for operation in then:
            operation(a)
bus = f"/run/user/{os.getuid()}/bus"
attempt("pair-stream", lambda: pair(socket.SOCK_STREAM))
attempt("pair-dgram", lambda: pair(socket.SOCK_DGRAM))
attempt("pair-seqpacket", lambda: pair(socket.SOCK_SEQPACKET))
attempt("pair-to-bus", lambda: pair(socket.SOCK_STREAM, lambda a: a.connect(bus)))
attempt("pair-listen", lambda: pair(socket.SOCK_STREAM, lambda a: a.bind(f"\0ledger-probe-{os.getpid()}"),
                                    lambda a: a.listen()))
attempt("listen", lambda: socket.socket().listen())  # an unbound socket: listen() binds it itself
attempt("tcp", lambda: socket.socket(socket.AF_INET, socket.SOCK_STREAM).close())
attempt("udp6", lambda: socket.socket(socket.AF_INET6, socket.SOCK_DGRAM).close())
attempt("netlink", lambda: socket.socket(socket.AF_NETLINK, socket.SOCK_RAW).close())
attempt("connect-443", lambda: connect(443))
attempt("connect-local", lambda: connect(int(sys.argv[1])))  # a local service on another port
attempt("bind", lambda: socket.socket().bind(("127.0.0.1", 0)))
attempt("io_uring", io_uring_setup)
attempt("device-ioctl", lambda: fcntl.ioctl(os.open("/dev/zero", os.O_RDONLY), termios.TCGETS))
attempt("signal", lambda: os.kill(os.getppid(), 0))  # the parent is outside the child's domain
pid = os.fork()
if pid == 0:  # an i386 system call through int 0x80: mov eax, 20 (getpid); int 0x80; ret
    code = bytes.fromhex("b814000000cd80c3")
    page = mmap.mmap(-1, len(code), prot=mmap.PROT_READ | mmap.PROT_WRITE | mmap.PROT_EXEC)
    page.write(code)
    ctypes.CFUNCTYPE(ctypes.c_int)(ctypes.addressof(ctypes.c_char.from_buffer(page)))()
    os._exit(0)
status = os.waitpid(pid, 0)[1]
print("i386", f"signal-{os.WTERMSIG(status)}" if os.WIFSIGNALED(status) else "survived")
"""


def test_child_layers_block_sockets_signals_and_foreign_abis():
    """Under the child confinement every socket and socketpair fails with EACCES; with --tcp only AF_INET and
    AF_INET6 sockets and an AF_UNIX stream pair open, the pair reaches no named socket (the user bus) and listens
    on no abstract name, a TCP connect reaches port 443 only and no TCP bind or listen is allowed. Either way
    io_uring and an ioctl on a device fail with EACCES, a signal to a process outside the domain fails with EPERM,
    and an i386 system call kills the process (SIGSYS). The same probe outside the confinement is allowed and
    survives."""
    with socket.create_server(("127.0.0.1", 0)) as server:
        def outcomes(*prefix):
            run = in_unit(*prefix, PY, "-c", PROBE, server.getsockname()[1])
            return dict(line.split() for line in run.out.splitlines()) or run.err

        blocked = {"unix-stream": "EACCES", "unix-dgram": "EACCES", "pair-stream": "EACCES", "pair-dgram": "EACCES",
                   "pair-seqpacket": "EACCES", "pair-to-bus": "EACCES", "pair-listen": "EACCES", "listen": "EACCES",
                   "tcp": "EACCES", "udp6": "EACCES",
                   "netlink": "EACCES", "connect-443": "EACCES", "connect-local": "EACCES", "bind": "EACCES",
                   "io_uring": "EACCES", "device-ioctl": "EACCES", "signal": "EPERM", "i386": "signal-31"}
        connected = {"pair-to-bus": "EISCONN"}  # the pair is already connected
        assert outcomes() == dict.fromkeys(blocked, "allowed") | connected | {"device-ioctl": "ENOTTY",
                                                                              "i386": "survived"}
        assert outcomes(PY, "-m", "ledger._nonet", "--") == blocked
        assert outcomes(PY, "-m", "ledger._nonet", "--tcp", "--") == blocked | connected | dict.fromkeys(
            ["tcp", "udp6", "connect-443", "pair-stream"], "allowed")


# Each metadata call by its number, on a file of mode 0600 this uid owns, in a form that succeeds unconfined: the
# mode it has, owner and group -1 (unchanged), the current time, a user attribute set and then removed.
META_PROBE = r"""
import ctypes, errno, os, sys
libc = ctypes.CDLL(None, use_errno=True)
class XattrArgs(ctypes.Structure):
    _fields_ = [("value", ctypes.c_char_p), ("size", ctypes.c_uint32), ("flags", ctypes.c_uint32)]
path, fd, at, name = sys.argv[1].encode(), os.open(sys.argv[1], os.O_RDONLY), -100, b"user.ledger"  # -100: AT_FDCWD
calls = {"chmod": (90, path, 0o600), "fchmod": (91, fd, 0o600), "fchmodat": (268, at, path, 0o600),
         "fchmodat2": (452, at, path, 0o600, 0), "chown": (92, path, -1, -1), "fchown": (93, fd, -1, -1),
         "lchown": (94, path, -1, -1), "fchownat": (260, at, path, -1, -1, 0), "utime": (132, path, None),
         "utimes": (235, path, None), "futimesat": (261, at, path, None), "utimensat": (280, at, path, None, 0),
         "setxattr": (188, path, name, b"1", 1, 0), "removexattr": (197, path, name),
         "lsetxattr": (189, path, name, b"1", 1, 0), "lremovexattr": (198, path, name),
         "fsetxattr": (190, fd, name, b"1", 1, 0), "fremovexattr": (199, fd, name),
         "setxattrat": (463, at, path, 0, name, ctypes.byref(XattrArgs(b"1", 1, 0)), 16),
         "removexattrat": (466, at, path, 0, name)}
for call, args in calls.items():
    print(call, "allowed" if libc.syscall(*args) == 0 else errno.errorcode[ctypes.get_errno()])
"""


def test_no_meta_refuses_mode_owner_time_and_xattr_changes(tmp_path):
    """Landlock mediates no change to a file's mode, owner, timestamps or extended attributes. Under _nonet every
    call that changes an owner or an extended attribute fails with EPERM; under _nonet --no-meta, every one of
    them, so a file outside the call's writes keeps its mode. Unconfined, all are allowed."""
    (canary := tmp_path / "canary").write_text("")
    canary.chmod(0o600)

    def outcomes(*prefix):
        run = in_unit(*prefix, PY, "-c", META_PROBE, canary)
        return dict(line.split() for line in run.out.splitlines()) or run.err

    allowed = outcomes()
    assert set(allowed.values()) == {"allowed"} and len(allowed) == 20
    assert outcomes(PY, "-m", "ledger._nonet", "--") == allowed | {
        call: "EPERM" for call in allowed if "own" in call or "xattr" in call}
    assert outcomes(PY, "-m", "ledger._nonet", "--no-meta", "--") == dict.fromkeys(allowed, "EPERM")
    assert canary.stat().st_mode & 0o7777 == 0o600


# Each inode-flag ioctl on a file this uid owns, setting the flags it has: FS_IOC_SETFLAGS and FS_IOC32_SETFLAGS
# (which a 64-bit caller's file system does not know: ENOTTY) from FS_IOC_GETFLAGS, FS_IOC_FSSETXATTR from
# FS_IOC_FSGETXATTR.
FLAGS_PROBE = r"""
import errno, fcntl, os, sys
fd, flags, fsx = os.open(sys.argv[1], os.O_RDONLY), bytearray(8), bytearray(28)
fcntl.ioctl(fd, 0x80086601, flags)
fcntl.ioctl(fd, 0x801C581F, fsx)
for name, request, arg in (("setflags", 0x40086602, flags), ("setflags32", 0x40046602, flags[:4]),
                           ("fssetxattr", 0x401C5820, fsx)):
    try:
        fcntl.ioctl(fd, request, arg)
        print(name, "allowed")
    except OSError as e:
        print(name, errno.errorcode[e.errno])
"""


def test_inode_flag_ioctls_refused_in_every_child(tmp_path):
    """Landlock does not mediate a file's inode flags either: under _nonet, with or without --no-meta, each ioctl
    that sets them fails with EPERM. Unconfined, the two a 64-bit caller has succeed."""
    (target := tmp_path / "target").write_text("")

    def outcomes(*prefix):
        run = in_unit(*prefix, PY, "-c", FLAGS_PROBE, target)
        return dict(line.split() for line in run.out.splitlines()) or run.err

    assert outcomes() == {"setflags": "allowed", "setflags32": "ENOTTY", "fssetxattr": "allowed"}
    for options in (["--"], ["--no-meta", "--"]):
        assert outcomes(PY, "-m", "ledger._nonet", *options) == dict.fromkeys(
            ("setflags", "setflags32", "fssetxattr"), "EPERM")


def test_no_child_dumps_core():
    """Every child runs with RLIMIT_CORE soft and hard at 1 byte, even from a unit that allows core dumps, and in a
    scope that never swaps, memory-capped or not."""
    limit = ("import resource; print(resource.getrlimit(resource.RLIMIT_CORE)); "
             "print(open('/sys/fs/cgroup' + open('/proc/self/cgroup').read().split(':')[-1].strip()"
             " + '/memory.swap.max').read(), end='')")
    run = in_unit(PY, "-c", "import sys; from pathlib import Path; from ledger import confine; "
                  f"print(confine.run([sys.executable, '-c', {limit!r}], cwd=Path.cwd(), writes=[]).output, end='')",
                  flags=["--property=LimitCORE=infinity"])
    assert run.out == "(1, 1)\n0\n", run.err


def test_only_confine_spawns_processes():
    """Only confine, _nonet and _reporter start processes."""
    spawn = re.compile(r"\b(subprocess|Popen)\b|\bos\.(system|exec|spawn|posix_spawn|fork)")
    allowed = {"confine.py", "_nonet.py", "_reporter.py"}
    assert [p.name for p in PACKAGE.glob("*.py") if p.name not in allowed and spawn.search(p.read_text())] == []


def test_net_true_only_from_permitted_steps():
    """A child with TCP is started only from the five network steps."""
    callers = set()
    for path in PACKAGE.glob("*.py"):
        if path.name == "confine.py":
            continue
        for top in ast.parse(path.read_text()).body:
            for node in ast.walk(top):
                if isinstance(node, ast.Call) and getattr(node.func, "attr", getattr(node.func, "id", "")) == "run" \
                        and any(k.arg == "net" and not (isinstance(k.value, ast.Constant) and k.value.value is False)
                                for k in node.keywords):
                    callers.add(f"{path.stem}.{getattr(top, 'name', '<module>')}")
    assert callers <= NETWORK_STEPS


def test_stdlib_only_runtime():
    """Importing every module loads nothing outside the standard library."""
    check = (
        "import importlib, pkgutil, sys; sys.path.insert(0, sys.argv[1]); import ledger\n"
        "for m in pkgutil.iter_modules(ledger.__path__): importlib.import_module('ledger.' + m.name)\n"
        "print(sorted(n for n in sys.modules if n.split('.')[0] not in sys.stdlib_module_names | {'ledger', '__main__'}))")
    result = subprocess.run([PY, "-S", "-c", check, SRC], capture_output=True, text=True)
    assert (result.returncode, result.stdout) == (0, "[]\n"), result.stderr


def test_landlock_abi_below_6_fails_closed(make_policy, monkeypatch, tmp_path):
    """Below Landlock ABI 6, which the child layers' signal scoping needs, the host's policy refuses to continue
    rather than run unconfined. The container's runs at ABI 1 with each call's write layer, without the signal
    scope, and refuses where Landlock is absent."""
    monkeypatch.setattr(confine, "landlock_abi", lambda: 5)
    with pytest.raises(LedgerStop, match="ABI 5"):
        confine.apply_fs(policy.load(make_policy()))
    (tmp_path / "container.toml").write_text(toml(CONTAINER))
    monkeypatch.chdir(tmp_path)
    for name in ("_container", "_floor"):  # restored after the test
        monkeypatch.setattr(confine, name, getattr(confine, name))
    monkeypatch.setattr(confine, "landlock_abi", lambda: 1)
    assert confine.apply_fs(policy.load(tmp_path / "container.toml")) == \
        "Landlock ABI 1, each call's write layer (no signal scope below ABI 6) in the container"
    assert confine.handled(1) == (confine.FS_WRITE & ~(confine.REFER | confine.TRUNCATE | confine.IOCTL_DEV), 0)
    monkeypatch.setattr(confine, "landlock_abi", lambda: 0)
    with pytest.raises(LedgerStop, match="ABI 0: Landlock is unavailable"):
        confine.apply_fs(policy.load(tmp_path / "container.toml"))


def test_apply_fs_refuses_a_threaded_process(make_policy):
    """The Landlock layer binds only the calling thread, so apply_fs refuses while a second thread exists."""
    script = ("import sys, threading; from ledger import confine, policy\n"
              "threading.Thread(target=threading.Event().wait, daemon=True).start()\n"
              "confine.apply_fs(policy.load(sys.argv[1]))")
    result = subprocess.run([PY, "-c", script, make_policy()], capture_output=True, text=True, env=ENV)
    assert result.returncode == 1 and "one thread" in result.stderr, result.stderr


def test_child_gets_allowlisted_environment(tmp_path, monkeypatch):
    """A child sees the allowlisted variables and none of the parent's others: no token, no session bus; and
    git, there, never prompts or reads the system's attributes file."""
    bus = f"unix:path=/run/user/{os.getuid()}/bus"  # the real one: run's own systemctl calls use it
    for name, value in (("LAKE_PROBE", "1"), ("LEDGER_PROBE_TOKEN", "secret"), ("DBUS_SESSION_BUS_ADDRESS", bus)):
        monkeypatch.setenv(name, value)
    names = confine.run([PY, "-c", "import os; print(*os.environ, 'prompt=' + os.environ['GIT_TERMINAL_PROMPT'], "
                         "'attr=' + os.environ['GIT_ATTR_NOSYSTEM'])"], cwd=tmp_path, writes=[]).output.split()
    assert {"PATH", "LAKE_PROBE", "prompt=0", "attr=1"} <= set(names)
    assert not {"LEDGER_PROBE_TOKEN", "DBUS_SESSION_BUS_ADDRESS"} & set(names)


def test_output_is_bounded(tmp_path):
    """A call keeps the first OUTPUT_MAX bytes of its output and reads and discards the rest, so the call runs to
    its end and no amount of output fills the caller's memory: its output and log hold that prefix alone, and it is
    marked truncated. Output of exactly OUTPUT_MAX bytes is whole and not marked."""
    (tmp_path / "w").mkdir()
    flood = ("import sys; sys.stdout.write('x' * {}); sys.stdout.write('y' * (64 << 20)); sys.stdout.flush(); "
             "open('w/end', 'w').close(); sys.exit(3)")
    proc = confine.run([PY, "-c", flood.format(confine.OUTPUT_MAX)], cwd=tmp_path, writes=[tmp_path / "w"],
                       log=tmp_path / "log")
    assert (proc.exit, proc.output_truncated, len(proc.output), set(proc.output)) == (3, True, confine.OUTPUT_MAX, {"x"})
    assert proc.raw == proc.output.encode() and (tmp_path / "log").read_text() == proc.output
    assert (tmp_path / "w/end").exists()
    whole = confine.run([PY, "-c", f"print('x' * {confine.OUTPUT_MAX - 1})"], cwd=tmp_path, writes=[])
    assert (whole.output_truncated, len(whole.output)) == (False, confine.OUTPUT_MAX)


def test_git_runs_no_command_from_repository_or_user_config(tmp_path):
    """git, started by another command too, never reads the system's or the user's own config or the user's
    attributes file, and a git call refuses, before git starts, a repository whose config holds a key outside
    the allowlist: core.fsmonitor in either runs a command, or whose config is not a regular file (a FIFO would
    stall the check). A fresh repository's config is accepted. A `git` planted first on the call's PATH, a
    `ledger` package planted in its cwd, or a usercustomize module planted in its HOME's user site, never runs
    outside the child."""
    repo, home, tools = tmp_path / "repo", tmp_path / "home", tmp_path / "tools"
    outside = tmp_path / "ran-outside-the-child"  # the child may not write here; the caller may
    git = ["git", "-c", "user.name=t", "-c", "user.email=t@example.invalid", "-C", repo]
    subprocess.run(["git", "init", "-q", repo], check=True)
    (repo / "file").touch()
    subprocess.run([*git, "add", "file"], check=True)
    subprocess.run([*git, "commit", "-qm", "t"], check=True)
    home.mkdir()
    (home / ".gitconfig").write_text(f'[core]\n\tfsmonitor = "touch {repo}/user-config-ran; false"\n')
    tools.mkdir()
    (tools / "git").write_text(f'#!/bin/sh\ntouch {outside} 2>/dev/null\nexec /usr/bin/git "$@"\n')
    (tools / "git").chmod(0o755)
    (repo / "ledger").mkdir()
    (repo / "ledger/__init__.py").write_text(f"open({str(outside)!r}, 'w').close()\n")
    (user_site := home / Path(site.getusersitepackages()).relative_to(Path.home())).mkdir(parents=True)
    (user_site / "usercustomize.py").write_text(f"open({str(outside)!r}, 'w').close()\n")
    status = ["git", "--no-optional-locks", "status", "--porcelain"]
    env = {"PATH": f"{tools}:/usr/bin:/bin", "HOME": str(home)}
    assert confine.run(status, cwd=repo, writes=[repo], env=env).exit == 0
    (home / ".config/git").mkdir(parents=True)
    (home / ".config/git/attributes").write_text("* working-tree-encoding=UTF-7\n")
    assert confine.run(["/bin/sh", "-c", "/usr/bin/git check-attr -a file"], cwd=repo, writes=[], env=env).output == ""
    subprocess.run([*git, "config", "core.fsmonitor", f"touch {repo}/repo-config-ran; false"], check=True)
    with pytest.raises(LedgerStop, match="core.fsmonitor"):
        confine.run(status, cwd=repo, writes=[repo], env=env)
    (repo / ".git/config").unlink()
    (repo / ".git/config").symlink_to("/dev/null")
    with pytest.raises(LedgerStop, match="regular file"):
        confine.run(status, cwd=repo, writes=[repo], env=env)
    assert sorted(path.name for path in repo.iterdir()) == [".git", "file", "ledger"]
    assert not outside.exists()


def test_git_config_fifo_cannot_stall_the_check(tmp_path, monkeypatch):
    """A repository whose config is a FIFO, as a fetched package could leave, is refused within the config
    check's time limit instead of blocking the run."""
    subprocess.run(["git", "init", "-q", tmp_path], check=True)
    (tmp_path / ".git/config").unlink()
    os.mkfifo(tmp_path / ".git/config")
    monkeypatch.setattr(confine, "GIT_CHECK_S", 1)
    start = time.monotonic()
    with pytest.raises(LedgerStop, match="config"):
        confine.run([confine.GIT, "rev-parse", "HEAD"], cwd=tmp_path, writes=[])
    assert time.monotonic() - start < 10


def test_every_pin_lake_call_has_no_cache(tmp_path):
    """In the pin, rebuild, stop-loss, pin audit and proof-1b fixture trees, whatever the recipe says, a Lake call
    without --no-cache is refused before it starts."""
    for tree in ("env/pin", "env/rebuild/Pairs", "env/pin-seeded", "env/audit-pin", "fixtures-run/env/proof1b"):
        (cwd := tmp_path / tree).mkdir(parents=True)
        with pytest.raises(LedgerStop, match="no-cache"):
            confine.run(["lake", "build"], cwd=cwd, writes=[])
    cwd = tmp_path / "env/pin"
    assert confine.run([PY, "-c", "pass"], cwd=cwd, writes=[]).exit == 0
    confine.run(["lake", "--no-cache", "--version"], cwd=cwd, writes=[])  # not refused; lake need not exist here


def test_container_policy_runs_children_bare(tmp_path, monkeypatch):
    """Under the container's policy a child runs without a scope, even when a memory ceiling is asked for, and with
    `net` reaches any TCP port; without `net`, so whenever it may run proof code, the seccomp filter still refuses it
    every socket, so it reaches neither the container's host nor its network. A running call is polled against the policy's disk_floor_gb in the working directory, below which it
    is killed and the run stops."""
    (tmp_path / "container.toml").write_text(toml(CONTAINER | {"disk_floor_gb": 10**9}))
    monkeypatch.chdir(tmp_path)
    for name in ("_container", "_floor", "FLOOR_POLL_S"):  # restored after the test
        monkeypatch.setattr(confine, name, getattr(confine, name))
    assert confine.apply_fs(policy.load(tmp_path / "container.toml")) == \
        f"Landlock ABI {confine.landlock_abi()}, each call's write layer and signal scope in the container"
    with socket.create_server(("127.0.0.1", 0)) as server:
        reach = f"import socket; socket.create_connection(('127.0.0.1', {server.getsockname()[1]}), timeout=10).close()"
        refused, reached = (confine.run([PY, "-c", reach], cwd=tmp_path, writes=[], net=net) for net in (False, True))
    assert refused.exit != 0 and "PermissionError" in refused.output and reached.exit == 0, refused.output
    proc = confine.run([PY, "-c", "print(open('/proc/self/cgroup').read())"],
                       cwd=tmp_path, writes=[], memory_max_mb=100, unit_name="ledger-bare", log=tmp_path / "log")
    assert proc.exit == 0 and "ledger.slice" not in proc.output, proc.output
    confine.FLOOR_POLL_S = 0.2
    with pytest.raises(LedgerStop, match="free-space floor reached during ledger-call"):
        confine.run(["/bin/sh", "-c", "sleep 30"], cwd=tmp_path, writes=[])


def test_container_oom_from_memory_events(tmp_path, monkeypatch):
    """Under a container policy a call killed by SIGKILL, itself or as Lake reports a child so killed (exit 137), while
    the container cgroup's oom_kill count rises, is killed "oom", the rise its oom_kill; a rise during a call not so
    killed, another call's, counts 0; where memory.events is unreadable, oom_kill is None and nothing is "oom"."""
    monkeypatch.setattr(confine, "_container", True)
    monkeypatch.setattr(confine, "MEMORY_EVENTS", events := tmp_path / "memory.events")

    def call(end: str) -> tuple:
        events.write_text("oom 3\noom_kill 3\n")
        proc = confine.run(["/bin/sh", "-c", f"printf 'oom 5\\noom_kill 5\\n' > {events}; {end}"], cwd=tmp_path,
                           writes=[tmp_path])
        return proc.killed, proc.oom_kill
    assert [call(end) for end in ("kill -9 $$", "exit 137", "exit 0")] == [("oom", 2), ("oom", 2), (None, 0)]
    events.unlink()
    assert confine.run(["/bin/sh", "-c", "exit 137"], cwd=tmp_path, writes=[]).oom_kill is None


def test_container_timeout_kills_the_process_group(tmp_path, monkeypatch):
    """Under a container policy a call that reaches timeout_s is killed with every process it started, so no
    worker outlives the call."""
    monkeypatch.setattr(confine, "_container", True)
    # A shell starts in milliseconds even under I/O pressure, so the worker's pid is printed well inside the limit.
    proc = confine.run(["/bin/sh", "-c", "sleep 60 & echo $!; wait"], cwd=tmp_path, writes=[], timeout_s=5)
    stat = Path(f"/proc/{proc.output.split()[0]}/stat")

    def running() -> bool:  # a zombie has exited; a reaped process has no stat
        try:
            return stat.read_text().split()[2] != "Z"
        except (FileNotFoundError, ProcessLookupError):
            return False
    deadline = time.monotonic() + 10  # SIGKILL is delivered, not instant
    while running() and time.monotonic() < deadline:
        time.sleep(0.05)
    assert proc.killed == "wall-clock" and not running()


def test_container_timeout_after_the_command_exited(tmp_path, monkeypatch):
    """Under a container policy a command that has exited while a process outside its group holds its output open
    times out still unreaped, so its group is signalled while it exists: the call returns its wall-clock kill, and
    no failed signal replaces it."""
    monkeypatch.setattr(confine, "_container", True)
    proc = confine.run(["/bin/sh", "-c", "setsid sleep 2 &"], cwd=tmp_path, writes=[], timeout_s=1)
    assert proc.killed == "wall-clock"


def test_container_branch_no_systemd_write_layer(tmp_path, monkeypatch):
    """Under a container policy a leg's command runs without systemd-run, its memory peak comes from wait4, and the
    wall-clock kill still holds. It keeps the host's Landlock write layer: a call, with or without net, that rewrites
    the ledger's code or the toolchain is refused, so the next call starts under the seccomp filter and opens no
    socket."""
    monkeypatch.setattr(confine, "_container", True)
    for name in ("SYSTEMD_RUN", "SYSTEMCTL"):
        monkeypatch.setattr(confine, name, str(tmp_path / "absent"))
    shutil.copytree(SRC, tmp_path / "src", ignore=shutil.ignore_patterns("__pycache__"))
    monkeypatch.setattr(confine, "REPO", tmp_path)  # the ledger the children start, which the first call rewrites
    (lake := tmp_path / "toolchain/bin/lake").parent.mkdir(parents=True)
    lake.touch()
    (work := tmp_path / "work").mkdir()
    unfiltered = "import os, sys; command = sys.argv[sys.argv.index('--') + 1:]; os.execvp(command[0], command)"
    rewrite = (f"import sys\nfor path in sys.argv[1:]:\n    try:\n        open(path, 'w').write({unfiltered!r})\n"
               "    except PermissionError:\n        print('refused', path)")
    targets = [str(tmp_path / "src/ledger/_nonet.py"), str(lake)]
    for net in (False, True):
        rewritten = confine.run([PY, "-c", rewrite, *targets], cwd=work, writes=[work], net=net, timeout_s=60)
        assert rewritten.output.split() == ["refused", targets[0], "refused", targets[1]], rewritten.output
    reach = confine.run([PY, "-c", "import socket; socket.socket()"], cwd=work, writes=[work], timeout_s=60)
    assert "PermissionError" in reach.output, reach.output
    grow = "b = bytearray(200 << 20); import time; time.sleep({})"
    done = confine.run([PY, "-c", grow.format(0)], cwd=tmp_path, writes=[], timeout_s=60)
    assert (done.exit, done.killed) == (0, None)
    assert 200 << 10 < done.peak_mem_kb < 400 << 10
    killed = confine.run([PY, "-c", grow.format(60)], cwd=tmp_path, writes=[], timeout_s=3)
    assert killed.killed == "wall-clock" and 200 << 10 < killed.peak_mem_kb < 400 << 10


def test_call_without_timeout_is_bounded(tmp_path, monkeypatch):
    """A call that passes no timeout_s is killed at the published per-pair limit, so none can hang until the
    unit's own timeout."""
    monkeypatch.setattr(confine, "_container", True)
    (tmp_path / "recipe").mkdir()
    (tmp_path / "recipe/constants.toml").write_text("[limits]\nper_pair_wall_clock_s = 1\n")
    (tmp_path / "src").symlink_to(SRC)  # the ledger the child layers start
    monkeypatch.setattr(confine, "REPO", tmp_path)
    proc = confine.run([PY, "-c", "import time; time.sleep(60)"], cwd=tmp_path, writes=[])
    assert proc.killed == "wall-clock"


def test_leftover_scope_stop_failure_stops(root, monkeypatch):
    """A failure to stop the leftover scopes stops the run with a reason, rather than an unexplained crash."""
    monkeypatch.setattr(confine, "SYSTEMCTL", "/bin/false")
    with pytest.raises(LedgerStop, match="leftover scopes"):
        confine.stop_leftover_scopes(root)


def test_host_lock_serialises_calls(tmp_path):
    """With LEDGER_HOST_LOCK set, calls from two processes run one at a time: the second child starts only after
    the first has ended, and the second process says on stderr that it waits. A missing lock file stops the call."""
    (lock := tmp_path / "host.lock").touch()
    call = ("from pathlib import Path; from ledger import confine; print(confine.run(['/bin/sh', '-c', "
            "'date +%s.%N; sleep 1; date +%s.%N'], cwd=Path.cwd(), writes=[]).output, end='')")
    run = in_unit("/bin/sh", "-c", f'{PY} -c "$0" & {PY} -c "$0"; wait; LEDGER_HOST_LOCK=$1 {PY} -c "$0"', call,
                  tmp_path / "absent", env={"LEDGER_HOST_LOCK": lock})
    times = [float(t) for t in run.out.split()]  # each process prints its child's start and end at once
    assert len(times) == 4 and times == sorted(times), run.out + run.err
    assert run.err.count(f"waiting for the host lock {lock}\n") == 1, run.err
    assert f"LedgerStop: the host lock {tmp_path / 'absent'}: No such file or directory\n" in run.err, run.err


FLOOR = """
import sys, time
from ledger import confine, policy
from ledger.types import LedgerStop
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
confine.FLOOR_POLL_S = 1
(work := pol.root / "work").mkdir()
for script in ("sleep 3; touch late", "(sleep 3; touch late) &"):  # the second leaves its output open
    try:
        confine.run(["/bin/sh", "-c", script], cwd=work, writes=[work], no_meta=True)
    except LedgerStop as e:
        print(e)
time.sleep(3)
print(sorted(p.name for p in work.iterdir()))
confine._floor = confine._floor[0], 0
print(confine.run(["/bin/sh", "-c", "sleep 3; echo above"], cwd=work, writes=[]).output.strip())
print(confine.run(["/bin/sh", "-c", "sleep 2; wc -c"], cwd=work, writes=[], input=b"x" * (1 << 20)).output.strip())
"""


def test_free_space_floor_kills_the_call(make_policy):
    """A call that finds free space on the policy's disk_floor_mount below its disk_floor_gb, at one of its
    checks while the child runs or its output is open, kills the child with its scope and stops the run; above the
    floor, such a call runs to its end. A call given input (git's), which communicate cannot resume writing after a
    check, is not checked and writes the whole of it."""
    run = in_unit(PY, "-c", FLOOR, make_policy(disk_floor_gb=10**9), timeout=60)
    expected = r"(free-space floor reached during ledger-call-\d+-\d+\n){2}\[\]\nabove\n1048576\n"
    assert re.fullmatch(expected, run.out), run.out + run.err
