import json
import os
import subprocess
import time

import pytest
from helpers import PY, SRC, in_unit, write_policy

from ledger import confine

pytestmark = pytest.mark.integration

SELF_TEST = """
import sys
from ledger import confine, policy
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
report = confine.self_test(pol)
print(report)
sys.exit(0 if report.ok else 1)
"""
SCOPED = """
import json, sys
from ledger import confine, policy
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
proc = confine.run([sys.executable, "-c", sys.argv[3]], cwd=pol.root, writes=[], env={"XDG_RUNTIME_DIR": str(pol.root / "runtime")},
                   memory_max_mb=150, unit_name=confine.scope_name(pol.root, sys.argv[2]), log=pol.root / "scoped.log")
print(json.dumps(proc.__dict__, default=bytes.decode))
"""
GREEDY = """
import os
print(open("/proc/self/cgroup").read().strip(), os.environ["XDG_RUNTIME_DIR"], flush=True)
chunks = []
while True:
    chunks.append(b"x" * (8 << 20))
"""
LEG = """
import sys
from ledger import confine, policy
pol = policy.load(sys.argv[1])
confine.run(["/usr/bin/sleep", "300"], cwd=pol.root, writes=[], memory_max_mb=100, unit_name=confine.scope_name(pol.root, sys.argv[2]),
            log=pol.root / "leg.log")
"""
CALLS = """
import sys, time
from ledger import confine, policy
from ledger.types import LedgerStop
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
work, logs = pol.root / "work", pol.root / "runs/r/logs"
work.mkdir()
logs.mkdir(parents=True)
try:
    confine.run(["/bin/true"], cwd=work, writes=[work], log=work / "step.log")
except LedgerStop:
    print("refused")
standin = pol.root / "standin"
standin.write_text("ORIGINAL")
confine.run(["/bin/ln", "-s", str(standin), str(logs / "planted.log")], cwd=work, writes=[logs.parent])
try:
    confine.run(["/bin/true"], cwd=work, writes=[work], log=logs / "planted.log")
except OSError as e:
    print("not followed", e.errno, standin.read_text())
child = ["/bin/sh", "-c", sys.argv[3].format(work=work, logs=logs)]
plain = confine.run(child, cwd=work, writes=[work])
scoped = confine.run(child, cwd=work, writes=[work], memory_max_mb=100, log=logs / "step.log",
                     unit_name=confine.scope_name(pol.root, sys.argv[2]))
time.sleep(2)  # past the moment a surviving daemon would write
print(plain.exit, scoped.exit, sorted(p.name for p in work.iterdir()), (logs / "step.log").read_text() == scoped.output)
"""
PLANT = ("ln -s {work}/forged {logs}/step.log.reporter.json; ln -s {work}/forged {logs}/step.log; "
         "setsid sh -c 'sleep 1; echo forged > {work}/late' </dev/null >/dev/null 2>&1 & exit 137")
TOOLS = """
import sys
from ledger import confine, policy
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
work = pol.root / "toy"
work.mkdir()
(work / "lakefile.toml").write_text('name = "toy"\\ndefaultTargets = ["Toy"]\\n\\n[[lean_lib]]\\nname = "Toy"\\n')
(work / "Toy.lean").write_text("theorem toy : 1 + 1 = 2 := rfl\\n")
env = {"PATH": sys.argv[2] + ":/usr/bin:/bin", "HOME": str(pol.root), "TMPDIR": str(pol.root)}
for step in (["git", "init", "-q"],
             ["git", "-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-q", "--allow-empty", "-m", "t"],
             ["lean", "Toy.lean"],
             ["lake", "--no-cache", "build"],
             ["lake", "--no-cache", "env", "leanchecker", "Toy"]):
    proc = confine.run(step, cwd=work, writes=[work], env=env)
    print(" ".join(step[:2]), proc.exit, proc.output.strip()[-300:] if proc.exit else "")
"""
WRITES = """
import sys
from ledger import confine, policy
from ledger.types import LedgerStop
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
root, public = pol.root, pol.root / "public"
git = ["git", "-c", "user.name=t", "-c", "user.email=t@example.invalid"]
env = {"PATH": "/usr/bin:/bin", "HOME": str(root / "tmp")}
(public / ".git").mkdir()
confine.run([*git, "init", "-q"], cwd=public, writes=[public / ".git"], env=env)
for tree in (public, root, public / "src/ledger", public / "templates"):
    try:
        confine.run(["/bin/true"], cwd=root, writes=[tree])
    except LedgerStop:
        print(tree.name, "refused as a write path")
probe = "import sys\\nfor p in sys.argv[1:]:\\n    try:\\n        open(p, 'a').close(); print(p, 'written')\\n    except PermissionError:\\n        print(p, 'refused')"
print(confine.run([sys.executable, "-c", probe, *sys.argv[2:]], cwd=root, writes=[root / "work", root / "tmp"]).output, end="")
hook = public / ".git/hooks/pre-commit"
hook.write_text("#!/bin/sh\\ntouch hook-ran\\n")
hook.chmod(0o755)
commit = confine.run([*git, "commit", "-q", "--allow-empty", "-m", "t"], cwd=public, writes=[public / ".git"],
                     env=env)
print("commit", commit.exit, "hook", "ran" if (public / "hook-ran").exists() else "skipped", commit.output)
"""


TIMEOUT = """
import json, sys
from ledger import confine, policy
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
plain = confine.run(["/usr/bin/sleep", "300"], cwd=pol.root, writes=[], timeout_s=2)
capped = confine.run(["/usr/bin/sleep", "300"], cwd=pol.root, writes=[], timeout_s=2, memory_max_mb=100,
                     log=pol.root / "timeout.log", unit_name=confine.scope_name(pol.root, sys.argv[2]))
held = confine.run(["/bin/sh", "-c", "setsid /usr/bin/sleep 300 & /usr/bin/sleep 300"], cwd=pol.root, writes=[],
                   timeout_s=2)  # a descendant in a session of its own holds the output open
print(json.dumps([plain.killed, plain.exit, round(plain.wall_s), capped.killed, capped.peak_mem_kb > 0,
                  held.killed, round(held.wall_s)]))
"""


def scope_state(unit: str) -> str:
    return subprocess.run(["systemctl", "--user", "show", "-P", "ActiveState", f"{unit}.scope"],
                          capture_output=True, text=True).stdout.strip()


def wait_for(condition, timeout=30):
    deadline = time.monotonic() + timeout
    while not condition():
        assert time.monotonic() < deadline, "condition not reached in time"
        time.sleep(0.2)


def test_landlock_self_test_from_unit(dev_root, tmp_path):
    """From a systemd user unit: writes to home, /var/tmp and the volume outside the ledger root are refused
    and the root is writable; a net=False child cannot connect over TCP; the restriction carries into a
    ledger.slice scope; and both escapes fail from a net=False child, asking the user manager for a
    service over D-Bus and connecting to the docker socket."""
    # covers: test_self_test_reports, test_lean_invocations_are_netless
    # covers: test_escape_via_user_bus_fails, test_docker_socket_connect_fails
    run = in_unit(PY, "-c", SELF_TEST, write_policy(tmp_path / "policy.toml", dev_root))
    assert run.out.splitlines() == [
        "label: unconfined",
        "ok   home write refused",
        "ok   /var/tmp write refused",
        "ok   write outside the root refused",
        "ok   root write permitted",
        "ok   outbound TCP refused in a net=False child",
        "ok   outbound UDP refused in a net=False child",
        "ok   home write refused in a ledger.slice scope by the inherited layer",
        "ok   systemd-run --user refused in a net=False child",
        "ok   docker socket connect refused in a net=False child",
    ], run.err
    assert run.code == 0


def test_reporter_reads_peak_and_oom_before_exit(make_policy, root):
    """A scoped child over its 150 MB ceiling is OOM-killed; the in-scope reporter survives it
    (OOMPolicy=continue) and records the kill and the peak before the scope's cgroup vanishes. The scope
    sits in ledger.slice, and its child has the redirected runtime directory while systemd-run had the real one."""
    # covers: test_oom_policy_continue_reporter_survives, test_scope_in_ledger_slice
    # covers: test_scope_child_gets_redirected_runtime_dir
    leg = f"oomtest-{os.getpid()}-a1"
    run = in_unit(PY, "-c", SCOPED, make_policy(), leg, GREEDY)
    assert run.code == 0, run.err
    proc = json.loads(run.out)
    assert (proc["killed"], proc["exit"]) == ("oom", -9) and proc["oom_kill"] >= 1
    assert 100_000 < proc["peak_mem_kb"] <= 150 * 1024
    cgroup, runtime = proc["output"].splitlines()[0].split()
    assert cgroup.endswith(f"/ledger.slice/{confine.scope_name(root, leg)}.scope") and runtime == str(root / "runtime")


def test_scopes_bound_to_invoking_unit_no_orphans(make_policy, root):
    """A leg scope stops with the oneshot that started it, both when the oneshot reaches TimeoutStartSec
    and when its main process is SIGKILLed."""
    for attempt, timeout in ((1, ["--property=TimeoutStartSec=5"]), (2, [])):
        leg, service = f"orphantest-{os.getpid()}-a{attempt}", f"ledger-orphantest-service-{os.getpid()}-{attempt}"
        subprocess.run(["systemd-run", "--user", "--quiet", "--collect", "--no-block", f"--unit={service}",
                        "--property=Type=oneshot", *timeout, f"--setenv=PYTHONPATH={SRC}", PY, "-c", LEG,
                        make_policy(), leg], check=True)
        scope = confine.scope_name(root, leg)
        wait_for(lambda: scope_state(scope) == "active")
        if not timeout:
            subprocess.run(["systemctl", "--user", "kill", "--signal=KILL", "--kill-whom=main", f"{service}.service"],
                           check=True)
        wait_for(lambda: scope_state(scope) == "inactive")


def test_call_leaves_nothing_behind(make_policy, root):
    """A child cannot outlive its call, forge its exit status or steer the log: a log where the call writes is
    refused, a symlink an earlier call planted where a later call's log goes is not followed, and a failing
    child that tries to plant symlinks in place of its log and the reporter's file and leaves a daemon to
    write later exits 137, its own status, its daemon killed with its scope, whether or not it is
    memory-capped."""
    run = in_unit(PY, "-c", CALLS, make_policy(), f"callstest-{os.getpid()}-a1", PLANT)
    assert run.out.splitlines() == ["refused", "not followed 40 ORIGINAL", "137 137 [] True"], run.out + run.err


def test_leftover_scopes_stopped_after_lock(make_policy, root, tmp_path):
    """Having taken the run lock, ledger stops the scopes a killed run on its root left behind, and no
    other scope: another root's scope runs on."""
    ours, theirs = (confine.scope_name(r, f"leftovertest-{os.getpid()}") for r in (root, tmp_path / "other"))
    leftovers = [subprocess.Popen(["systemd-run", "--user", "--scope", "--quiet", f"--unit={unit}",
                                   "--slice=ledger.slice", "/usr/bin/sleep", "300"]) for unit in (ours, theirs)]
    try:
        wait_for(lambda: scope_state(ours) == scope_state(theirs) == "active")
        run = in_unit(PY, "-m", "ledger", "oneoff", "probe-d7", "--policy", make_policy())
        assert run.code == 2 and "ceiling:d7-probes" in run.err, run.err  # it took the lock and went on
        assert (scope_state(ours), scope_state(theirs)) == ("inactive", "active")
    finally:
        for leftover in leftovers:
            leftover.kill()


def test_child_cannot_write_policy_or_code(root):
    """A child writes only beneath the paths its call names: never the policy, the lock, the gate file or
    the public tree's code, templates and constants, even though the run itself may write the whole root: a
    call naming a path that holds any of them, or lies within one, is refused. git writing the public tree names
    only its .git and runs no hook."""
    for tree in ("policy", "gates", "work", "tmp", "public/src/ledger", "public/lean", "public/recipe",
                 "public/classifier"):
        (root / tree).mkdir(parents=True)
    for existing in ("lock", "gates/GATES.md", "public/src/ledger/_nonet.py", "public/recipe/constants.toml"):
        (root / existing).write_text("")
    refused = ["policy/operator.toml", "policy/new.toml", "lock", "gates/GATES.md", "public/src/ledger/_nonet.py",
               "public/lean/New.lean", "public/recipe/constants.toml", "public/classifier/table.toml",
               "public/.git/hooks/pre-commit", "public/.git/config"]
    run = in_unit(PY, "-c", WRITES, write_policy(root / "policy/operator.toml", root), *refused, "work/out", "tmp/out")
    assert run.out.splitlines() == ["public refused as a write path", "root refused as a write path",
                                    "ledger refused as a write path", "templates refused as a write path",
                                    *(f"{path} refused" for path in refused), "work/out written", "tmp/out written",
                                    "commit 0 hook skipped "], run.out + run.err


def test_git_and_lean_work_under_seccomp(make_policy, lean_bin):
    """git, lean, lake and leanchecker all work under the full confinement, the AF_UNIX block included."""
    run = in_unit(PY, "-c", TOOLS, make_policy(), lean_bin)
    assert run.out.splitlines() == ["git init 0 ", "git -c 0 ", "lean Toy.lean 0 ", "lake --no-cache 0 ",
                                    "lake --no-cache 0 "], run.out + run.err


def test_timeout_kills_the_scope(make_policy, root):
    """A call that outlives `timeout_s` is killed with its scope at the limit, plain, memory-capped (its peak
    read first) or with a descendant in a session of its own holding the output open, and reports
    `killed == "wall-clock"`."""
    leg = f"timeouttest-{os.getpid()}-a1"
    run = in_unit(PY, "-c", TIMEOUT, make_policy(), leg, timeout=60)
    assert run.out.splitlines() == ['["wall-clock", -9, 2, "wall-clock", true, "wall-clock", 2]'], run.out + run.err
    assert scope_state(confine.scope_name(root, leg)) == "inactive"
