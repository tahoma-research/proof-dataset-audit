import time
from datetime import date, timedelta

import pytest
from helpers import PY, hold_lock, in_unit

from ledger import cli, gatefile, policy, preflight
from ledger.types import LedgerStop

# `ledger <argv[1:]>`, rebuild waiting a second for the run lock.
WAIT_1S = "import sys; from ledger import cli; cli.LOCK_WAIT_S = 1; sys.exit(cli.main(sys.argv[1:]))"
CHECK_UNDER_LOCK = (
    "import sys; from pathlib import Path; from ledger import confine, constants, policy, preflight\n"
    "pol = policy.load(sys.argv[1]); assert preflight.lock(pol.root) is None; confine.apply_fs(pol)\n"
    "print('\\n'.join(preflight.check(pol, constants.load(Path(sys.argv[2])))))")


def test_ledger_takes_lock_itself_writes_pid(make_policy, root):
    """ledger takes the run lock itself, with no wrapper, and writes its own PID into it."""
    run = in_unit(PY, "-m", "ledger", "oneoff", "probe-d7", "--policy", make_policy())
    assert run.code == 2 and "ceiling:d7-probes" in run.err  # past the lock, stopped at the ceiling check
    assert (root / "lock").read_text() == f"{run.pid}\n"


def test_helper_returns_holder_pid(root):
    """On contention the helper returns the holder's PID from the lock file, or "unknown" when the file
    holds anything else."""
    with hold_lock(root) as holder:
        assert preflight.lock(root) == str(holder.pid)
        (root / "lock").write_bytes(b"\xff not a pid")
        assert preflight.lock(root) == "unknown"


def test_lock_symlink_refused(root, tmp_path):
    """The lock is taken, and read on a rebuild night, before the confinement exists, so a symlink planted in its
    place is refused rather than followed to a file outside the root."""
    (target := tmp_path / "target").write_text("keep\n")
    (root / "lock").symlink_to(target)
    with pytest.raises(LedgerStop, match="run lock"):
        preflight.lock(root)
    with pytest.raises(OSError, match="symbolic links"):
        cli._overrun(root, date.today() + timedelta(days=1))
    assert target.read_text() == "keep\n"


@pytest.mark.parametrize("command, day, holder, cause", [("nightly", 25, (), "lock"),
                                                    ("rebuild", 30, ("rebuild",), "d30-rebuild")],
                         ids=["test_second_run_logs_skipped_night_with_pid", "test_rebuild_contention_skipped_night"])
def test_contention_on_its_night_is_a_skipped_night(make_policy, root, command, day, holder, cause):
    """A nightly run, on a pass-1 night, finding the lock held, and a rebuild, on a rebuild night, finding it held
    still after its wait, each write a skipped-night line naming the holder's PID and what it is, write a run report
    naming it, and exit 0."""
    path = make_policy()
    gatefile.append(policy.load(path), "d0", "met", "operator", "pin commit", date.today() - timedelta(days=day))
    with hold_lock(root, *holder) as held:
        start = time.monotonic()
        run = in_unit(PY, "-c", WAIT_1S, command, "--policy", path)
    assert run.code == 0 and (command == "nightly" or time.monotonic() - start > 1), run.err
    assert [row[1:] for row in gatefile.rows(policy.load(path))][1:] == [
        ("skipped-night", "skipped", "pipeline", f"lock held by pid {held.pid}; cause={cause}")]
    assert f"the run lock is held by pid {held.pid}" in next(root.glob("runs/*/report.md")).read_text()


def test_preflight_does_not_relock(make_policy, code_repo):
    """Preflight checks the lock this process holds and never takes it again: a second flock from the
    same process would always find the lock held."""
    run = in_unit(PY, "-c", CHECK_UNDER_LOCK, make_policy(), code_repo)
    assert run.code == 0 and "run lock: held by this process" in run.out, run.err
