import json
import os
import time
from datetime import date, timedelta

from helpers import PY, hold_lock, in_unit

from ledger import gatefile, policy


def test_nightly_exits_before_lock_on_rebuild_night(make_policy, root):
    """On a rebuild night the nightly exits 0 before taking the run lock, and on any other night so does rebuild; where
    a rebuild attempt has held the lock since an earlier night, the nightly writes the skipped night, cause d30-rebuild,
    and where the rebuild took the lock tonight, or the lock file from an earlier night names no rebuild, none. Once a
    kill is recorded, both exit on any night, and neither writes a skipped night."""
    pol = policy.load(path := make_policy())
    gatefile.append(pol, "d0", "met", "operator", "pin commit", date.today() - timedelta(days=31))
    (results := root / "results").mkdir()
    with hold_lock(root, "rebuild") as holder:
        for n, (command, result) in enumerate((("nightly", "fail"), ("nightly", "fail"), ("rebuild", "pass"),
                                               ("nightly", "fail"), ("rebuild", "fail"), ("nightly", "fail"))):
            if n in (1, 3):  # step 0 reads the holder's lock file of tonight; these, an earlier night's naming
                # PID 1, init, which is no rebuild, then the holder
                (root / "lock").write_text(f"{holder.pid if n == 3 else 1}\n")
                os.utime(root / "lock", (time.time() - 86400,) * 2)
            if n == 4:
                gatefile.append(pol, "kill", "over the cap", "pipeline", "test", date.today())
            (results / "progress.json").write_text(json.dumps(
                {"rebuild": {"attempts": [{"n": 1, "date": "2026-12-02", "result": result}]}}))
            run = in_unit(PY, "-m", "ledger", command, "--policy", path)
            assert run.code == 0, run.err
    rows = gatefile.rows(pol)
    assert [row[1] for row in rows] == ["d0", "skipped-night", "kill"]
    assert rows[1][4] == f"lock held by pid {holder.pid}; cause=d30-rebuild"
    reports = [path.read_text() for path in sorted(root.glob("runs/*/report.md"))]
    assert all("skipped: the night's work: D+31: a rebuild night; the rebuild unit runs" in r for r in reports[:2])
    assert "skipped: the night's work: D+31: not a rebuild night" in reports[2]
    assert (f"skipped: the night's work: D+31: the rebuild attempt begun on an earlier night holds the run lock, pid "
            f"{holder.pid}") in reports[3]
    assert all("skipped: the night's work: D+31: a kill is recorded" in report for report in reports[4:])
