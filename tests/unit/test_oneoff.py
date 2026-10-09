import os
import re
from datetime import date, datetime

from helpers import CLI, PY, hold_lock, in_unit

from ledger import cli, confine, gatefile, policy


def build(env, n):
    return ["env", "build", "--env", env, "--attempt", str(n)]


def test_instance_table():
    """The fixed one-off instances, the command each runs and the ceiling line each needs."""
    # covers: test_attempt_from_instance_name
    assert cli.ONEOFF == {
        "probe-d7": (["probe", "d7"], "ceiling:d7-probes"),
        "mathlib-1": (build("pin", 1), "ceiling:d14-measurement"),
        "mathlib-2": (build("pin", 2), "ceiling:d14-measurement"),
        "mathlib-3": (build("pin", 3), "ceiling:d14-measurement"),
        "mathlib-seeded": (build("pin-seeded", 1), "ceiling:d14-stop-loss"),
        "measure-d14": (["measure", "d14"], "ceiling:d14-measurement"),
        "legacy-1": (build("legacy", 1), "ceiling:d21-legacy"),
        "legacy-2": (build("legacy", 2), "ceiling:d21-legacy"),
        "legacy-3": (build("legacy", 3), "ceiling:d21-legacy"),
        "freeze": (["freeze"], "ceiling:d21-pilot"),
        "fixtures": (["fixtures"], "ceiling:d21-pilot"),
        "proof1b": (["fixtures", "--proof1b"], "ceiling:d21-pilot"),
        "pilot-d21": (["pilot", "d21"], "ceiling:d21-pilot"),
        "pilot-d21-replay": (["pilot", "d21", "--replay"], "ceiling:d21-pilot"),
    }


def test_refuses_without_ceiling_line(make_policy, root, code_repo):
    """A one-off whose milestone has no ceiling line in the gate file does not start; with it, the instance's command
    runs: the build attempt its name numbers."""
    path = make_policy()
    run = in_unit(PY, "-c", CLI, code_repo, "oneoff", "mathlib-2", "--policy", path)
    assert run.code == 2 and "no `ceiling:d14-measurement` gate line" in run.err
    report = next(root.glob("runs/*/report.md"))
    landlock = rf"Landlock ABI \d+, writes beneath {re.escape(str(root))}, /dev/shm, /dev/null"
    assert re.search(rf"- confinement: {landlock}, self-test passed\n", report.read_text())
    gatefile.append(policy.load(path), "ceiling:d14-measurement", "24h per attempt", "assistant", "three attempts",
                    date.today())
    run = in_unit(PY, "-c", CLI, code_repo, "oneoff", "mathlib-2", "--policy", path)
    assert run.code == 2 and "pin: attempt 2 is out of order" in run.err, run.err


def test_contention_exits_1_no_skipped_night(make_policy, root):
    """A one-off, or a stage, finding the lock held exits 1 with a run report naming the holder, and writes no
    gate line."""
    path = make_policy()
    with hold_lock(root) as holder:
        runs = [in_unit(PY, "-m", "ledger", *argv, "--policy", path) for argv in (["oneoff", "probe-d7"], ["stage"])]
    assert [run.code for run in runs] == [1, 1], [run.err for run in runs]
    reports = [report.read_text() for report in root.glob("runs/*/report.md")]
    assert len(reports) == 2 and all(f"pid {holder.pid}" in report for report in reports)
    assert gatefile.rows(policy.load(path)) == []


def test_failed_self_test_stops(make_policy, root):
    """A lock-taking command whose confinement self-test fails stops before its work, and says why."""
    path = make_policy()
    root.parent.chmod(0o555)  # the self-test can no longer show a write outside the root being refused
    try:
        run = in_unit(PY, "-m", "ledger", "oneoff", "probe-d7", "--policy", path)
    finally:
        root.parent.chmod(0o755)
    assert run.code == 2 and "self-test failed (label unconfined): write outside the root refused" in run.err
    assert "self-test failed" in next(root.glob("runs/*/report.md")).read_text()


def test_unexpected_error_is_a_reported_stop(make_policy, root, monkeypatch, capsys):
    """Any error, not only a failed precondition, ends in exit 2 and a run report saying it needs the operator. Two
    runs stopping in the same second each get their own run directory: the second waits for the next second."""
    def apply_fs(pol):  # in place of the real one, which would also confine this test process
        raise ValueError("unexpected")
    monkeypatch.setattr(confine, "apply_fs", apply_fs)
    clock = iter([datetime(2026, 1, 2, 3, 4, 5)] * 2 + [datetime(2026, 1, 2, 3, 4, 6)])
    monkeypatch.setattr(cli, "datetime", type("Clock", (), {"now": lambda: next(clock)}))
    argv = ["oneoff", "probe-d7", "--policy", str(make_policy())]
    assert cli.main(argv) == cli.main(argv) == 2
    assert "Traceback" in capsys.readouterr().err
    for run in ("2026-01-02T030405", "2026-01-02T030406"):
        assert ("- result: stopped: ValueError: unexpected\n- needs the operator: yes: the run stopped: ValueError: "
                "unexpected\n") in (root / "runs" / run / "report.md").read_text()


def test_run_starts_with_fresh_child_state(make_policy, root, monkeypatch):
    """Nothing a child wrote in an earlier run is input to the next: xdg-cache/ starts every run empty, an earlier
    run's tmp/<run-id>/ is removed, and the run's TMPDIR, which children inherit, is its own tmp/<run-id>/, named like
    its run directory."""
    (root / "xdg-cache/mathlib").mkdir(parents=True)
    (root / "xdg-cache/mathlib/planted.olean").touch()
    for name in ("2026-01-02T030405", "not-a-run"):
        (root / "tmp" / name / "left").mkdir(parents=True)
    monkeypatch.setattr(confine, "apply_fs", lambda pol: None)  # as under a container policy: no self-test
    monkeypatch.setenv("TMPDIR", "/unused")  # restored after the test
    assert cli.main(["oneoff", "probe-d7", "--policy", str(make_policy())]) == 2
    run_id = next(root.glob("runs/*")).name
    assert list((root / "xdg-cache").iterdir()) == []
    assert os.environ["TMPDIR"] == str(root / "tmp" / run_id) and (root / "tmp" / run_id).is_dir()
    assert sorted(path.name for path in (root / "tmp").iterdir()) == sorted([run_id, "not-a-run"])
