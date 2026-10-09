from datetime import date, timedelta

import pytest

from ledger import modes

D0 = date(2026, 11, 2)


def attempts(*results: str) -> dict:
    return {"rebuild": {"attempts": [{"n": n, "date": "2026-12-02", "result": r} for n, r in enumerate(results, 1)]}}


def check(state: str, extension: str = "unspent") -> dict:
    return {"aggregate": {"state": state, "reruns_used": 0, "extension": extension}}


@pytest.mark.parametrize("day, progress, mode, reason", [
    (10, {}, "exit", "pass 1 starts on D+22"),  # D+7 to D+14
    (17, {}, "exit", "pass 1 starts on D+22"),  # D+15 to D+20
    (21, {}, "exit", "pass 1 starts on D+22"),  # D+21
    (25, {}, "pass1", "a pass-1 night"),  # D+22 to D+29
    (30, {}, "exit", "rebuild night"),  # D+30
    (35, attempts("fail"), "exit", "rebuild night"),  # D+31 to D+43, a failed attempt and fewer than three
    (45, check("replay-pending"), "aggregate", "the D+44 check, state replay-pending"),  # D+44 to D+46
    (50, check("replay-returned"), "exit", "replay-returned"),  # after D+46
    (22, {}, "pass1", "a pass-1 night"),
    (29, attempts(), "pass1", "a pass-1 night"),
    (31, attempts(), "exit", "rebuild night"),
    (31, attempts("pass"), "pass1", "a pass-1 night"),
    (43, attempts("fail", "fail", "fail"), "pass1", "a pass-1 night"),
    (44, {}, "aggregate", "the D+44 check, state build-pending"),
    (46, check("replay-unavailable"), "exit", "replay-unavailable"),
    (47, check("replay-pending"), "exit", "past the D+44 check's last night"),
    (47, check("rejected-rerun-pending", "spent"), "aggregate", "the D+44 check, state rejected-rerun-pending"),
    (48, check("rejected-rerun-pending", "spent"), "exit", "past the D+44 check's last night"),
], ids=[*(f"test_row_{n}" for n in range(1, 9)),
        *(f"test_boundary_d{k}" for k in (22, 29, "31_no_attempt", 31, 43, 44, 46, 47, "47_extension", 48))])
def test_mode(day, progress, mode, reason):
    """One night's action from the mode table, by its day after D+0 and the progress file's state."""
    # covers: test_boundary_d21, test_boundary_d30
    found = modes.action(D0 + timedelta(days=day), D0, progress)
    assert found.mode == mode and reason in found.reason and found.reason.startswith(f"D+{day}: ")

