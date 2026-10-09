"""The nightly unit's mode table: the one thing a night does, from its day after D+0 and the state the progress file
records. The rebuild unit's nights are read from the same state, so each night belongs to one of the two units."""

from dataclasses import dataclass
from datetime import date

from ledger.aggregate import DONE

PASS1_FIRST, REBUILD_NIGHT, PASS1_LAST, CHECK_LAST = 22, 30, 43, 46  # days after D+0
REBUILD_ATTEMPTS = 3


@dataclass(frozen=True)
class Action:
    mode: str  # exit, pass1 or aggregate
    reason: str


def rebuild_night(day: int, progress: dict) -> bool:
    """Each night from D+30 to D+43 while no rebuild attempt has passed and fewer than three are recorded, so a D+30
    that made no attempt, missed or contended, still gets it."""
    tried = progress.get("rebuild", {}).get("attempts", [])
    return REBUILD_NIGHT <= day <= PASS1_LAST and len(tried) < REBUILD_ATTEMPTS and all(
        attempt["result"] == "fail" for attempt in tried)


def action(today: date, d0: date, progress: dict) -> Action:
    """The night's action: nothing before D+22, the dated work before it running in one-off units; pass 1 on the
    pass-1 nights; nothing on a rebuild night; from D+44 the D+44 check's step, until its state is replay-returned or
    replay-unavailable. Past D+46, or D+47 when the D+46 run spent the extension, nothing."""
    day = (today - d0).days
    if day < PASS1_FIRST:
        return Action("exit", f"D+{day}: pass 1 starts on D+{PASS1_FIRST}; the dated work before it runs in one-off "
                              "units")
    if rebuild_night(day, progress):
        return Action("exit", f"D+{day}: a rebuild night; the rebuild unit runs")
    if day <= PASS1_LAST:
        return Action("pass1", f"D+{day}: a pass-1 night")
    check = progress.get("aggregate", {"state": "build-pending", "extension": "unspent"})
    if check["state"] in DONE:
        return Action("exit", f"D+{day}: the D+44 check is done, {check['state']}")
    if day <= CHECK_LAST or day == CHECK_LAST + 1 and check["extension"] == "spent":
        return Action("aggregate", f"D+{day}: the D+44 check, state {check['state']}")
    return Action("exit", f"D+{day}: past the D+44 check's last night, at state {check['state']}")
