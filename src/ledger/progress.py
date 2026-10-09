"""The progress file, results/progress.json: pass 1's resumable state, keyed by pair digest and environment, and
the D+44 check's. Every change is on disk before the call that made it returns."""

import json
import threading
from datetime import UTC, date, datetime
from pathlib import Path

from ledger.types import Digest, LedgerStop, write_atomic

# The D+44 check's transitions, (state, event) -> state, as PRD § D+44 gives them; no other is legal.
AGGREGATE = {
    ("build-pending", "built"): "replay-pending",
    ("build-pending", "built-unavailable"): "replay-unavailable",
    ("build-pending", "removed"): "build-pending",
    ("rejected-rerun-pending", "built"): "replay-pending",
    ("rejected-rerun-pending", "removed"): "build-pending",
    ("replay-pending", "started"): "replay-running",
    ("replay-running", "resumed"): "replay-pending",  # the run that started it died; this run holds the lock
    ("replay-running", "returned"): "replay-returned",
    ("replay-running", "rejected"): "rejected-rerun-pending",
    ("build-pending", "cut"): "build-pending",  # over the cap: the cut, carried out by the next re-run
    ("rejected-rerun-pending", "cut"): "build-pending",
    ("replay-running", "cut"): "build-pending",
}
RERUN = {"removed", "rejected", "cut"}  # a member removed or a cut: the rebuild and replay is one of the re-runs


class Progress:
    def __init__(self, path: Path, data: dict):
        self.path, self.data, self._lock = path, data, threading.Lock()  # legs finish on several workers

    def save(self) -> None:
        write_atomic(self.path, (json.dumps(self.data, indent=2, sort_keys=True) + "\n").encode())

    def _leg(self, pair: Digest, env: str) -> dict:
        return self.data["legs"].setdefault(pair, {}).setdefault(env, {"attempts": 0, "terminal": False, "leg": None})

    def start_attempt(self, pair: Digest, env: str) -> int:
        """Count an attempt at a leg before any of its commands runs, so a run killed during it still counts
        it; returns the attempt's number."""
        with self._lock:
            leg = self._leg(pair, env)
            leg["attempts"] += 1
            self.save()
            return leg["attempts"]

    def finish(self, pair: Digest, env: str, path: str, terminal: bool) -> None:
        """Point the leg at its latest result file, relative to results/."""
        with self._lock:
            self._leg(pair, env).update(leg=path, terminal=terminal)
            self.save()

    def attempts(self, pair: Digest, env: str) -> int:
        return self.data["legs"].get(pair, {}).get(env, {}).get("attempts", 0)

    def reopened_at(self, pair: Digest, env: str) -> int:
        """The attempts the leg had when it was last reopened, from which its allowance of attempts counts again."""
        return self.data["legs"].get(pair, {}).get(env, {}).get("reopened_at", 0)

    def pending_pairs(self, pairs: list[dict], required: list[str]) -> list[tuple[dict, list[str]]]:
        """The pairs, in the order given, that still need a leg, each with those legs: a required leg not
        terminal."""
        pending = []
        for pair in pairs:
            legs = self.data["legs"].get(pair["pair_sha256"], {})
            needed = [env for env in required if not legs.get(env, {}).get("terminal")]
            if needed:
                pending.append((pair, needed))
        return pending

    def reopen(self, pairs: dict[Digest, dict | None]) -> None:
        """Make each pair's pin leg not terminal, with a fresh allowance of attempts, so that the next run takes it
        again, recording the reason it was reopened at the freeze, {reason, date}, where one is given; in one save."""
        with self._lock:
            for pair, why in pairs.items():
                leg = self._leg(pair, "pin")
                leg.update(terminal=False, reopened_at=leg["attempts"])
                if why:
                    self.data.setdefault("reopened", {})[pair] = why
            self.save()

    def pilot(self, attempted: list[Digest], spent_s: float, line_reached: bool) -> None:
        """Record the D+14 serial pilot's pairs attempted so far, the compile and replay wall-clock they summed,
        and whether its 25-hour line stopped it."""
        with self._lock:
            self.data["d14_pilot"] = {"attempted": attempted, "spent_s": spent_s, "line_reached": line_reached}
            self.save()

    def aggregate(self) -> dict:
        """The D+44 check's record: its state, the re-runs used, the extension, the membership last built, the
        removals and the last build and replay; build-pending before its first night."""
        return self.data.setdefault("aggregate", {
            "state": "build-pending", "reruns_used": 0, "extension": "unspent", "membership_sha256": None,
            "removals": [], "last_build": None, "last_replay": None})

    def note(self, **fields) -> None:
        """Record facts of the D+44 check beside its state."""
        with self._lock:
            self.aggregate().update(fields)
            self.save()

    def _move(self, event: str, spend: bool) -> None:
        agg = self.aggregate()
        if (state := AGGREGATE.get((agg["state"], event))) is None:
            raise LedgerStop(f"aggregate: no transition from {agg['state']} on {event}")
        if spend and agg["extension"] == "spent":
            raise LedgerStop("the extension is spent once")
        agg.update(state=state, reruns_used=agg["reruns_used"] + (event in RERUN))
        if spend:
            agg["extension"] = "spent"

    def transition(self, event: str, spend: bool = False, **fields) -> str:
        """Move the D+44 check to the state AGGREGATE gives `event` from its state, counting a re-run for a
        member removed or a cut; with `spend`, which the D+46 run alone passes, spending the D+47 extension, once;
        and recording `fields` beside it, all in one save. Returns the state. Any other move stops."""
        with self._lock:
            self._move(event, spend)
            self.aggregate().update(fields)
            self.save()
            return self.aggregate()["state"]

    def remove(self, faults: dict[Digest, dict], cause: str, today: date, event: str | None = None,
               spend: bool = False, **fields) -> None:
        """Remove members from the aggregate with `cause`, rejected-by-replay or harness-error, each pair digest in
        `faults` with the override that classifies it: {source, constant} for a replay rejection, {source, detail}
        otherwise, with its date and `at`, the UTC time to the second, which orders two overrides of one day; and
        with them, in one save, the transition on `event` that the removal drives (`spend` as for transition) and
        `fields`."""
        with self._lock:
            if event:
                self._move(event, spend)
            self.aggregate().update(fields)
            kind = "replay_overrides" if cause == "rejected-by-replay" else "harness_overrides"
            at = datetime.now(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")
            for pair, override in faults.items():
                self.data.setdefault(kind, {})[pair] = override | {"date": today.isoformat(), "at": at}
                self.aggregate()["removals"].append({"pair_sha256": pair, "cause": cause, "date": today.isoformat()})
            self.save()

    def rebuild_attempt(self, n: int, result: str, today: date) -> None:
        """Record D+30 rebuild attempt `n`: as it starts, failed, so that an attempt that never ends counts; as it
        ends, its result."""
        with self._lock:
            tried = self.data.setdefault("rebuild", {"attempts": []})["attempts"]
            if tried and tried[-1]["n"] == n:
                tried[-1]["result"] = result
            else:
                tried.append({"n": n, "date": today.isoformat(), "result": result})
            self.save()

    def cut_written(self, pending: list) -> None:
        """Record that the D+44 run has computed the D+43 cut, and the writes it left pending, in one save."""
        with self._lock:
            self.data["d44_cut_written"] = True
            self.aggregate()["pending"] = pending
            self.save()


def load(path: Path, sample_sha256: Digest) -> Progress:
    """The progress of the draw whose sample.json has digest `sample_sha256`; a new one if there is none.
    Stops on a progress file kept for another draw."""
    if not path.exists():
        return Progress(path, {"schema": "progress/1", "sample_sha256": sample_sha256, "legs": {},
                               "d14_pilot": {"attempted": [], "spent_s": 0.0, "line_reached": False}})
    data = json.loads(path.read_text())
    if data["sample_sha256"] != sample_sha256:
        raise LedgerStop(f"{path.name} is the progress of sample {data['sample_sha256']}, not {sample_sha256}")
    return Progress(path, data)
