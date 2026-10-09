"""Frame: the entries a draw can take pairs from, after dedupe, and the counts published beside the draw."""

import hashlib
import re
import statistics
from collections import Counter
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path

from ledger import ingest
from ledger.constants import Constants
from ledger.types import Digest, LedgerStop, canonical, write_atomic


@dataclass(frozen=True)
class Frame:
    summary: dict  # every field of frame.json but `eligible`
    eligible: list[ingest.Entry]  # in file order

    @cached_property
    def json(self) -> bytes:
        eligible = [{"position": e.position, "decl": e.decl, "n": len(e.proofs)} for e in self.eligible]
        return canonical(self.summary | {"eligible": eligible})

    @property
    def digest(self) -> Digest:
        return "sha256:" + hashlib.sha256(self.json).hexdigest()


def _key(entry: ingest.Entry, suffix: re.Pattern) -> str | None:
    """The cross-entry dedupe key: the statement with whitespace runs collapsed, the suffix removed and the
    declaration name masked; None for an entry with no name, which is never deduplicated."""
    if entry.decl is None:
        return None
    text = suffix.sub("", re.sub(r"\s+", " ", entry.formal_statement))
    name = ingest.DECL.search(text)
    return text[:name.start(1)] + "⟨NAME⟩" + text[name.end(1):]


def build(entries_path: Path, consts: Constants) -> Frame:
    """The frame of the entries in `entries_path`: those with a proof, minus each whose statement an earlier
    one already has (a proof-less entry takes no part). Refused entries stay in the frame. Stops when no
    entry has a proof."""
    entries, entries_sha256 = ingest.load(entries_path)
    bearing = [e for e in entries if e.proofs]
    if not bearing:
        raise LedgerStop(f"{entries_path.name} has no entry with a proof: nothing to draw from")
    suffix, seen, eligible = re.compile(consts.published["assembly"]["suffix_regex"]), set(), []
    for entry in bearing:
        key = _key(entry, suffix)
        if key in seen:
            continue
        eligible.append(entry)
        if key:
            seen.add(key)
    splits = dict(Counter(e.split for e in entries))
    sizes = [len(e.proofs) for e in bearing]
    widest = max(bearing, key=lambda e: len(e.proofs))

    def pairs(group):
        return sum(min(len(e.proofs), consts.published["sampling"]["max_pairs_per_entry"]) for e in group)
    summary = {
        "schema": "frame/1",
        "entries_sha256": entries_sha256,
        "records_total": len(entries),
        "split_counts": splits,
        "card_count_lean_workbook": consts.source["card_split_counts"]["lean_workbook"],
        "reconciliation": f"counted split values sum to records_total: {str(sum(splits.values()) == len(entries)).lower()}",
        "proofless_excluded": len(entries) - len(bearing),
        "proof_bearing": len(bearing),
        "proof_elements_raw": sum(e.proofs_raw for e in bearing),
        "within_entry_exact_duplicates_removed": sum(e.proofs_raw - len(e.proofs) for e in bearing),
        "cross_entry_duplicates_removed": len(bearing) - len(eligible),
        "refused": {kind: sum(e.refusal == kind for e in eligible) for kind in ingest.REFUSALS},
        "eligible_entries": len(eligible),
        "drawable_pairs_before_cross_dedupe": pairs(bearing),
        "drawable_pairs": pairs(eligible),
        "multiplier": {"mean": round(statistics.mean(sizes), 2), "median": statistics.median(sizes),
                       "max": len(widest.proofs), "max_entry": widest.decl},
    }
    return Frame(summary, eligible)


def write(frame: Frame, work: Path) -> Digest:
    """Write frame.json under `work` and return its digest."""
    return write_atomic(work / "frame.json", frame.json)


def published(frame: Frame, work: Path) -> None:
    """Stop unless `work`/frame.json is this frame: both frame sizes are published before a draw."""
    path = work / "frame.json"
    if not path.is_file() or path.read_bytes() != frame.json:
        raise LedgerStop(f"{path} is missing or is not this frame: run `ledger frame` first")
