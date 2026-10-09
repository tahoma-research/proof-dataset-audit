"""Assemble: the Lean text of each drawn pair, byte for byte as the published assembly rule states it, and the
digests that key it."""

import hashlib
import shutil
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path

from ledger import frame, ingest
from ledger.types import Digest, LedgerStop, canonical, write_atomic

REFUSALS = (*ingest.REFUSALS, "substitution-missing", "carriage-return")


@dataclass(frozen=True)
class Assembled:
    i: int
    pair_id: str
    pair_sha256: Digest  # of the text; of the refusal key when the pair is refused
    element_sha256: Digest  # re-computed from the element placed
    refusal: str | None
    text: str | None  # None when the pair is refused: nothing to check


def _sha(data: str) -> Digest:
    return "sha256:" + hashlib.sha256(data.encode()).hexdigest()


def assemble_pair(row: dict, entry: ingest.Entry, assembly: dict) -> Assembled:
    """The pair a draw's `row` names, pair `row["k"]` of `entry`: the header, then the statement less its
    suffix and its trailing whitespace, the declaration name replaced by the pair's, then one space, `:= by`,
    a newline, the element less one trailing newline, split on newlines only, with every line indented two
    spaces, and one terminal newline. A pair the rule cannot build, or whose text does not declare the pair's
    name and carry its element after the declaration, is refused and keyed by its refusal key. Stops when the
    element's digest is not the one the frame recorded for its index."""
    k, element = row["k"], entry.proofs[row["k"]]
    digest = _sha(element)
    if digest != row["element_sha256"]:
        raise LedgerStop(f"{row['pair_id']}: element {k} has digest {digest}, the frame's is {row['element_sha256']}")
    text, refusal = None, entry.refusal or ("carriage-return" if "\r" in element else None)
    if refusal is None:
        body = ingest.body(entry.formal_statement, assembly["suffix_regex"])
        name = ingest.DECL.search(body)
        declaration = assembly["header"] + body[:name.start(1)] + row["pair_id"] + body[name.end(1):] + " := by\n"
        text = declaration + "\n".join("  " + line for line in element.removesuffix("\n").split("\n")) + "\n"
        placed = text[len(declaration):].removesuffix("\n")
        placed = "\n".join(line.removeprefix("  ") for line in placed.split("\n"))
        if ingest.DECL.search(declaration)[1] != row["pair_id"] or placed != element.removesuffix("\n"):
            text, refusal = None, "substitution-missing"
    key = text if refusal is None else f"refused\t{entry.position}\t{k}\t{digest}"
    return Assembled(row["i"], row["pair_id"], _sha(key), digest, refusal, text)


def demangle(name: str, name_mangle: str) -> tuple[str, int]:
    """A pair's declaration name split on the last occurrence of the published separator: the source
    declaration name and the pair index. Stops on a name without the separator."""
    decl, separator, k = name.rpartition(name_mangle.format(decl="", k=""))
    if not separator:
        raise LedgerStop(f"{name!r} is not a pair name: no separator")
    return decl, int(k)


def write_pairs(sample: dict, built: frame.Frame, assembly: dict, work: Path) -> tuple[Digest, Counter]:
    """Assemble every pair of `sample`'s draw from the frame `built`; clear work/pairs/, then write each text
    to work/pairs/<pair_id>.lean and one line per pair, in draw order, to work/assembled.jsonl, a refused pair
    a line and no file. Returns the digest of assembled.jsonl and the count of pairs by refusal (None: a
    text). Stops unless work/frame.json is `built` and the draw is of it, or when a row names a position
    outside it."""
    frame.published(built, work)
    if sample["frame_sha256"] != built.digest:
        raise LedgerStop(f"sample.json's frame_sha256 {sample['frame_sha256']} is not frame.json's {built.digest}")
    entries = {e.position: e for e in built.eligible}
    if outside := [row["position"] for row in sample["draw"] if row["position"] not in entries]:
        raise LedgerStop(f"sample.json draws from positions outside the frame: {outside}")
    pairs = [assemble_pair(row, entries[row["position"]], assembly) for row in sample["draw"]]
    if (work / "pairs").exists():
        shutil.rmtree(work / "pairs")
    (work / "pairs").mkdir()
    for pair in pairs:
        if pair.text is not None:
            write_atomic(work / "pairs" / f"{pair.pair_id}.lean", pair.text.encode())
    digest = write_atomic(work / "assembled.jsonl",
                          b"".join(canonical({k: v for k, v in asdict(p).items() if k != "text"}) for p in pairs))
    return digest, Counter(p.refusal for p in pairs)
