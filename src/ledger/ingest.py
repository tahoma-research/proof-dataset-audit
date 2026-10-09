"""Ingest: the pinned release file, fetched and checked against the recipe, parsed into entries.jsonl."""

import hashlib
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterator

from ledger import confine
from ledger.types import Digest, LedgerStop, canonical, write_atomic

CURL = "/usr/bin/curl"
DECL = re.compile(r"\b(?:theorem|lemma)\s+([^\s(){}\[\]:]+)", re.ASCII)
REFUSALS = ("no-decl", "double-underscore", "unsafe-name", "comment-before-suffix", "suffix-mismatch", "name-collision")
WHITESPACE = " \t\n\r\f\v"  # the assembly rule's whitespace is ASCII alone


@dataclass(frozen=True)
class Entry:
    position: int  # 0-based index in the release file; the tiebreaker
    decl: str | None
    split: str  # the record's own `split` field, verbatim
    formal_statement: str
    proofs_raw: int
    proofs: list[str]  # after exact-string dedupe, first occurrence kept
    element_sha256: list[Digest]
    refusal: str | None


def _check(file: Path, source: dict) -> None:
    with open(file, "rb") as f:
        digest = hashlib.file_digest(f, "sha256").hexdigest()
    if file.stat().st_size != source["bytes"] or digest != source["sha256"]:
        raise LedgerStop(f"{file.name} does not match the recipe's size and sha256")


def fetch(consts, policy) -> Path:
    """The release file under dataset/, its size and sha256 equal to the recipe's. A file already there is
    checked and used; otherwise it is downloaded from the pinned URL, the only network use, through a child
    that may reach TCP port 443 alone, and checked before it takes the final name. A file that does not match
    stops ingest; a download that fails the check is removed."""
    source = consts.source
    path = policy.root / "dataset" / source["file"]
    if path.exists():
        _check(path, source)
        return path
    path.parent.mkdir(exist_ok=True)
    part = path.with_name(path.name + ".part")
    done = confine.run([CURL, "-q", "--fail", "--silent", "--show-error", "--location", "--proto", "=https",
                        "--proto-redir", "=https", "--max-redirs", "5", "--connect-timeout", "30",
                        "--speed-limit", "1000", "--speed-time", "60", "--output", str(part), source["url"]],
                       cwd=path.parent, writes=[path.parent], net=True)
    if done.exit != 0:
        raise LedgerStop(f"ingest.fetch: curl exited {done.exit}: {done.output.strip()}")
    try:
        _check(part, source)
    except LedgerStop:
        part.unlink()
        raise
    part.replace(path)
    return path


def body(statement: str, suffix_regex: str) -> str | None:
    """The verbatim statement before its suffix, trailing whitespace stripped; None when the suffix does not
    match."""
    match = re.search(suffix_regex, statement, re.ASCII)
    return statement[:match.start()].rstrip(WHITESPACE) if match else None


def _refusal(decl: str | None, statement: str, suffix_regex: str, seen: set[str]) -> str | None:
    if decl is None:
        return "no-decl"
    if "__" in decl:
        return "double-underscore"
    if "/" in decl or "\0" in decl:
        return "unsafe-name"
    stated = body(statement, suffix_regex)
    if stated is None:
        return "suffix-mismatch"
    if "--" in stated.rpartition("\n")[2]:
        return "comment-before-suffix"
    return "name-collision" if decl in seen else None


def parse(path: Path, suffix_regex: str) -> Iterator[Entry]:
    """One Entry per record of the release file, in file order. A record is refused, not dropped, when it has
    no declaration name, a name containing the mangling separator `__`, a name containing `/` or NUL (no file
    name), a statement not ending in the suffix, a `--` comment on the last line before the suffix, or a name an
    earlier record already has (the earlier keeps it). Only a record that is not otherwise refused claims its
    name: a refused record never assembles, so it keeps nothing from a later one."""
    seen: set[str] = set()
    for position, record in enumerate(json.loads(path.read_text(encoding="utf-8"))):
        split, statement, proof = record.get("split"), record.get("formal_statement"), record.get("proof")
        if not (isinstance(split, str) and split and isinstance(statement, str) and isinstance(proof, list)
                and all(isinstance(p, str) for p in proof)):
            raise LedgerStop(f"record {position}: split must be a non-empty string, formal_statement a string, "
                             "proof a list of strings")
        decl = match[1] if (match := DECL.search(statement)) else None
        proofs = list(dict.fromkeys(proof))
        refusal = _refusal(decl, statement, suffix_regex, seen)
        yield Entry(position, decl, split, statement, len(proof), proofs,
                    ["sha256:" + hashlib.sha256(p.encode()).hexdigest() for p in proofs], refusal)
        if refusal is None:
            seen.add(decl)


def load(path: Path) -> tuple[list[Entry], Digest]:
    """The entries of an entries.jsonl, in file order, and the file's digest."""
    data = path.read_bytes()
    entries = [Entry(**json.loads(line)) for line in data.split(b"\n") if line]
    return entries, "sha256:" + hashlib.sha256(data).hexdigest()


def write(entries, work: Path) -> Digest:
    """Write entries.jsonl under `work` (atomically) and return its digest."""
    work.mkdir(exist_ok=True)
    return write_atomic(work / "entries.jsonl", b"".join(canonical(asdict(entry)) for entry in entries))
