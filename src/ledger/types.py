"""Types shared across the package, the check that a parsed file has exactly the expected shape, and the canonical JSON form with its atomic writer."""

import hashlib
import json
import os
import tomllib
from pathlib import Path
from typing import Literal

Env = Literal["pin", "pin-seeded", "legacy"]
Digest = str  # "sha256:" followed by 64 lowercase hex digits


class LedgerStop(Exception):
    """A precondition failed: the command stops before any further work."""


def canonical(value) -> bytes:
    """The machine form of one JSON value: sorted keys, compact separators, one terminal newline."""
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n").encode()


def write_atomic(path: Path, data: bytes) -> Digest:
    """Write `data` to `path` through a temporary file, fsynced, then renamed; return its digest."""
    tmp = path.with_name(f".{path.name}.{os.getpid()}")
    with open(tmp, "wb") as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())
    tmp.replace(path)
    return "sha256:" + hashlib.sha256(data).hexdigest()


def check_shape(data, shape, where: str) -> None:
    """Stop unless `data` matches `shape`: a dict demands exactly its keys, `[t]` a list of t, a type itself."""
    if isinstance(shape, dict):
        if type(data) is not dict or data.keys() != shape.keys():
            found = data.keys() if type(data) is dict else set()
            raise LedgerStop(f"{where}: unknown keys {sorted(found - shape.keys())}, "
                             f"missing keys {sorted(shape.keys() - found)}")
        for key, sub in shape.items():
            check_shape(data[key], sub, f"{where}.{key}")
    elif isinstance(shape, list):
        if type(data) is not list:
            raise LedgerStop(f"{where}: expected a list")
        for i, item in enumerate(data):
            check_shape(item, shape[0], f"{where}[{i}]")
    elif type(data) is not shape:
        raise LedgerStop(f"{where}: expected {shape.__name__}")


def load_toml(path: Path, shape: dict, where: str) -> dict:
    """Parse a TOML file and check its shape; an unreadable or malformed file stops."""
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except OSError as e:
        raise LedgerStop(f"{where}: {e.strerror}") from e
    except tomllib.TOMLDecodeError as e:
        raise LedgerStop(f"{where}: {e}") from e
    check_shape(data, shape, where)
    return data
