"""Policy files: the host's rules (the operator policy, never published) or the container's (published),
named by every command and read before anything else."""

import os
import tomllib
from dataclasses import dataclass
from pathlib import Path

from ledger.types import LedgerStop, check_shape

OPERATOR = {
    "schema": str, "kind": str, "root": str, "root_device_forbidden": bool, "confinement": str,
    "disk_floor_gb": int, "disk_floor_mount": str, "slice": str, "privacy_denylist": str, "scrub": [str],
    "public_tree": str, "identity": {"name": str, "email": str}, "host_addresses": [str], "house_sweep": str,
}
CONTAINER = {"schema": str, "kind": str, "root": str, "confinement": str, "disk_floor_gb": int, "disk_need_gb": int}
SHAPES = {"operator": OPERATOR, "container": CONTAINER}
CONFINEMENT = {"operator": "landlock", "container": "none"}  # the container's own isolation stands in
WRITTEN = ("lock", "gates", "dataset", "work", "env", "runs", "measure", "fixtures-src", "fixtures-run",
           "elan", "venv", "xdg-cache", "tmp", "runtime", "podman")  # beneath the root


@dataclass(frozen=True)
class Policy:
    path: Path
    kind: str
    root: Path
    values: dict

    def paths(self) -> dict[str, Path]:
        """Every path a run writes, by name."""
        paths = {"root": self.root} | {name: self.root / name for name in WRITTEN}
        if self.kind == "operator":
            paths["public_tree"] = Path(self.values["public_tree"])
        return paths


def load(path: Path) -> Policy:
    """Load a policy file; a missing, unreadable or invalid one, or an operator policy whose mode is not
    0600, stops the command before any work."""
    try:
        with open(path, "rb") as f:
            mode = os.fstat(f.fileno()).st_mode & 0o777
            data = tomllib.load(f)
    except OSError as e:
        raise LedgerStop(f"policy file missing or unreadable: {e.strerror}") from e
    except tomllib.TOMLDecodeError as e:
        raise LedgerStop(f"policy file is not valid TOML: {e}") from e
    kind = data.get("kind")
    if kind not in SHAPES:
        raise LedgerStop(f"policy kind {kind!r} is neither operator nor container")
    check_shape(data, SHAPES[kind], "policy")
    if data["schema"] != "policy/1":
        raise LedgerStop("policy schema is not policy/1")
    if data["confinement"] != CONFINEMENT[kind]:
        raise LedgerStop(f"a {kind} policy requires confinement = {CONFINEMENT[kind]!r}")
    if kind == "operator" and mode != 0o600:
        raise LedgerStop(f"operator policy mode is {mode:o}, not 600")
    return Policy(Path(path), kind, Path(data["root"]).absolute(), data)
