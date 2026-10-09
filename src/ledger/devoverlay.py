"""The development overlay: a smaller header and build-target list, honoured only when the run's root is
LEDGER_DEV_ROOT. Results produced under it are for development only."""

import os
from dataclasses import dataclass

from ledger.types import load_toml

FILE = "dev-overlay.toml"


@dataclass(frozen=True)
class Overlay:
    header: str
    build_targets: list[str]


def load(policy) -> Overlay | None:
    """The overlay under the policy's root, if that root is LEDGER_DEV_ROOT and the file exists."""
    dev = os.environ.get("LEDGER_DEV_ROOT")
    path = policy.root / FILE
    if not dev or os.path.realpath(dev) != os.path.realpath(policy.root) or not path.exists():
        return None
    return Overlay(**load_toml(path, {"header": str, "build_targets": [str]}, FILE))
