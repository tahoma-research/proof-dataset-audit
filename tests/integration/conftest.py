import os
from pathlib import Path

import pytest
from helpers import REPO


@pytest.fixture(autouse=True)
def dev_root():
    """The development environment; without it every integration test is skipped, saying why."""
    if not os.environ.get("LEDGER_DEV_ROOT"):
        pytest.skip("LEDGER_DEV_ROOT is unset: integration tests need the development environment")
    return Path(os.environ["LEDGER_DEV_ROOT"])


@pytest.fixture
def lean_bin(dev_root):
    """The pinned toolchain's bin directory in the development environment's elan home."""
    toolchain = (REPO / "recipe/pin/lean-toolchain").read_text().strip()
    return dev_root / "elan/toolchains" / toolchain.replace("/", "--").replace(":", "---") / "bin"
