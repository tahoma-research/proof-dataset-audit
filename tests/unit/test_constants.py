import hashlib
import json
import shutil
import tomllib

import pytest
from helpers import REPO

from ledger import constants
from ledger.types import LedgerStop

REVISION = "2e066e310b2c6d2c27616927ae131f82901c8f1c"
MATHLIB = "https://github.com/leanprover-community/mathlib4"
APACHE_2_0_SHA256 = "cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30"
# The pin's manifest: Mathlib and the eight packages its release requires, at their revisions.
PIN_PACKAGES = {"mathlib": "5ed2965", "aesop": "355695d", "batteries": "f2effa3d", "Cli": "e92c9f1",
                "importGraph": "e928b72", "LeanSearchClient": "ddf04cf", "plausible": "118aa17",
                "proofwidgets": "106ff4f", "Qq": "6a489d9"}


@pytest.fixture
def repo(tmp_path):
    shutil.copytree(REPO / "recipe", tmp_path / "recipe")
    return tmp_path


def replace(repo, rel, old, new):
    path = repo / rel
    assert old in path.read_text()
    path.write_text(path.read_text().replace(old, new))


def test_revision_must_be_40_hex(repo):
    """A source revision that is not 40 hex characters cannot be pinned, so loading stops."""
    replace(repo, "recipe/source.toml", f'revision = "{REVISION}"', 'revision = "main"')
    with pytest.raises(LedgerStop, match="revision"):
        constants.load(repo)


def test_url_must_pin_revision(repo):
    """A source URL that does not resolve at the pinned revision is refused, at load and so before any fetch."""
    # covers: test_resolve_main_refused
    replace(repo, "recipe/source.toml", f"/resolve/{REVISION}/", "/resolve/main/")
    with pytest.raises(LedgerStop, match="url"):
        constants.load(repo)


@pytest.mark.parametrize("env", ["pin", "pin-seeded"])
def test_pin_recipe_without_no_cache_refused(repo, env):
    """A pin or stop-loss recipe whose lake_flags lack --no-cache is refused at load."""
    replace(repo, f"recipe/{env}/env.toml", 'lake_flags = ["--no-cache"]', "lake_flags = []")
    with pytest.raises(LedgerStop, match="no-cache"):
        constants.load(repo)


def test_header_ends_single_newline(repo):
    """The published header ends in exactly one newline; a second one is refused."""
    assert constants.load(REPO).published["assembly"]["header"].endswith("Rat\n")
    replace(repo, "recipe/constants.toml", 'Rat\\n"', 'Rat\\n\\n"')
    with pytest.raises(LedgerStop, match="header"):
        constants.load(repo)


def test_recipe_id_stable_and_sensitive(repo):
    """The same recipe files give the same identifier; a one-byte change gives a new one."""
    pin = constants.recipe_id(repo, "pin")
    assert pin == constants.recipe_id(repo, "pin") and len(pin) == len("sha256:") + 64
    assert pin != constants.recipe_id(repo, "legacy")
    path = repo / "recipe/pin/lean-toolchain"
    path.write_bytes(path.read_bytes() + b" ")
    assert constants.recipe_id(repo, "pin") != pin


def test_d0_tree_pins():
    """The environment files agree with their env.toml: each toolchain file names its compiler, each manifest
    and lakefile its Mathlib commit; the pin's manifest holds exactly Mathlib's eight packages, and its
    lakefile builds Aggregate alone; the legacy lakefile declares no library. LICENSE is Apache-2.0, verbatim."""
    env = constants.load(REPO).env
    for e in ("pin", "legacy"):
        assert (REPO / f"recipe/{e}/lean-toolchain").read_text() == env[e]["lean"] + "\n"
        packages = json.loads((REPO / f"recipe/{e}/lake-manifest.json").read_text())["packages"]
        manifest = {p["name"]: p["rev"] for p in packages}
        assert manifest["mathlib"] == env[e]["mathlib_commit"]
    pin = json.loads((REPO / "recipe/pin/lake-manifest.json").read_text())["packages"]
    assert {p["name"]: p["rev"][:len(PIN_PACKAGES.get(p["name"], ""))] for p in pin} == PIN_PACKAGES
    assert tomllib.loads((REPO / "recipe/pin/lakefile.toml").read_text()) == {
        "name": "pairs", "defaultTargets": [], "lean_lib": [{"name": "Aggregate"}],
        "require": [{"name": "mathlib", "git": MATHLIB, "rev": env["pin"]["mathlib_commit"]}]}
    assert (REPO / "recipe/legacy/lakefile.lean").read_text() == (
        "import Lake\nopen Lake DSL\n\npackage pairs\n\nrequire mathlib from git\n"
        f'  "{MATHLIB}" @ "{env["legacy"]["mathlib_commit"]}"\n')
    assert hashlib.sha256((REPO / "templates/LICENSE").read_bytes()).hexdigest() == APACHE_2_0_SHA256
