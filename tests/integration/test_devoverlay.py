import pytest
from helpers import write_policy

from ledger import confine, devoverlay, policy

pytestmark = pytest.mark.integration


def test_overlay_header_elaborates(dev_root, lean_bin, tmp_path, monkeypatch):
    """The dev overlay's header elaborates in the dev pin tree, its build targets built from source."""
    monkeypatch.setenv("LEDGER_DEV_ROOT", str(dev_root))
    overlay = devoverlay.load(policy.load(write_policy(tmp_path / "policy.toml", dev_root)))
    assert overlay is not None
    env = {"PATH": f"{lean_bin}:/usr/bin:/bin", "HOME": str(tmp_path), "TMPDIR": str(tmp_path),
           "XDG_CACHE_HOME": str(dev_root / "xdg-cache"), "MATHLIB_NO_CACHE_ON_UPDATE": "1"}
    tree = dev_root / "env/pin"
    writes = [tree, dev_root / "xdg-cache", tmp_path]
    build = confine.run(["lake", "--no-cache", "build", *overlay.build_targets], cwd=tree, writes=writes, env=env)
    assert build.exit == 0, build.output[-3000:]
    probe = tmp_path / "Probe.lean"
    probe.write_text(overlay.header + "example (x : ℝ) : x + 0 = x := by simp\n")
    check = confine.run(["lake", "--no-cache", "env", "lean", str(probe)], cwd=tree, writes=writes, env=env)
    assert check.exit == 0, check.output
