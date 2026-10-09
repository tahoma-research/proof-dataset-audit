import pytest

from ledger import devoverlay, policy, preflight
from ledger.types import LedgerStop

OVERLAY = 'header = "import Aesop\\n"\nbuild_targets = ["Aesop"]\n'


def test_only_under_dev_root(make_policy, root, tmp_path, monkeypatch):
    """The overlay is read only when the run's root is LEDGER_DEV_ROOT."""
    (root / devoverlay.FILE).write_text(OVERLAY)
    pol = policy.load(make_policy())
    monkeypatch.setenv("LEDGER_DEV_ROOT", str(root))
    assert devoverlay.load(pol) == devoverlay.Overlay("import Aesop\n", ["Aesop"])
    monkeypatch.setenv("LEDGER_DEV_ROOT", str(tmp_path))
    assert devoverlay.load(pol) is None


def test_presence_elsewhere_fails_preflight(ready, monkeypatch):
    """An overlay file under any root other than LEDGER_DEV_ROOT stops the run."""
    monkeypatch.delenv("LEDGER_DEV_ROOT", raising=False)
    pol, consts = ready()
    (pol.root / devoverlay.FILE).write_text(OVERLAY)
    with pytest.raises(LedgerStop, match="dev overlay"):
        preflight.check(pol, consts)
