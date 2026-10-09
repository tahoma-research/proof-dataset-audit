import pytest

from ledger import cli, policy
from ledger.types import LedgerStop


def test_missing_file_stops(tmp_path):
    """A named policy file that does not exist stops the run before any work."""
    with pytest.raises(LedgerStop, match="unreadable"):
        policy.load(tmp_path / "absent.toml")


def test_unreadable_stops(make_policy):
    """A named policy file that cannot be read stops the run before any work."""
    path = make_policy()
    path.chmod(0)
    with pytest.raises(LedgerStop, match="unreadable"):
        policy.load(path)


def test_none_named_refuses():
    """A command naming no policy file refuses to start."""
    with pytest.raises(SystemExit) as stop:
        cli.main(["preflight"])
    assert stop.value.code == 2


def test_unknown_key_refused(make_policy):
    """A policy with a key outside the schema is refused rather than ignored."""
    with pytest.raises(LedgerStop, match="surplus"):
        policy.load(make_policy(surplus=1))


def test_operator_policy_mode_0600(make_policy):
    """An operator policy is accepted only with mode 0600."""
    path = make_policy()
    assert policy.load(path).kind == "operator"
    path.chmod(0o640)
    with pytest.raises(LedgerStop, match="600"):
        policy.load(path)
