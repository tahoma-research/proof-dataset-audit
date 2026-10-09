import threading
from datetime import date

import pytest
from helpers import PY, REPO, git, in_unit

from ledger import gatefile, policy
from ledger.types import LedgerStop

TODAY = date(2026, 10, 2)
SLUGS = [
    "prd-approved", "d-0-name", "d-0-research", "d0", "pin-amendment", "ceiling:d7-probes", "budget-check",
    "pre-d0-note-reply", "d7", "d7-frame", "d7-sample", "palomar-check", "independent-audit-check", "d14",
    "d14-outcome", "stop-loss", "legacy-cache-probe", "legacy-collector", "d21-legacy", "legacy-status",
    "classifier-freeze", "limit-freeze", "d21-proof-1", "d21-proof-1b", "d21-proof-2", "d21-proof-3",
    "d21-proof-3b", "branch-reduction", "d21-pilot", "route-one", "timer-enabled", "fixture-repeat", "rescope",
    "skipped-night", "d30-attempt-1", "d30-divergence-note", "d43", "d44-state", "notice", "route-two",
    "stranger-provisioning", "stranger-tree-deletion", "d48-smoke", "d50-tag", "proof-4", "d60",
    "announce-step-1", "timer-disabled", "d90", "proof-4b", "g1-sweep-2027-01-15", "clone-count-2027-01-15",
    "g1", "withdrawal", "outside-reproduction", "kill"]


@pytest.fixture
def pol(make_policy, tmp_path):
    """An operator policy whose public tree lies outside its root."""
    return policy.load(make_policy(public_tree=str(tmp_path / "public")))


def test_append_valid(pol):
    """A valid line is appended below the preamble and reads back field for field."""
    gatefile.append(pol, "prd-approved", "recorded", "operator", "approval date", TODAY)
    text = (pol.root / "gates/GATES.md").read_text()
    assert text == (REPO / "templates/GATES.md.tmpl").read_text() + (
        "| 2026-10-02 | prd-approved | recorded | operator | approval date |\n")
    assert gatefile.rows(pol) == [("2026-10-02", "prd-approved", "recorded", "operator", "approval date")]


@pytest.mark.parametrize("verdict, reason", [
    ("met | unmet", "r"), ("met", "first\nsecond"), ("met", "log in /home/example/run"),
    ("met", "tree=/mnt/example/env"), ("met", "see (/etc/hosts)"), ("met", "probe of 192.0.2.1:22"),
    ("v" * 121, "r"), ("met", "r" * 401), ("met", "see file:///home/example/x"), ("met", "log //mnt/example/x"),
    ("met", "see https:///home/example/x"), ("met", "in ~example/notes"), ("met", "built on Example-Host"),
], ids=["pipe", "newline", "home-path", "mnt-path", "rooted-token", "host-address", "long-verdict", "long-reason",
        "file-url", "double-slash", "empty-host-url", "named-home", "scrub-term"])
def test_rejects_pipe_newline_path(pol, verdict, reason):
    """A line with a separator, a line break, an absolute path, a host address, a scrubbed name or an over-long
    field is refused before anything is written."""
    with pytest.raises(LedgerStop):
        gatefile.append(pol, "d7", verdict, "pipeline", reason, TODAY)
    assert gatefile.rows(pol) == []


def test_sanitized_text_with_an_empty_denylist_still_stops(pol):
    """sanitize withholds text when the sweep cannot run for an empty denylist, and appending the line it made
    still stops on that."""
    open(pol.values["privacy_denylist"], "w").close()
    reason = gatefile.sanitize(pol, "a constant", 200)
    assert reason == gatefile.WITHHELD
    with pytest.raises(LedgerStop, match="no terms"):
        gatefile.append(pol, "rescope", "cut_n=1", "pipeline", reason, TODAY)


def test_rejects_unknown_gate(pol):
    """An unknown gate is refused, and so is a route-two verdict outside its closed set."""
    with pytest.raises(LedgerStop, match="unknown gate"):
        gatefile.append(pol, "d8", "met", "pipeline", "r", TODAY)
    with pytest.raises(LedgerStop, match="route-two verdict"):
        gatefile.append(pol, "route-two", "skew framing invoked", "operator", "r", TODAY)


def test_rejects_person_as_evaluator(pol):
    with pytest.raises(LedgerStop, match="evaluator"):
        gatefile.append(pol, "d7", "met", "Example Person", "r", TODAY)


def test_every_prd_slug_accepted(pol):
    for slug in SLUGS:
        gatefile.append(pol, slug, "skew" if slug == "route-two" else "recorded", "pipeline", "r", TODAY)
    assert [row[1] for row in gatefile.rows(pol)] == SLUGS


def test_d0_parsed(pol):
    assert gatefile.d0(pol) is None
    gatefile.append(pol, "prd-approved", "recorded", "operator", "r", date(2026, 10, 1))
    gatefile.append(pol, "d0", "recorded", "operator", "pin commit", TODAY)
    assert gatefile.d0(pol) == TODAY


def test_accepts_https_link(pol):
    gatefile.append(pol, "announce-step-1", "posted", "operator", "at https://example.invalid/t/1", TODAY)
    assert gatefile.rows(pol)[0][4] == "at https://example.invalid/t/1"


def test_accepts_version_strings(pol):
    """The address check refuses non-public addresses only, so version strings that parse as public ones pass."""
    gatefile.append(pol, "d0", "recorded", "operator",
                    "v4.15.0.1 pinned; tag 1.2.3.4; version 0.4.0.1; saw a::b and x :: xs in output", TODAY)
    assert len(gatefile.rows(pol)) == 1


def test_bootstrap_copy_before_public_tree(pol, tmp_path):
    """Lines go to the bootstrap copy until the policy's public tree has its own gate file, then only there."""
    gatefile.append(pol, "prd-approved", "recorded", "operator", "r", TODAY)
    bootstrap = (pol.root / "gates/GATES.md").read_text()
    public = tmp_path / "public/gates/GATES.md"
    public.parent.mkdir(parents=True)
    public.write_text(bootstrap)
    gatefile.append(pol, "d0", "recorded", "operator", "pin commit", TODAY)
    assert (pol.root / "gates/GATES.md").read_text() == bootstrap
    assert [row[1] for row in gatefile.rows(pol)] == ["prd-approved", "d0"]
    assert public.read_text().endswith("| d0 | recorded | operator | pin commit |\n")


def test_gate_commits_its_line(staged, stage_policy):
    """`ledger gate` commits its line in the public tree as the project identity, and nothing else there,
    waiting briefly for another git call's index.lock."""
    (lock := staged / ".git/index.lock").touch()
    threading.Timer(2.5, lock.unlink).start()  # another git call, holding the index for a moment
    (staged / "results").mkdir()
    (staged / "results/progress.json").write_text("{}\n")
    run = in_unit(PY, "-m", "ledger", "gate", "--gate", "d0", "--verdict", "recorded", "--evaluator", "operator",
                  "--reason", "pin commit", "--policy", stage_policy.path)
    assert run.code == 0, run.err
    assert git("-C", staged, "log", "-1", "--format=%s|%an") == "Gate line: d0|Example Project\n"
    assert git("-C", staged, "show", "--name-only", "--format=", "HEAD") == "gates/GATES.md\n"
    assert git("-C", staged, "status", "--porcelain") == "?? results/\n"
