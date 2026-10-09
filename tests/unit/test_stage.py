import dataclasses
import hashlib
import ipaddress
import json
import os
import re
import shutil
import socket
import threading
import time
from datetime import date
from pathlib import Path

import pytest
from helpers import REPO, git

from ledger import confine, constants, fixtures, gatefile, ingest, privacy, publish, stage
from ledger.types import LedgerStop

TODAY = date(2026, 10, 2)
# What the development repository holds that the allowlist takes in.
STAGED = ("src/ledger/", "lean/", "tests/", "templates/", "pyproject.toml", "recipe/source.toml",
          "recipe/constants.toml", "recipe/pin/", "recipe/legacy/", "recipe/pin-seeded/", "recipe/policy/",
          "recipe/Containerfile", "recipe/stranger.sh", "fixtures/assembler/", "fixtures/toy/")
RENDERED = {"LICENSE", "CITATION.cff", "CONTRIBUTING.md", "RULES.md", "README.md", ".gitignore", "gates/GATES.md",
            "recipe/ids.txt"}


def files(tree: Path) -> set[str]:
    return {p.relative_to(tree).as_posix() for p in tree.rglob("*")
            if p.is_file() and p.relative_to(tree).parts[0] != ".git"}


def digests(tree: Path) -> set[str]:
    return {hashlib.sha256(p.read_bytes()).hexdigest() for p in tree.rglob("*") if p.is_file()}


def edit(path: Path, old: str, new: str) -> None:
    text = path.read_text()
    assert old in text
    path.write_text(text.replace(old, new))


def test_git_refuses_truncated_output(tmp_path):
    """A git call whose output passed its bound stops the run, so publish never reads a commit's objects, and
    sweeps them, from a prefix."""
    git("init", "-q", tmp_path)
    with open(tmp_path / "big", "wb") as f:
        f.truncate(confine.GIT_OUTPUT_MAX + 1)
    git("-C", tmp_path, "add", "big")
    with pytest.raises(LedgerStop, match=f"git show: its output passed {confine.GIT_OUTPUT_MAX} bytes"):
        stage.git(tmp_path, "show", ":big")


def test_copies_exact_allowlist(dev_repo, stage_policy, root):
    """The first stage copies exactly the allowlist into the public tree, never compiled Python or Lake output,
    and lists each allowlisted path the development repository lacks; renders the five root files under the
    public name and publisher; carries the bootstrap gate file; records the recipe identifier of each
    environment with audit sources; puts the planted fixture sources beside the tree and none of their bytes
    in it; and commits it all at once, its .gitignore leaving the tree clean when Python compiles the code in a clone.
    The real code, tests and recipe pass the privacy sweep, the recipe as published prose."""
    # covers: test_no_pycache_staged, test_absent_allowlist_path_skipped_and_reported
    # covers: test_root_files_rendered_first_commit, test_ids_txt_written_when_audit_sources_exist
    # covers: test_gatefile::test_first_stage_carries_bootstrap_lines, test_planted_sources_outside_public_tree
    # covers: test_real_src_and_tests_pass_privacy_sweep, test_container::test_recipe_names_no_host
    report = stage.stage(stage_policy, constants.load(dev_repo), dry_run=False)
    public = root / "public"
    copied = {f for f in files(dev_repo) if f.startswith(STAGED) and "__pycache__" not in f and "/.lake/" not in f}
    assert files(public) == copied | RENDERED
    assert report.skipped == ["requirements-dev.txt", "classifier/table-v1.toml"]
    assert report.committed and git("-C", public, "log", "--format=%s").count("\n") == 1
    assert set(git("-C", public, "ls-files").split()) == files(public)
    (public / "src/ledger/__pycache__").mkdir()
    (public / "src/ledger/__pycache__/cli.cpython-312.pyc").write_bytes(b"")
    assert git("-C", public, "status", "--porcelain") == ""
    assert (public / "LICENSE").read_bytes() == (dev_repo / "templates/LICENSE").read_bytes()
    assert (public / "README.md").read_text().startswith("# Example Ledger\n")
    citation = (public / "CITATION.cff").read_text().splitlines()
    authors = citation[citation.index("authors:") + 1:]
    assert 'title: "Example Ledger"' in citation and authors[0] == '  - name: "Example Organisation"'
    assert not authors[1].startswith((" ", "-"))  # the one author, an organisation
    assert (public / "gates/GATES.md").read_text() == (root / "gates/GATES.md").read_text()
    assert gatefile.rows(stage_policy)[0][1] == "prd-approved"
    assert (public / "recipe/ids.txt").read_text() == f"recipe_pin={constants.recipe_id(dev_repo, 'pin')}\n"
    assert files(root / "fixtures-src") == {"planted/p.lean", "proof1b/q.lean"}
    assert not digests(root / "fixtures-src") & digests(public)
    shutil.copy(dev_repo / "fixtures/planted/p.lean", dev_repo / "fixtures/toy/copy.lean")
    with pytest.raises(LedgerStop, match="planted.*fixtures/toy/copy.lean"):
        stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)


def test_refuses_empty_public_name(dev_repo, stage_policy, root, monkeypatch):
    """Nothing is staged, not even in a dry run, while the public name, the publisher or the privacy denylist
    is empty, or a rendered root file keeps a placeholder. Under the development overlay an empty name and
    publisher stand in as dev-placeholder, the public name is marked a development snapshot, and development-overlay
    records are staged."""
    # covers: test_refuses_empty_publisher
    path = dev_repo / "recipe/constants.toml"
    named = path.read_text()
    for field, value in (("public_name", "Example Ledger"), ("publisher", "Example Organisation")):
        path.write_text(named.replace(f'{field} = "{value}"', f'{field} = ""'))
        with pytest.raises(LedgerStop, match=f"^{field} empty"):
            stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)
    denylist = Path(stage_policy.values["privacy_denylist"])
    terms = denylist.read_text()
    denylist.write_text("# no terms\n")
    path.write_text(named)
    with pytest.raises(LedgerStop, match="denylist has no terms"):
        stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)
    denylist.write_text(terms)
    rules = (dev_repo / "templates/RULES.md.tmpl").read_text()
    (dev_repo / "templates/RULES.md.tmpl").write_text(rules + "{licence}\n")
    with pytest.raises(LedgerStop, match="RULES.md: unrendered {licence}"):
        stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)
    assert not (root / "public").exists()
    (dev_repo / "templates/RULES.md.tmpl").write_text(rules)
    path.write_text(named.replace('"Example Ledger"', '""').replace('"Example Organisation"', '""'))
    monkeypatch.setenv("LEDGER_DEV_ROOT", str(root))
    (root / "dev-overlay.toml").write_text('header = "import Aesop\\n"\nbuild_targets = ["Aesop"]\n')
    (dev_repo / "fixtures/toy/records.jsonl").write_text(json.dumps({"dev_overlay": True}))
    stage.stage(stage_policy, constants.load(dev_repo), dry_run=False)
    assert (root / "public/README.md").read_text().startswith("# dev-placeholder — DEV SNAPSHOT — NOT EVIDENCE\n")
    assert (root / "public/fixtures/toy/records.jsonl").exists()
    assert 'name: "dev-placeholder"' in (root / "public/CITATION.cff").read_text()


@pytest.mark.parametrize("gate, rel, old, new, held", [
    ("d7-sample", "recipe/constants.toml", "seed = 0", "seed = 7", True),
    ("classifier-freeze", "classifier/table-v1.toml", 'version = "v1"', 'version = "v2"', True),
    ("d7-sample", "classifier/table-v1.toml", 'version = "v1"', 'version = "v2"', False),
], ids=["test_refuses_overwriting_recorded_constant", "test_refuses_overwriting_frozen_table",
        "constants-line-leaves-table-staged"])
def test_refuses_overwriting_recorded(dev_repo, stage_policy, root, gate, rel, old, new, held):
    """Until a gate line records a change to the constants or the classifier table, staging copies the
    development copy over the public one, as it replaces every staged path, dropping what the development
    repository no longer holds. After it, staging neither copies nor removes that path, and names it in its
    report: the public copy is its only home. Each path is held by its own gate lines only: a constants line
    leaves the table staged. A public-only file beside it is never removed."""
    (dev_repo / "classifier").mkdir()
    (dev_repo / "classifier/table-v1.toml").write_text('version = "v1"\n')
    consts = constants.load(dev_repo)
    stage.stage(stage_policy, consts, dry_run=False)
    edit(dev_repo / rel, old, new)
    (dev_repo / "fixtures/toy/t.lean").unlink()
    stage.stage(stage_policy, consts, dry_run=False)
    assert new in (root / "public" / rel).read_text() and not (root / "public/fixtures/toy/t.lean").exists()
    gatefile.append(stage_policy, gate, "recorded", "pipeline", "changed by its command", TODAY)
    (beside := (root / "public" / rel).with_name("beside.toml")).write_text("kept = true\n")
    edit(dev_repo / rel, new, old)
    report = stage.stage(stage_policy, consts, dry_run=False)
    assert (new if held else old) in (root / "public" / rel).read_text() and beside.exists()
    assert (rel in report.held) is held
    if not held:
        return
    (dev_repo / rel).unlink()
    stage.stage(stage_policy, consts, dry_run=False)
    assert new in (root / "public" / rel).read_text()


@pytest.mark.parametrize("rel, lines, kind", [
    ("src/ledger/planted.py", ["# notes in " + str(Path("/mnt", "data")),
                               "# see http://localhost" + str(Path("/home", "someone"))],
     "host path"),
    ("tests/planted.py", ["# built on {host}"], "host name or address"),
    ("fixtures/toy/planted.lean", ["-- {scrub}", "-- {address}"], "host name or address"),
    ("src/ledger/planted.py", ["# " + "@".join(["someone", "example.org"]), "# " + "@".join(["ops", "house.lan"])],
     "e-mail address"),
    ("templates/planted.md", ["{term}"], "denylist term"),
    ("fixtures/toy/records.jsonl", [json.dumps({"dev_overlay": True})], "development-overlay record"),
    ("recipe/pin/planted.txt", ["see /etc/hosts", "or ~/notes", "or file:///x"], "absolute path"),
    ("templates/planted.md", ["reached at 10.0.0.1.", "and fd00::1", "2001:db8::1:fd7a::1", "192.0.2.1:10.0.0.1",
                              "2001:db8::192.168.1.1"],
     "IP address"),
    ("templates/planted.md", ["PRD", "story 3", "the open decision", "§ 2", "the spec", "docs/x.md"],
     "private reference"),
    ("fixtures/toy/planted.lean", ["-- x = {scrub}_probe", "-- {scrub}2", "-- x_{scrub}"], "host name or address"),
    ("templates/planted.md", ["x@example.invalid", "192.0.2.1 and 2001:db8::1", "https://example.invalid/x/y",
                              "{scrub}s, x{scrub} and the Ledger package"], None),
], ids=["test_privacy_sweep_path", "test_privacy_sweep_host", "scrub-and-host-address", "test_privacy_sweep_email",
        "test_privacy_sweep_denylist", "test_refuses_dev_overlay_records", "absolute-paths-in-published-text",
        "ip-literals-in-published-text", "private-references-in-published-text", "names-bounded-by-letters",
        "placeholders-allowed"])
def test_privacy_sweep(dev_repo, stage_policy, rel, lines, kind):
    """Staging refuses a tree where a staged file names a host path (in a URL's path too), this host, a
    scrubbed name or host address, an e-mail address, a denylisted term in any case, or a development-overlay
    record; and where the published text of recipe/ and templates/ holds any absolute path, an IP address (glued to
    or read within a documentation address too) or a reference a public reader cannot follow. It names each file and
    line, never the text found. The reserved placeholders and documentation addresses pass, a scrubbed name matches
    wherever no letter touches it, and the package name is never one."""
    values = {"host": socket.gethostname(), "scrub": stage_policy.values["scrub"][0],
              "address": stage_policy.values["host_addresses"][0],
              "term": Path(stage_policy.values["privacy_denylist"]).read_text().split()[-1].upper()}
    text = "".join(line + "\n" for line in lines)
    for key, value in values.items():
        text = text.replace("{" + key + "}", value)
    (dev_repo / rel).parent.mkdir(parents=True, exist_ok=True)
    (dev_repo / rel).write_text(text)
    if kind is None:
        stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)
        return
    with pytest.raises(LedgerStop) as stop:
        stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)
    assert str(stop.value) == "privacy sweep: " + "; ".join(f"{rel}:{n}: {kind}" for n in range(1, len(lines) + 1))


def test_sweep_is_linear_in_a_line(stage_policy):
    """The e-mail check scans from each `@`, so a 4 MiB line of word characters is swept in under a second, and
    an address at the end of such a line is still found."""
    line, start = "a" * (4 << 20), time.monotonic()
    privacy.sweep([("results/long.txt", line.encode())], stage_policy)
    with pytest.raises(LedgerStop, match=r"^privacy sweep: results/long.txt:1: e-mail address$"):
        privacy.sweep([("results/long.txt", "@".join([line, "example.org"]).encode())], stage_policy)
    assert time.monotonic() - start < 1


def test_sweep_covers_every_committed_path_and_byte(staged, dev_repo, stage_policy, monkeypatch):
    """stage and publish, dry runs included, sweep every path name and every byte the commit would hold, not
    only what stage copies: a file already in the public tree is swept as well, a file that is not UTF-8 is
    refused, and so is an unrendered placeholder outside the code, in a path name too. Both require the house
    sweep clean over that same set, and refuse a path name that is not UTF-8. publish also sweeps every commit no
    tag reaches: a finding committed, then removed, is refused until origin holds that commit, whatever local tag
    reaches it, and so is a path any of those commits names, a merge's too, and one that is not UTF-8. It reads
    each blob as git stores it and refuses any NUL byte."""
    # covers: test_privacy_sweep_path_names
    term = Path(stage_policy.values["privacy_denylist"]).read_text().split()[-1].upper()
    scrub = stage_policy.values["scrub"][0]
    for rel, text in ((f"responses/{term}.md", "received\n"),
                      ("results/records.jsonl", json.dumps({"dev_overlay": True})),
                      ("results/{public_name}.md", "received\n"), (f"responses/{scrub}_notes.md", "received\n")):
        (staged / rel).parent.mkdir(exist_ok=True)
        (staged / rel).write_text(text)
    (staged / "responses/u16.md").write_text("received\n", encoding="utf-16")
    runs = (lambda: stage.stage(stage_policy, constants.load(dev_repo), dry_run=True),
            lambda: publish.publish(stage_policy, tag=None, dry_run=True))
    for run in runs:
        with pytest.raises(LedgerStop) as stop:
            run()
        assert str(stop.value) == (f"privacy sweep: responses/{term}.md:0: denylist term; responses/u16.md:0: not "
                                   f"UTF-8; responses/u16.md:0: NUL byte; responses/{scrub}_notes.md:0: host name or "
                                   "address; results/records.jsonl:1: development-overlay record; "
                                   "results/{public_name}.md:0: unrendered placeholder")
    shutil.rmtree(staged / "responses")
    shutil.rmtree(staged / "results")
    (staged / "responses").mkdir()
    (staged / "responses/house-finding.md").write_text("found\n")
    for run in runs:
        with pytest.raises(LedgerStop, match="house privacy sweep"):
            run()
    (staged / "responses/house-finding.md").unlink()
    identity = stage_policy.values["identity"]
    (latin := staged / os.fsdecode(f"responses/{scrub}-r".encode() + b"\xe9ponse.md")).write_text("received\n")
    for run in runs:
        with pytest.raises(LedgerStop, match="path name that is not UTF-8"):
            run()
    stage.commit(staged, identity, "Latin-1 name", ("responses",))
    latin.unlink()
    stage.commit(staged, identity, "Drop it", ("responses",))
    with pytest.raises(LedgerStop) as stop:
        publish.publish(stage_policy, tag=None, dry_run=True)
    assert str(stop.value) == (f"privacy sweep: responses/{scrub}-r\ufffdponse.md:0: not UTF-8; "
                               f"responses/{scrub}-r\ufffdponse.md:0: host name or address")
    git("-C", staged, "update-ref", "refs/remotes/origin/main", "HEAD")
    (staged / "responses/note.md").write_text(f"reached at {stage_policy.values['host_addresses'][0]}\n")
    stage.commit(staged, identity, "Note", ("responses",))
    shutil.rmtree(staged / "responses")
    stage.commit(staged, identity, "Drop the note", ("responses",))
    with pytest.raises(LedgerStop, match=r"^privacy sweep: responses/note.md:1: host name or address$"):
        publish.publish(stage_policy, tag=None, dry_run=True)
    git("-C", staged, "tag", "scratch-mark")
    with pytest.raises(LedgerStop, match="responses/note.md"):
        publish.publish(stage_policy, tag=None, dry_run=True)
    git("-C", staged, "update-ref", "refs/remotes/origin/main", "HEAD")  # what a push leaves
    publish.publish(stage_policy, tag=None, dry_run=True)
    pushed = git("-C", staged, "rev-parse", "HEAD").strip()  # a pushed blob renamed and back, each in a merge
    git("-C", staged, "mv", "LICENSE", f"{scrub}.md")
    renamed = git("-C", staged, "write-tree").strip()
    git("-C", staged, "mv", f"{scrub}.md", "LICENSE")
    who = ["-c", f"user.name={identity['name']}", "-c", f"user.email={identity['email']}"]
    monkeypatch.setenv("TZ", "UTC")  # the project identity commits at +0000
    merge = git("-C", staged, *who, "commit-tree", renamed, "-p", pushed, "-p", f"{pushed}~", "-m", "Merge").strip()
    back = git("-C", staged, *who, "commit-tree", f"{pushed}^{{tree}}", "-p", merge, "-p", pushed, "-m", "M").strip()
    git("-C", staged, "update-ref", "HEAD", back)
    with pytest.raises(LedgerStop, match=rf"^privacy sweep: {scrub}.md:0: host name or address$"):
        publish.publish(stage_policy, tag=None, dry_run=True)


@pytest.mark.parametrize("attributes", [".gitattributes", ".git/info/attributes"])
def test_publish_refuses_git_attributes(staged, dev_repo, stage_policy, attributes):
    """publish refuses a git attributes file in the commits it would push, even once removed, and stage and
    publish one in the public tree's git directory: either converts the bytes git add stores. The blob publish
    sweeps is the stored one."""
    scrub = stage_policy.values["scrub"][0]
    (staged / attributes).write_text("responses/*.md working-tree-encoding=UTF-16LE\n")
    (staged / "responses").mkdir()
    (staged / "responses/x.md").write_text(f"{scrub}\n", encoding="utf-16-le")
    if attributes == privacy.INFO_ATTRIBUTES:
        with pytest.raises(LedgerStop, match=f"{attributes}:0: git attributes file"):
            stage.stage(stage_policy, constants.load(dev_repo), dry_run=False)
    stage.commit(staged, stage_policy.values["identity"], "Attributes")
    if attributes == ".gitattributes":
        (staged / attributes).unlink()
    shutil.rmtree(staged / "responses")
    stage.commit(staged, stage_policy.values["identity"], "Clean")
    with pytest.raises(LedgerStop) as stop:
        publish.publish(stage_policy, tag=None, dry_run=True)
    assert str(stop.value) == (f"privacy sweep: {attributes}:0: git attributes file; "
                               "responses/x.md:1: host name or address")


def test_dry_run_no_commit_no_remote(staged, dev_repo, stage_policy, monkeypatch):
    """A dry run of stage, then of publish, commits nothing, tags nothing, leaves the public tree as it was and
    contacts no remote, even with no TCP port rule on the children: a listener standing in for the remote, which would
    close the first connection at once, accepts none."""
    (dev_repo / "src/ledger/added.py").write_text("")
    (staged / "responses").mkdir()
    (staged / "responses/2026-12-01-upstream.md").write_text("received\n")
    head = git("-C", staged, "rev-parse", "HEAD")
    with socket.create_server(("127.0.0.1", 0)) as listener:
        git("-C", staged, "remote", "add", "origin", f"http://127.0.0.1:{listener.getsockname()[1]}/public.git")
        accepted = []
        threading.Thread(target=lambda: accepted.append(listener.accept()[0].close()), daemon=True).start()
        monkeypatch.setattr(confine, "_container", True)  # children reach any TCP port
        stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)
        publish.publish(stage_policy, tag="v0-pin", dry_run=True)
    assert accepted == []
    assert git("-C", staged, "rev-parse", "HEAD") == head and git("-C", staged, "tag") == ""
    assert git("-C", staged, "status", "--porcelain") == "?? responses/\n"
    assert not (staged / "src/ledger/added.py").exists()


def test_gates_file_created_only_when_absent(dev_repo, stage_policy, root):
    """The first stage creates the public gate file from the bootstrap copy, refusing a copy that does not open
    with the approval line or holds a line breaking the gate-file rules. Once it exists, staging never
    replaces it."""
    bootstrap = root / "gates/GATES.md"
    approved = bootstrap.read_text()
    template = (dev_repo / "templates/GATES.md.tmpl").read_text()
    for text in (template, approved + "| 2026-10-02 | d0 | recorded | Example Person | pin commit |\n"):
        bootstrap.write_text(text)
        with pytest.raises(LedgerStop, match="bootstrap gate file"):
            stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)
    bootstrap.write_text(approved)
    stage.stage(stage_policy, constants.load(dev_repo), dry_run=False)
    gatefile.append(stage_policy, "d0", "recorded", "operator", "pin commit", TODAY)
    recorded = (root / "public/gates/GATES.md").read_text()
    stage.stage(stage_policy, constants.load(dev_repo), dry_run=False)
    assert (root / "public/gates/GATES.md").read_text() == recorded != approved


@pytest.mark.parametrize("plant", ["records", "summary", "membership"])
def test_planted_absence_by_digest_planted_and_proof1b(snapshot, dev_repo, stage_policy, root, plant):
    """Staging stops, naming the file, when the digest of a pair a fixture run assembles from an honesty-proof entry,
    of fixtures/planted/ under the recipe's header or of fixtures/proof1b/ under its project's own, or of one the
    assembler refuses, would be published anywhere: in the records, the summary or the membership."""
    _, found = snapshot
    for rel in ("fixtures/planted", "fixtures/proof1b"):
        shutil.copytree(REPO / rel, dev_repo / rel, dirs_exist_ok=True)
    assembly = constants.load(dev_repo).published["assembly"]
    collision = next(entry for entry in ingest.parse(dev_repo / "fixtures/planted/entries.json",
                                                     assembly["suffix_regex"]) if entry.refusal)
    text = {"records": f"{assembly['header']}theorem planted_sorry__p0 : (1 : ℕ) = 2 := by\n  sorry\n",
            "summary": f"{fixtures.HEADER}theorem companion__p0 : True := by\n  trivial\n",
            "membership": f"refused\t{collision.position}\t0\t{collision.element_sha256[0]}"}[plant]
    digest = hashlib.sha256(text.encode()).hexdigest()
    if plant == "records":
        progress = json.loads((root / "results/progress.json").read_text())
        progress["harness_overrides"] = {found[1]["pair_sha256"]: {
            "source": "crosspass-d44", "detail": f"sha256:{digest}", "date": "2026-12-01",
            "at": "2026-12-01T03:00:00Z"}}
        (root / "results/progress.json").write_text(json.dumps(progress))
    elif plant == "summary":
        gatefile.append(stage_policy, "palomar-check", "unchanged", "assistant", f"seen sha256:{digest}", TODAY)
    else:
        membership = root / "results/membership.txt"
        membership.write_text(re.sub("sha256=[0-9a-f]+", f"sha256={digest}", membership.read_text()))
    with pytest.raises(LedgerStop, match=f"planted fixture entries would be published: .*results/{plant}"):
        stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)


def test_results_wait_for_every_drawn_pair(snapshot, dev_repo, stage_policy, root):
    """A dry run writes nothing in the root. While a drawn pair has a leg not terminal, staging stages the code alone,
    leaving the published results and README as they were, and says why."""
    public, found = snapshot
    before = {path: path.stat().st_mtime_ns for path in root.rglob("*") if path.is_file()}
    stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)
    assert {path: path.stat().st_mtime_ns for path in root.rglob("*") if path.is_file()} == before
    progress = json.loads((root / "results/progress.json").read_text())
    progress["legs"][found[1]["pair_sha256"]]["pin"]["terminal"] = False
    (root / "results/progress.json").write_text(json.dumps(progress))
    (dev_repo / "src/ledger/later.py").write_text('"""Staged while a run is under way."""\n')
    published = {path: path.read_bytes() for path in [public / "README.md", *(public / "results").iterdir()]}
    report = stage.stage(stage_policy, constants.load(dev_repo), dry_run=False)
    assert report.late == f"{found[1]['pair_id']}: its pin leg is not terminal, so the pair has no record yet"
    assert {path: path.read_bytes() for path in [public / "README.md", *(public / "results").iterdir()]} == published
    assert git("-C", public, "ls-files", "src/ledger/later.py") == "src/ledger/later.py\n"


@pytest.mark.parametrize("text, kind", [
    ('File "/root/tree/x.py", line 3, via 8.8.8.8:53, at https://example.org/a', None),
    ("from {split}", "host name or address"),
    ("from {encoded}", "host name or address"),
    ("cd %2Fsrv%2Fsomeone", "host path"),
    ("on {fullwidth}", "host name or address"),
], ids=["kept", "split", "percent-encoded", "percent-encoded-path", "fullwidth"])
def test_scrub_transcript_residue_after_normalising(stage_policy, text, kind):
    """What remains of the transcript is swept again with each line joined to the next, NFKC-normalised and
    percent-decoded, and a hit only that finds stops staging, naming its line: a host address split or percent-encoded,
    a host path encoded, a name in another form of its letters. Container paths, public addresses and links stay."""
    scrub, address = stage_policy.values["scrub"][0], stage_policy.values["host_addresses"][0]
    text = text.format(split=f"{address[:4]}\n{address[4:]}", encoded="".join(f"%{b:02X}" for b in address.encode()),
                       fullwidth="".join(chr(ord(c) + 0xFEE0) for c in scrub))
    if kind is None:
        assert stage.scrub_transcript(text, stage_policy) == text
    else:
        with pytest.raises(LedgerStop, match=f"privacy sweep: proofs/proof-4/transcript.md, each line joined to the "
                                             f"next:1: {kind}"):
            stage.scrub_transcript(text, stage_policy)


def test_scrub_transcript_removes_and_fails_on_residue(staged, dev_repo, stage_policy, monkeypatch, tmp_path):
    """scrub_transcript withholds everything the privacy sweep refuses: every scrub term and this host's name, in any
    case, wherever no letter touches it, each address inside an entry of host_addresses, a prefix too, or live on this
    host, in any form (glued to a label or a port, an IPv6 address embedding one too) with the run of address
    characters it is in, each denylist term, each NUL byte, and each host path up to a space, quote, comma or bracket
    and each e-mail address whole, before any term or name within it, and each address the internet does not route
    but slirp's own and the documentation ranges; every other address stays. It stops when the sweep still refuses
    what remains, and the sweep finds each address glued to a label, to another address, to a port or by a dot, after a
    digit of another script, and a dotted quad's zero-padded octets.
    Staging commits the stranger's transcript so scrubbed, every other byte as it was, and stops on one that is not
    UTF-8."""
    scrub, address = stage_policy.values["scrub"][0], stage_policy.values["host_addresses"][0]
    term = Path(stage_policy.values["privacy_denylist"]).read_text().split()[-1]
    live, leaf, six = {}, "", Path("/proc/net/if_inet6")  # one live address of each family this host has
    for line in Path("/proc/net/fib_trie").read_text().splitlines():
        if "|--" in line:
            leaf = line.split()[-1]
        elif line.strip() == "/32 host LOCAL" and not leaf.startswith("127."):
            live[4] = ipaddress.IPv4Address(leaf)
    for line in six.read_text().splitlines() if six.exists() else []:
        if line.split()[0] != f"{1:032x}":
            live[6] = ipaddress.IPv6Address(int(line.split()[0], 16))
    live = live.values()
    hex_embeds = ["::ffff:cb00:7107", "64:ff9b::cb00:7107"]  # 203.0.113.7, written in hex
    labelled = ["inet addr:192.168.1.5", "src:10.1.2.3", "host:fd7a::1", "ipv6:2a01:4f8::1"]
    glued = ["addr::192.168.1.5", "x.py:12:10.0.0.1", "dead:beef:10.0.0.1", "ad:fd7a:115c:a1e0::53",
             "ip_fd7a:115c:a1e0::53", "fe:2a01:4f8::1", "2a01:4f8::1:443", "fd7a:115c:a1e0::53.53", "fd7a::1.Each",
             "cafe.fd7a::1", "eth0.fd7a::1", "\u066310.0.0.1", "\uff1110.0.0.1", "192.168.001.005", "010.000.000.001"]
    wide = dataclasses.replace(stage_policy, values=stage_policy.values | {
        "host_addresses": [address, "198.18.0.0/15", "2001:db8:abcd::/48", "203.0.113.7", "192.168.1.5", "10.1.2.3",
                           "fd7a::1", "2a01:4f8::1", "10.0.0.1", "fd7a:115c:a1e0::53"]})
    text = (f"ssh {scrub.upper()}:22 from {address}, on {socket.gethostname()}; the Ledger package, x{scrub}\r\n"
            f"cd {'/home'}/someone/run && git log --author=someone@{'mail'}.example.org\r# {term.upper()}\n"
            f"--author={term}x@{'mail'}.example.org {scrub}.ops@{'mail'}.example.org\0\n"
            f'File "{'/srv'}/run/x.py", line 3, in "/root/tree/x.py" via 8.8.8.8:53, at https://example.org/a\n'
            f"from 198.18.4.7 port 22, [2001:db8:abcd::1234]:22, {ipaddress.IPv6Address(address).exploded}"
            f"{''.join(', ' + a.exploded for a in live)}; kept 203.0.113.77, 198.20.0.1\n"
            f"via 192.168.1.1, 100.64.0.1, fd12::1 and fe80::1; kept 10.0.2.2, 10.0.2.3:53\n{', '.join(labelled)}\n"
            f"{', '.join(hex_embeds)}\n")
    scrubbed = (f"ssh [withheld]:22 from [withheld], on [withheld]; the Ledger package, x{scrub}\r\n"
                "cd [withheld] && git log --author=[withheld]\r# [withheld]\n"
                "--author=[withheld] [withheld][withheld]\n"
                'File "[withheld]", line 3, in "/root/tree/x.py" via 8.8.8.8:53, at https://example.org/a\n'
                f"from [withheld] port 22, [[withheld]]:22, [withheld]{', [withheld]' * len(live)}; kept 203.0.113.77, "
                "198.20.0.1\nvia [withheld], [withheld], [withheld] and [withheld]; kept 10.0.2.2, 10.0.2.3:53\n"
                "inet addr[withheld], sr[withheld], host[withheld], ipv[withheld]\n[withheld], [withheld]\n")
    assert stage.scrub_transcript(text, wide) == scrubbed
    for form in (*map(str, live), *(f"::ffff:{a}" for a in live if a.version == 4), "64:ff9b::203.0.113.7",
                 "::203.0.113.7", "2002:cb00:7107::1", *hex_embeds, *labelled, *glued):  # 6to4 before the glued forms
        with pytest.raises(LedgerStop, match="privacy sweep: x.md:1: host name or address"):
            privacy.sweep([("x.md", form.encode())], wide)
    residue = dataclasses.replace(stage_policy, values=stage_policy.values | {"scrub": ["withheld"]})
    with pytest.raises(LedgerStop, match="privacy sweep: proofs/proof-4/transcript.md:1: host name or address"):
        stage.scrub_transcript("on withheld\n", residue)
    (transcript := staged / "proofs/proof-4/transcript.md").parent.mkdir(parents=True)
    transcript.write_bytes(b"\xff\n")
    with pytest.raises(LedgerStop, match="proofs/proof-4/transcript.md: not UTF-8"):
        stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)
    transcript.write_bytes(text.encode())
    stage.stage(stage_policy, constants.load(dev_repo), dry_run=False)
    assert transcript.read_bytes() == stage.scrub_transcript(text, stage_policy).encode() and git("-C", staged, "status", "--porcelain") == ""
    monkeypatch.setattr(privacy, "FIB_TRIE", tmp_path / "fib_trie")  # a leaf of two entries; no IPv6 at all
    monkeypatch.setattr(privacy, "IF_INET6", tmp_path / "absent")
    privacy.FIB_TRIE.write_text("  +-- 192.0.2.0/24 2 0 2\n     |-- 192.0.2.0\n        /24 link UNICAST\n"
                                "     |-- 192.0.2.7\n        /24 link UNICAST\n        /32 host LOCAL\n")
    own = privacy.own(stage_policy)
    assert own[len(stage_policy.values["host_addresses"]):] == [ipaddress.ip_network("192.0.2.7")]
