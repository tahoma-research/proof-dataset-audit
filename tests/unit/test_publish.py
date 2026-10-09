import hashlib
import json
import os
import pty
import re
import subprocess
from datetime import date

import pytest
from helpers import ENV, PY, git

from ledger import aggregate, cli, confine, constants, gatefile, publish, records, report, stage
from ledger.types import LedgerStop

IDENTITY = "Example Project <project@example.invalid>"


def origin(public, monkeypatch):
    """A bare repository on this machine, set as the public tree's origin, which publish takes in GitHub's
    place, and a token typed for it, which it never asks for. It lies in the public tree's .git, the one place
    the push may write."""
    remote = public / ".git/origin.git"
    git("init", "-q", "--bare", remote)
    git("-C", public, "remote", "add", "origin", remote)
    monkeypatch.setattr(publish, "ORIGIN", re.compile(re.escape(str(remote))))
    monkeypatch.setattr("getpass.getpass", lambda prompt: "unused")
    return remote


def pushed(tree, *tags):
    """Record tags as a push records them."""
    for tag in tags:
        git("-C", tree, "update-ref", f"refs/ledger/pushed-tags/{tag}", "HEAD")


def test_refuses_without_tty(make_policy):
    """publish runs only when the operator asks for it at a terminal: through pipes, with stdin alone a
    terminal, or without --operator, it stops before any work."""
    terminal, _ = pty.openpty()
    for argv, stdin, reason in ((["--operator"], subprocess.PIPE, "terminal"), (["--operator"], terminal, "terminal"),
                                ([], subprocess.PIPE, "--operator")):
        run = subprocess.run([PY, "-m", "ledger", "publish", "--dry-run", *argv, "--policy", make_policy()],
                             stdin=stdin, capture_output=True, text=True, env=ENV)
        assert run.returncode == 2 and reason in run.stderr, run.stderr
    os.close(terminal)


def test_operator_commands_skip_self_test(make_policy, root):
    """The operator's stage and publish take the run lock and never run the confinement self-test, which a
    terminal's own security label could fail; publish, the push at a terminal, is not confined at all."""
    terminal, _ = pty.openpty()
    for argv, confinement in ((["stage", "--dry-run"], "- confinement: Landlock ABI"),
                              (["publish", "--operator", "--dry-run"], "- confinement: not applied: publish")):
        run = subprocess.run([PY, "-m", "ledger", *argv, "--policy", make_policy()], stdin=terminal, stdout=terminal,
                             stderr=subprocess.PIPE, text=True, env=ENV)
        report = max((root / "runs").glob("*/report.md")).read_text()
        assert run.returncode == 2 and argv[0] in report and confinement in report, report + run.stderr
        assert "self-test" not in report
    os.close(terminal)


def test_author_and_committer_are_project_identity(dev_repo, stage_policy, root, tmp_path, monkeypatch):
    """Every public-tree commit, stage's and publish's, has the project identity as author and committer: a
    personal identity in the global git config or the environment never reaches one. publish pushes HEAD to
    origin's main, whatever branch is checked out, and the tag, and nothing else. Each commit's time is UTC."""
    home = tmp_path / "home"
    home.mkdir()
    (home / ".gitconfig").write_text("[user]\n\tname = Leaked Name\n\temail = leaked@example.invalid\n")
    for name, value in (("HOME", home), ("GIT_AUTHOR_EMAIL", "leaked@example.invalid"),
                        ("GIT_COMMITTER_NAME", "Leaked")):
        monkeypatch.setenv(name, str(value))
    stage.stage(stage_policy, constants.load(dev_repo), dry_run=False)
    public = root / "public"
    remote = origin(public, monkeypatch)
    (public / "responses").mkdir()
    (public / "responses/2026-12-01-upstream.md").write_text("received\n")
    git("-C", public, "checkout", "-q", "-b", "notes")
    publish.publish(stage_policy, tag="v0-pin", dry_run=False)
    assert git("-C", public, "log", "--date=format:%z", "--format=%an <%ae> %ad|%cn <%ce> %cd").splitlines() == [
        f"{IDENTITY} +0000|{IDENTITY} +0000"] * 2
    assert git("-C", remote, "for-each-ref", "--format=%(refname)") == "refs/heads/main\nrefs/tags/v0-pin\n"
    assert git("-C", remote, "rev-parse", "main", "v0-pin") == git("-C", public, "rev-parse", "HEAD", "HEAD")


def test_publish_refuses_foreign_commit_identity_and_message(staged, stage_policy, monkeypatch):
    """publish refuses a commit origin lacks whose author or committer is not the project identity, that holds
    a header but tree, parent, author and committer, or whose message holds what the privacy sweep finds,
    naming the commit and never the text found; a commit origin holds is not checked again. Its times are UTC."""
    monkeypatch.setenv("TZ", "UTC")
    project = ["-c", f"user.name={IDENTITY.split(' <')[0]}", "-c", "user.email=project@example.invalid"]
    base = git("-C", staged, "rev-parse", "HEAD").strip()
    scrub = stage_policy.values["scrub"][0]
    foreign = ": a header but tree, parent, and the project identity as author and committer"
    for committer, args, found in ((project, ["--author=Example Project <other@example.invalid>", "-m", "Note"],
                                    foreign),
                                   (["-c", "user.name=Other", "-c", "user.email=other@example.invalid"],
                                    [f"--author={IDENTITY}", "-m", "Note"], foreign),
                                   ([*project, "-c", "i18n.commitEncoding=UTF-7"], ["-m", "Note"], foreign),
                                   (project, ["--date=2026-10-02T00:00:00-0700", "-m", "Note"], foreign),
                                   (project, ["-m", f"notes from {scrub}"], " message:1: host name or address")):
        git("-C", staged, *committer, "commit", "-q", "--allow-empty", *args)
        sha = git("-C", staged, "rev-parse", "HEAD").strip()
        with pytest.raises(LedgerStop, match=f"{sha}{found}") as stop:
            publish.publish(stage_policy, tag=None, dry_run=True)
        assert "other@" not in str(stop.value) and scrub not in str(stop.value)
        git("-C", staged, "reset", "-q", "--soft", base)
    git("-C", staged, *project, "commit", "-q", "--allow-empty", "--author=Other <other@example.invalid>", "-m", "x")
    git("-C", staged, "update-ref", "refs/remotes/origin/main", "HEAD")  # what a push leaves
    publish.publish(stage_policy, tag=None, dry_run=True)


def test_pushing_reads_a_large_blob_whole(staged, stage_policy, monkeypatch):
    """A blob origin lacks that is larger than confine.run's output bound is read whole and swept whole: what
    lies past the bound in it is found, though a later commit removed the file."""
    monkeypatch.setenv("TZ", "UTC")
    project = ["-c", f"user.name={IDENTITY.split(' <')[0]}", "-c", "user.email=project@example.invalid"]
    scrub = stage_policy.values["scrub"][0]
    data = ("x" * 63 + "\n").encode() * (confine.OUTPUT_MAX // 64) + f"from {scrub}\n".encode()
    (staged / "results").mkdir()
    (staged / "results/records.jsonl").write_bytes(data)
    git("-C", staged, "add", "results")
    git("-C", staged, *project, "commit", "-q", "-m", "Results")
    git("-C", staged, "rm", "-q", "results/records.jsonl")
    git("-C", staged, *project, "commit", "-q", "-m", "Results removed")
    assert ("results/records.jsonl", data) in publish._pushing(staged, stage_policy.values["identity"])
    with pytest.raises(LedgerStop, match=f"results/records.jsonl:{confine.OUTPUT_MAX // 64 + 1}: host name or address"):
        publish.publish(stage_policy, tag=None, dry_run=True)


def test_d0_tag_requires_matching_ids(staged, stage_policy):
    """The first tag, the pin's, is refused, in a dry run too, unless recipe/ids.txt is present and equals the
    recipe identifiers computed afresh from the tree, or when it is any tag but v0-pin."""
    for tag in ("v1.0.0-rc.1", "v1.0.0"):
        with pytest.raises(LedgerStop, match="first tag must be v0-pin"):
            publish.publish(stage_policy, tag=tag, dry_run=True)
    publish.publish(stage_policy, tag="v0-pin", dry_run=True)
    (staged / "recipe/pin/lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    with pytest.raises(LedgerStop, match="ids.txt"):
        publish.publish(stage_policy, tag="v0-pin", dry_run=True)
    git("-C", staged, "checkout", "--", "recipe")
    (staged / "recipe/ids.txt").unlink()
    with pytest.raises(LedgerStop, match="ids.txt"):
        publish.publish(stage_policy, tag="v0-pin", dry_run=True)


def test_final_tag_refuses_changes_outside_window_paths(staged, stage_policy, monkeypatch):
    """While the latest pushed tag is a pre-release, every publish, tagged or not and dry run included, is checked
    before it commits anything, and after a publish that pushes has asked for the token: accepted while only
    responses/, proofs/proof-4/ and the gate file changed since that tag, committed or not, and while the gate
    file only grew, and refused, naming the path and the re-dispatch rule, once anything else did. A new
    pre-release tag starts a new window."""
    pushed(staged, "v1.0.0-rc.1")
    for rel in ("responses/2026-12-01-upstream.md", "proofs/proof-4/result.json"):
        (staged / rel).parent.mkdir(parents=True)
        (staged / rel).write_text("{}\n")
    gatefile.append(stage_policy, "proof-4", "pass", "stranger", "digests equal", date(2026, 12, 1))
    stage.commit(staged, stage_policy.values["identity"], "Record the stranger's run", ("proofs",))
    publish.publish(stage_policy, tag="v1.0.0", dry_run=True)
    recorded = (staged / "gates/GATES.md").read_text()
    (staged / "gates/GATES.md").write_text(recorded.replace("approval date", "approval dated"))
    with pytest.raises(LedgerStop, match="append-only"):
        publish.publish(stage_policy, tag="v1.0.0", dry_run=True)
    (staged / "gates/GATES.md").write_text(recorded)
    (staged / "results").mkdir()
    (staged / "results/records.jsonl").write_text("{}\n")
    (staged / "gates/GATES.md.extra").write_text("{}\n")
    head, asked = git("-C", staged, "rev-parse", "HEAD"), []
    git("-C", staged, "remote", "add", "origin", "https://github.com/example/public.git")
    monkeypatch.setattr("getpass.getpass", lambda prompt: asked.append(prompt) or "unused")
    for tag, dry_run in (("v1.0.0", True), (None, True), (None, False)):
        with pytest.raises(LedgerStop, match="gates/GATES.md.extra, results/records.jsonl.*new pre-release tag"):
            publish.publish(stage_policy, tag=tag, dry_run=dry_run)
    assert git("-C", staged, "rev-parse", "HEAD") == head and len(asked) == 1
    publish.publish(stage_policy, tag="v1.0.0-rc.2", dry_run=True)


def test_window_reads_every_tag(staged, stage_policy):
    """The window holds while any pushed pre-release tag has no pushed final tag after it, whichever tag lies
    nearest HEAD, and a lower final tag, or a local tag no push recorded, leaves it open; a tag name is
    v<semver>, v<semver>-rc.<n> or v0-pin, with no leading zeros; at most two pre-release tags exist."""
    pushed(staged, "v0-pin", "v1.0.0-rc.1", "v0.0.1")
    git("-C", staged, "tag", "v1.0.0")
    (staged / "results").mkdir()
    (staged / "results/records.jsonl").write_text("{}\n")
    for tag in ("v1.0.0", None):
        with pytest.raises(LedgerStop, match="results/records.jsonl"):
            publish.publish(stage_policy, tag=tag, dry_run=True)
    for tag in ("v1.0.0-final", "V1.0.0-RC.1x", "example-host", "v1.0.0-rc.1-example-host", "v01.0.0"):
        with pytest.raises(LedgerStop, match="a tag is v<semver>"):
            publish.publish(stage_policy, tag=tag, dry_run=True)
    publish.publish(stage_policy, tag="v1.0.0-rc.2", dry_run=True)
    pushed(staged, "v1.0.0-rc.2")
    with pytest.raises(LedgerStop, match="two pre-release tags"):
        publish.publish(stage_policy, tag="v1.0.0-rc.3", dry_run=True)
    pushed(staged, "v1.0.0")
    publish.publish(stage_policy, tag=None, dry_run=True)


def test_origin_and_token_refused_first(staged, stage_policy, monkeypatch):
    """A publish that pushes refuses an origin but one https://github.com/<org>/<repo>.git URL before it asks
    for the token, and then an empty token, committing and recording nothing."""
    asked, head = [], git("-C", staged, "rev-parse", "HEAD")
    monkeypatch.setattr("getpass.getpass", lambda prompt: asked.append(prompt) or "")
    with pytest.raises(LedgerStop, match="pushes only to"):
        publish.publish(stage_policy, tag="v0-pin", dry_run=False)
    git("-C", staged, "remote", "add", "origin", "https://github.com/example/public.git")
    for url in ("http://github.com/example/public.git", "https://github.com.example.invalid/example/public.git",
                "https://user:@github.com/example/public.git", "https://github.com/example/public", "/tmp/public.git"):
        git("-C", staged, "remote", "set-url", "origin", url)
        with pytest.raises(LedgerStop, match="pushes only to"):
            publish.publish(stage_policy, tag="v0-pin", dry_run=False)
    git("-C", staged, "remote", "set-url", "origin", "https://github.com/example/public.git")
    git("-C", staged, "config", "--add", "remote.origin.url", "https://github.com/example/other.git")
    with pytest.raises(LedgerStop, match="pushes only to"):
        publish.publish(stage_policy, tag="v0-pin", dry_run=False)
    assert not asked
    git("-C", staged, "config", "--unset", "remote.origin.url", "other")
    with pytest.raises(LedgerStop, match="token is empty"):
        publish.publish(stage_policy, tag="v0-pin", dry_run=False)
    assert asked and git("-C", staged, "rev-parse", "HEAD") == head
    assert not git("-C", staged, "for-each-ref", "refs/ledger/")


def test_never_force(staged, stage_policy, tmp_path, monkeypatch):
    """A tag that exists is refused, and a remote that has moved on is never overwritten: the push is rejected
    whole, the remote keeps its branch and gets no tag, and the tag stays recorded, since a push git reports
    failed may have landed. A push that lands is recorded even when interrupted, and git's own pruning of the
    remote's refs forgets no pushed tag; a fetch refspec but origin's default, which could prune the record, is
    refused."""
    # covers: test_refuses_existing_tag
    remote = origin(staged, monkeypatch)
    publish.publish(stage_policy, tag="v0-pin", dry_run=False)
    run = confine.run

    def interrupted(argv, **kwargs):  # Ctrl-C the moment the push lands
        proc = run(argv, **kwargs)
        if "push" in argv and "--dry-run" not in argv:
            raise KeyboardInterrupt
        return proc
    monkeypatch.setattr(confine, "run", interrupted)
    with pytest.raises(KeyboardInterrupt):
        publish.publish(stage_policy, tag="v1.0.0-rc.1", dry_run=False)
    monkeypatch.setattr(confine, "run", run)
    git("-C", staged, "config", "remote.origin.fetch", "+refs/*:refs/*")
    with pytest.raises(LedgerStop, match="config outside the allowlist: remote.origin.fetch$"):
        publish.publish(stage_policy, tag=None, dry_run=True)
    git("-C", staged, "config", "remote.origin.fetch", "+refs/heads/*:refs/remotes/origin/*")
    git("-C", staged, "fetch", "-q", "--prune", "origin")
    git("-C", staged, "remote", "prune", "origin")
    with pytest.raises(LedgerStop, match="v0-pin exists"):
        publish.publish(stage_policy, tag="v0-pin", dry_run=True)
    (staged / "results").mkdir()
    (staged / "results/records.jsonl").write_text("{}\n")
    with pytest.raises(LedgerStop, match="changed since the pre-release tag v1.0.0-rc.1: results/records.jsonl"):
        publish.publish(stage_policy, tag=None, dry_run=False)
    clone = tmp_path / "clone"
    git("clone", "-q", "-b", "main", remote, clone)
    git("-C", clone, "-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-q", "--allow-empty",
        "-m", "t")

    def raced(argv, **kwargs):  # another push lands between the dry run and the push
        if "push" in argv and "--dry-run" not in argv:
            git("-C", clone, "push", "-q", "origin", "main")
        return run(argv, **kwargs)
    monkeypatch.setattr(confine, "run", raced)
    with pytest.raises(LedgerStop, match=r"(?s)rejected.*v1.0.0-rc.2 stays recorded"):
        publish.publish(stage_policy, tag="v1.0.0-rc.2", dry_run=False)
    assert git("-C", remote, "rev-parse", "main") == git("-C", clone, "rev-parse", "HEAD")
    assert git("-C", remote, "tag") == "v0-pin\nv1.0.0-rc.1\n"
    assert git("-C", staged, "for-each-ref", "--format=%(refname:lstrip=3)",
               "refs/ledger/pushed-tags/") == "v0-pin\nv1.0.0-rc.1\nv1.0.0-rc.2\n"


def test_index_summary_records_membership_agree(snapshot, dev_repo, stage_policy, root):
    """Staging runs the report and stages what it wrote: under results/, the records, the summary, the index, the
    membership, the progress file, the withdrawals and the finding report; at the root, the rendered README in
    place of the one before results. The index holds the sha256 of each staged file it names, the summary counts
    the records that are not withdrawn, and the membership lists the records' aggregate members, or nothing is
    staged."""
    public, found = snapshot
    results = public / "results"
    assert sorted(path.name for path in results.iterdir()) == [
        "FINDING_REPORT.md", "index.json", "membership.txt", "progress.json", "records.jsonl", "summary.json",
        "withdrawals.jsonl"]
    report.run(stage_policy, constants.load(public))
    assert (public / "README.md").read_bytes() == (root / "results/README.md").read_bytes()
    assert (results / "records.jsonl").read_bytes() == records.dump(found)

    def sha(path):
        return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()
    index, summary = (json.loads((results / name).read_text()) for name in ("index.json", "summary.json"))
    assert index["snapshot"] == {"records_sha256": sha(results / "records.jsonl"),
                                 "summary_sha256": sha(results / "summary.json"),
                                 "membership_sha256": sha(results / "membership.txt"),
                                 "canonical_subset_sha256": report.canonical_subset(found)}
    assert summary["canonical_subset_sha256"] == report.canonical_subset(found)
    assert [index["constants_sha256"], index["classifier"]["table_sha256"]] == [
        sha(public / "recipe/constants.toml"), sha(public / "classifier/table-v1.toml")]
    kept = [r for r in found if r["withdrawn"] is None]
    assert [summary["pairs"], summary["withdrawn"], summary["classes"]] == [
        len(kept), len(found) - len(kept), {cls: sum(r["class"] == cls for r in kept) for cls in summary["classes"]}]
    members = [r["pair_id"] for r in found if r["aggregate"]["member"]]
    assert (results / "membership.txt").read_text().splitlines()[1:] == members
    assert summary["membership"]["members"] == len(members) == 1
    aggregate.write_membership(root / "results", [*members, found[1]["pair_id"]])
    with pytest.raises(LedgerStop, match="results/membership.txt is not the records' aggregate members in draw "
                                         "order; listed beyond them: p1__p0; not listed: none"):
        stage.stage(stage_policy, constants.load(dev_repo), dry_run=True)


def test_table_regeneration_hashes(snapshot, stage_policy, monkeypatch, capsys):
    """`report --from-records` over the staged records and the published table derives them again, byte for byte,
    and prints the published content hash and canonical-subset hash."""
    public, _ = snapshot
    published = json.loads((public / "results/index.json").read_text())["snapshot"]
    monkeypatch.setattr(confine, "apply_fs", lambda pol: None)  # the real one would also confine this process
    assert cli.main(["report", "--from-records", str(public / "results/records.jsonl"), "--policy",
                     str(stage_policy.path)]) == 0
    assert capsys.readouterr().out == (f"records.jsonl: every record derived again, byte for byte; "
                                       f"{published['records_sha256']}; canonical subset "
                                       f"{published['canonical_subset_sha256']}\n")


def test_snapshot_immutable_after_growth(snapshot, stage_policy, monkeypatch):
    """A published tag resolves to the same tree, at origin and in the public tree's record of it, after the
    repository grows by a commit under a second tag; a third publish under the first tag is refused."""
    public, _ = snapshot
    remote = origin(public, monkeypatch)
    publish.publish(stage_policy, tag="v0-pin", dry_run=False)
    tree = git("-C", remote, "rev-parse", "v0-pin^{tree}")
    (public / "responses").mkdir()
    (public / "responses/2026-12-01-upstream.md").write_text("received\n")
    publish.publish(stage_policy, tag="v1.0.0-rc.1", dry_run=False)
    assert git("-C", remote, "rev-parse", "main^{tree}") != tree
    with pytest.raises(LedgerStop, match="v0-pin exists"):
        publish.publish(stage_policy, tag="v0-pin", dry_run=False)
    assert git("-C", remote, "rev-parse", "v0-pin^{tree}") == tree
    assert git("-C", public, "rev-parse", f"{publish.PUSHED}v0-pin^{{tree}}") == tree
