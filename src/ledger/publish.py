"""Publication: the operator's push of the public tree to its one remote, under a tag that is never moved, and
the withdrawal that answers a takedown demand by marking a published record, never deleting it. It is the only push
the project makes."""

import getpass
import json
import os
import re
import resource
from datetime import date
from pathlib import Path

from ledger import confine, constants, privacy, stage
from ledger.types import LedgerStop

# Between a pre-release tag and the final one, the only paths that may change: the upstream response, the
# stranger's transcript and result, and gate-file lines (GATES).
WINDOW = ("responses/", "proofs/proof-4/")
GATES = "gates/GATES.md"
N = r"(?:0|[1-9]\d*)"  # a version number: no leading zero
FINAL = re.compile(rf"v{N}\.{N}\.{N}")
PRERELEASE = re.compile(rf"v{N}\.{N}\.{N}-rc\.{N}")
PIN = "v0-pin"
# Where publish records each tag it pushes, which no fetch, prune or remote command touches; every tag rule reads
# only these.
PUSHED = "refs/ledger/pushed-tags/"
# The one origin publish pushes to, and the credential helper that hands the token to git for it alone; {} is the
# descriptor of the pipe the token is read from.
ORIGIN = re.compile(r"https://github\.com/[A-Za-z0-9-]+/[A-Za-z0-9._-]+\.git")
HELPER = ("credential.https://github.com.helper="
          "!f() {{ printf 'username=x-access-token\\npassword='; cat /dev/fd/{}; }}; f")
_PR_SET_DUMPABLE = 4


def push(public: Path, tag: str | None, token: str, *, dry_run: bool = False) -> None:
    """Push HEAD to origin's main, and the tag on it, and nothing else: both or neither, and never forced. The tag
    is recorded in PUSHED before the push, so a push that lands is never left unrecorded, and kept even when git
    reports a failure, since the push may have landed: the operator removes a stale record. A dry run records
    and sends nothing, but authenticates. git authenticates with `token`, which only its credential helper reads,
    from a pipe; it never prompts, and its output is reported with the token removed."""
    refs = ["HEAD:refs/heads/main", *([f"HEAD:refs/tags/{tag}"] if tag else [])]
    if tag and not dry_run:
        stage.git(public, "update-ref", PUSHED + tag, "HEAD", "")  # the empty old value: create, never move
    read, write = os.pipe()
    os.write(write, f"{token}\n".encode())
    os.close(write)
    try:
        proc = confine.run([confine.GIT, "-c", HELPER.format(read), "push", *(["--dry-run"] if dry_run else []),
                            "--atomic", "origin", *refs], cwd=public, writes=[public / ".git"], net=True,
                           secret_fd=read, output_max=confine.GIT_OUTPUT_MAX)
    finally:
        os.close(read)
    if proc.exit:
        kept = f"; {PUSHED}{tag} stays recorded until the operator removes it" if tag and not dry_run else ""
        raise LedgerStop(f"push{' --dry-run' if dry_run else ''} refused: "
                         f"{proc.output.strip().replace(token, '[token]')}{kept}")


def _text(path: Path) -> str:
    return path.read_text() if path.exists() else ""


def _forward(public: Path) -> None:
    """Stop unless every pushed tag is in HEAD's history, and the public tree still holds a record of every pair_id
    each one published and its withdrawals with lines only appended: published history is never rewritten, and a
    withdrawn record is marked, never deleted."""
    def pair_ids(text: str) -> set[str]:
        return {json.loads(line)["pair_id"] for line in text.splitlines()}
    for tag in stage.git(public, "for-each-ref", "--format=%(refname:lstrip=3)", PUSHED).output.split():
        ref = PUSHED + tag
        if stage.git(public, "merge-base", "--is-ancestor", ref, "HEAD", ok=(0, 1)).exit:
            raise LedgerStop(f"{tag} is not in HEAD's history: published history is never rewritten")
        published = stage.git(public, "ls-tree", "--name-only", ref, "results/").output.split()
        if "results/records.jsonl" in published and (lost := sorted(
                pair_ids(stage.git(public, "show", f"{ref}:results/records.jsonl").output)
                - pair_ids(_text(public / "results/records.jsonl")))):
            raise LedgerStop(f"{tag} published records the public tree no longer holds: {', '.join(lost)}; a "
                             "withdrawn record is marked, never deleted")
        if "results/withdrawals.jsonl" in published and not _text(public / "results/withdrawals.jsonl").startswith(
                stage.git(public, "show", f"{ref}:results/withdrawals.jsonl").output):
            raise LedgerStop(f"{tag} published results/withdrawals.jsonl, and the public tree's is not it with lines "
                             "appended: withdrawals are append-only")


def withdraw(policy, consts, pair: str, today: date, party_class: str, ground: str) -> str:
    """Withdraw the published record of `pair`, its pair_id or pair_sha256, in one forward commit (see _forward),
    made by staging the development repository `consts.repo` with the withdrawal (stage.stage): the report made
    again with the mark appended to the withdrawals, and a withdrawal gate line naming the pair, the demanding
    party's class and the stated ground, the operator evaluating, both recorded only once everything staging
    checks has passed. Refuses a pair with no published record, or one the published withdrawals hold."""
    public = Path(policy.values["public_tree"])
    _forward(public)
    record = next((r for r in map(json.loads, _text(public / "results/records.jsonl").splitlines())
                   if pair in (r["pair_id"], r["pair_sha256"])), None)
    if record is None:
        raise LedgerStop(f"{pair}: no published record")
    if earlier := next((w for w in map(json.loads, _text(public / stage.WITHDRAWALS).splitlines())
                        if w["pair_sha256"] == record["pair_sha256"]), None):
        raise LedgerStop(f"{record['pair_id']} was withdrawn on {earlier['date']}: a pair is withdrawn once")
    mark = {"pair_sha256": record["pair_sha256"], "date": today.isoformat(), "party_class": party_class,
            "ground": ground}
    stage.stage(policy, consts, dry_run=False, withdrawal=(record["pair_id"], mark))
    return f"withdrew {record['pair_id']} in {stage.git(public, 'rev-parse', 'HEAD').output.strip()}"


def _numbers(tag: str) -> tuple[int, ...]:
    return tuple(map(int, re.findall(r"\d+", tag)))


def _pushing(public: Path, identity: dict) -> list[tuple[str, bytes]]:
    """Every (path, content) the push could send: what the publish commit will hold (privacy.stored), each blob
    of the commits origin lacks as git stores it, every path those commits name, and each one's message as
    `<commit> message`. Stops when one of those commits holds a header but tree, parent, and author and
    committer as `identity` at +0000."""
    files = privacy.stored(public, [(rel, public / rel) for rel in stage.listed(public, public / ".gitignore")])
    person = re.escape(f"{identity['name']} <{identity['email']}>")
    allowed = re.compile(rf"(?:tree|parent) [0-9a-f]+|(?:author|committer) {person} \d+ \+0000".encode())
    unpushed = ("HEAD", "--not", "--remotes=origin")
    objects = [line.partition(" ")[::2] for line in stage.git(public, "rev-list", "--objects", *unpushed)
               .output.splitlines()]  # a commit's line has no path
    stored = stage.git(public, "cat-file", "--batch=%(objecttype) %(objectsize)",
                       input="".join(f"{sha}\n" for sha, _ in objects).encode()).raw
    start = 0
    for sha, rel in objects:  # each object: its type and size, a newline, its bytes, a newline
        head = stored.index(b"\n", start) + 1
        kind, size = stored[start:head].split()
        start = head + int(size) + 1
        data = stored[head:start - 1]
        if kind == b"blob":
            files.append((rel, data))
        elif kind == b"commit":
            headers, _, message = data.partition(b"\n\n")
            if not all(allowed.fullmatch(line) for line in headers.split(b"\n")):
                raise LedgerStop(f"commit {sha}: a header but tree, parent, and the project identity as author "
                                 "and committer")
            files.append((f"{sha} message", message))
    names = stage.git(public, "log", "-z", "-m", "--format=", "--name-only", "--no-renames", *unpushed).output
    return files + [(rel, b"") for rel in names.split("\0") if rel]


def publish(policy, *, tag: str | None, dry_run: bool) -> str:
    """Commit the public tree as the project identity, then push it, with `tag` on its HEAD. Before any commit
    it refuses while the public name or publisher is empty; a tag already pushed, or that is not v<semver>,
    v<semver>-rc.<n> or PIN; a third pre-release tag; a commit to push with any header but tree, parent, and
    the project identity as author and committer at +0000, and anything the privacy sweep or the house sweep
    finds in what the push could send (see _pushing); a first tag that is not PIN, or without recipe/ids.txt matching
    the recipe identifiers computed now; and, while any pre-release tag has no final tag after it, any publish
    but a new pre-release when anything outside WINDOW and GATES changed since the newest such tag, committed
    or not, or the gate file is not that tag's with lines appended; and a pushed tag outside HEAD's history, or a
    published record or withdrawal no longer held (see _forward). Every tag here is one PUSHED records,
    never a local tag. Unless a dry run, it first refuses an origin but one ORIGIN URL, then asks for the push
    token at the terminal, refusing an empty one, and once the checks pass runs an authenticated dry-run push
    before it commits; a dry run makes the same checks, then asks for nothing and commits, tags and sends
    nothing. Neither publish nor any child it starts can dump core once it holds the token."""
    public = Path(policy.values["public_tree"])
    if not dry_run:
        urls = stage.git(public, "config", "--get-all", "remote.origin.url", ok=(0, 1)).output.splitlines()
        if len(urls) != 1 or not ORIGIN.fullmatch(urls[0]):
            raise LedgerStop("origin: publish pushes only to one https://github.com/<org>/<repo>.git URL")
        confine.prctl(_PR_SET_DUMPABLE, 0, 0, 0, 0)
        # Every child inherits it. 1 byte, not 0: a piped core handler (apport here) ignores 0, the kernel's pipe
        # path refuses 1, and no core file fits.
        resource.setrlimit(resource.RLIMIT_CORE, (1, 1))
        if not (token := getpass.getpass("push token for origin: ")):
            raise LedgerStop("the push token is empty")
    published = constants.load(public).published
    if not (published["public_name"] and published["publisher"]):
        raise LedgerStop("public_name or publisher is empty in recipe/constants.toml: nothing is published "
                         "before both exist")
    if tag and not (FINAL.fullmatch(tag) or PRERELEASE.fullmatch(tag) or tag == PIN):
        raise LedgerStop(f"tag {tag!r}: a tag is v<semver>, v<semver>-rc.<n> or the pin's {PIN}")
    tags = stage.git(public, "for-each-ref", "--format=%(refname:lstrip=3)", PUSHED).output.split()
    if tag in tags:
        raise LedgerStop(f"tag {tag} exists: a published tag is never moved")
    prereleases = [t for t in tags if PRERELEASE.fullmatch(t)]
    if tag and PRERELEASE.fullmatch(tag) and len(prereleases) >= 2:
        raise LedgerStop("two pre-release tags exist: the stranger's one re-run is spent")
    _forward(public)
    files = _pushing(public, policy.values["identity"])
    privacy.sweep(files, policy)
    privacy.house(files, policy)
    if tag and not tags and tag != PIN:
        raise LedgerStop(f"the first tag must be {PIN}")
    ids = public / "recipe/ids.txt"
    if tag and not tags and not (ids.is_file() and ids.read_text() == stage.ids(public)):
        raise LedgerStop("the first tag is the pin's: recipe/ids.txt must be present and match the recipe "
                         "identifiers computed now; stage again")
    finals = [_numbers(t) for t in tags if FINAL.fullmatch(t)]
    unfinished = [t for t in prereleases if not any(f >= _numbers(t)[:3] for f in finals)]
    if unfinished and not (tag and PRERELEASE.fullmatch(tag)):
        last = max(unfinished, key=_numbers)
        untracked = stage.git(public, "ls-files", "-z", "--others", f"--exclude-from={public / '.gitignore'}")
        changed = (stage.git(public, "diff", "-z", "--name-only", "--no-renames", PUSHED + last).output
                   + untracked.output).split("\0")
        if outside := [path for path in changed if path and path != GATES and not path.startswith(WINDOW)]:
            raise LedgerStop(f"changed since the pre-release tag {last}: {', '.join(outside)}. Only responses/, "
                             "proofs/proof-4/ and gates/GATES.md may change before the final tag; any other "
                             "change needs a new pre-release tag and the stranger's run again")
        tagged = stage.git(public, "show", f"{PUSHED}{last}:{GATES}").output
        if not (public / GATES).read_text().startswith(tagged):
            raise LedgerStop(f"gates/GATES.md is not the gate file of {last} with lines appended: it is append-only")
    as_tag = f" as {tag}" if tag else ""
    if dry_run:
        return f"dry run: would commit and push{as_tag} to origin; nothing committed, tagged or sent"
    push(public, tag, token, dry_run=True)
    stage.commit(public, policy.values["identity"], "Publish")
    head = stage.git(public, "rev-parse", "HEAD").output.strip()
    push(public, tag, token)
    return f"pushed {head}{as_tag} to origin"
