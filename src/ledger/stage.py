"""Staging: the allowlisted code copied from the development repository into the public tree with the results
the report makes, swept for anything personal or private, and committed there locally as the project identity.
Nothing here pushes."""

import hashlib
import ipaddress
import json
import os
import re
import shutil
import tempfile
import time
import unicodedata
import urllib.parse
from dataclasses import dataclass
from datetime import date
from pathlib import Path, PurePosixPath

from ledger import assemble, confine, constants, devoverlay, fixtures, gatefile, ingest, privacy, records, report
from ledger.types import LedgerStop, canonical, write_atomic

# Copied when present in the development repository; nothing else ever is.
ALLOWLIST = ("src/ledger", "lean", "tests", "templates", "pyproject.toml", "requirements-dev.txt",
             "recipe/source.toml", "recipe/pin", "recipe/legacy", "recipe/pin-seeded", "recipe/policy",
             "recipe/Containerfile", "recipe/stranger.sh", "fixtures/assembler", "fixtures/toy")
# Copied too, until one of the gate lines that record a change to it exists; the public copy is then its only home.
GUARDED = {"recipe/constants.toml": {"d7-sample", "d14-outcome", "stop-loss", "legacy-status", "limit-freeze",
                                     "rescope"},
           "classifier/table-v1.toml": {"classifier-freeze"}}
PLANTED = ("fixtures/planted", "fixtures/proof1b")  # honesty-proof sources: beside the public tree, never in it
ROOT_FILES = ("LICENSE", "CITATION.cff.tmpl", "CONTRIBUTING.md.tmpl", "RULES.md.tmpl", "README.md.tmpl")
# The public paths staging replaces whole, besides the allowlist; results and the gate file are not among them.
RENDERED = (*(name.removesuffix(".tmpl") for name in ROOT_FILES), ".gitignore", "recipe/ids.txt")
IGNORED = shutil.ignore_patterns("__pycache__", "*.pyc", ".lake")  # compiled output carries host paths
PLACEHOLDER = "dev-placeholder"  # an empty public name or publisher under the development overlay
DEV_SNAPSHOT = " — DEV SNAPSHOT — NOT EVIDENCE"  # after the public name under the development overlay
WITHDRAWALS = "results/withdrawals.jsonl"  # append-only: the root's is the published one with lines appended
TRANSCRIPT = "proofs/proof-4/transcript.md"  # the stranger's, committed scrubbed
SLIRP = ipaddress.ip_network("10.0.2.0/24")  # slirp4netns's network inside the stranger's container: no house host


def names(policy, consts) -> dict[str, str]:
    """The public name and the publisher from the constants. Under the development overlay an empty one is
    PLACEHOLDER, and the public name carries DEV_SNAPSHOT, so no page that names it reads as evidence."""
    named = {key: consts.published[key] for key in ("public_name", "publisher")}
    if devoverlay.load(policy):
        named = {key: value or PLACEHOLDER for key, value in named.items()}
        named["public_name"] += DEV_SNAPSHOT
    return named


def git(tree: Path, *args: str, ok: tuple[int, ...] = (0,), input: bytes | None = None) -> confine.Proc:
    """Run git in `tree`, writing only its .git and retrying briefly while another git call holds its index.lock;
    stop on an exit status outside `ok`, or on output past confine.GIT_OUTPUT_MAX, since publish sweeps it."""
    for wait in (0.5, 1, 2, None):
        proc = confine.run([confine.GIT, *args], cwd=tree, writes=[tree / ".git"], input=input,
                           output_max=confine.GIT_OUTPUT_MAX)
        if wait is None or proc.exit in ok or "index.lock': File exists" not in proc.output:
            break
        time.sleep(wait)
    if proc.exit not in ok:
        raise LedgerStop(f"git exited {proc.exit}: {proc.output.strip()}")
    if proc.output_truncated:  # read from a prefix, publish's sweep would pass the rest unseen
        raise LedgerStop(f"git {args[0]}: its output passed {confine.GIT_OUTPUT_MAX} bytes")
    return proc


def listed(tree: Path, ignore: Path) -> list[str]:
    """Every path `git add -A` would commit in `tree` with `ignore` as its .gitignore: each tracked path still
    present and each untracked one the file does not ignore. Outside a repository, every file."""
    if not (tree / ".git").exists():
        return [p.relative_to(tree).as_posix() for p in tree.rglob("*") if p.is_file()]
    paths = git(tree, "ls-files", "-z", "--cached", "--others", f"--exclude-from={ignore}").output.split("\0")
    if any("\ufffd" in rel for rel in paths):
        raise LedgerStop(f"{tree} holds a path name that is not UTF-8, which the privacy sweep cannot read")
    return [rel for rel in paths if rel and os.path.lexists(tree / rel)]


def commit(tree: Path, identity: dict, message: str, paths: tuple[str, ...] = (".",)) -> bool:
    """Commit every change under `paths` in the tree as the project identity, if there is any; no global or
    system git config is read. Returns whether a commit was made."""
    git(tree, "add", "-A", "--", *paths)
    if git(tree, "diff", "--cached", "--quiet", "--", *paths, ok=(0, 1)).exit == 0:
        return False
    git(tree, "-c", f"user.name={identity['name']}", "-c", f"user.email={identity['email']}", "commit", "-q",
        "-m", message, "--", *paths)
    return True


def ids(tree: Path) -> str:
    """recipe/ids.txt: the recipe identifier of each environment whose audit sources are in the tree."""
    return "".join(f"recipe_{env}={constants.recipe_id(tree, env)}\n" for env in ("pin", "legacy")
                   if (tree / f"lean/audit-{env}").is_dir())


def planted(dev: Path, assembly: dict, overlay) -> set[bytes]:
    """The pair digest, as hex, of each honesty-proof entry of fixtures/planted/ and fixtures/proof1b/, assembled or
    refused, under every header a fixture run uses: the recipe's, the development overlay's and the proof-1b
    project's own."""
    headers = {assembly["header"], fixtures.HEADER, *([overlay.header] if overlay else [])}
    found = set()
    for rel in PLANTED:
        for path in (dev / rel).glob("entries.json"):
            for entry in ingest.parse(path, assembly["suffix_regex"]):
                for k, element in enumerate(entry.element_sha256):
                    row = {"i": 0, "k": k, "element_sha256": element,
                           "pair_id": assembly["name_mangle"].format(decl=entry.decl, k=k)}
                    for header in headers:
                        made = assemble.assemble_pair(row, entry, assembly | {"header": header})
                        found.add(made.pair_sha256.removeprefix("sha256:").encode())
    return found


def scrub_transcript(text: str, policy) -> str:
    """The stranger's transcript with everything the privacy sweep refuses in any file withheld (privacy.refused), and
    each address in a network of privacy.own or not globally routed, the house's own numbering (its gateway, LAN and
    tailnet), but those of SLIRP and privacy.PUBLISHABLE, in whatever form it is written, with the whole run of
    privacy.ADDRESS_LIKE it is in; every other address stays.
    The sweep then reads it again with each line joined to the next, NFKC-normalised and percent-decoded, and stops on
    what that finds, naming the lines: a name, address or path split, encoded or in another form of its letters."""
    nets, kept = privacy.own(policy), [SLIRP, *privacy.PUBLISHABLE]

    def withheld(token: str) -> bool:
        return privacy.covered(token, nets) or any(not address.is_global and not any(address in net for net in kept)
                                                   for address in privacy.addresses(token))
    scrubbed = privacy.ADDRESS_LIKE.sub(lambda m: gatefile.WITHHELD if withheld(m[0]) else m[0],
                                        privacy.refused(policy).sub(gatefile.WITHHELD, text))
    lines = [unicodedata.normalize("NFKC", urllib.parse.unquote(line)) for line in scrubbed.splitlines()]
    joined = "\n".join(line + after for line, after in zip(lines, [*lines[1:], ""]))
    privacy.sweep([(TRANSCRIPT, scrubbed.encode()), (f"{TRANSCRIPT}, each line joined to the next", joined.encode())],
                  policy)
    return scrubbed


def results(policy, consts, scratch: Path, withdrawal: tuple[str, dict] | None) -> str | None:
    """Once there are leg results or a `withdrawal`, the results under `scratch`/results/ and their README in
    `scratch`: the report run with the root's withdrawals, which must be the published ones with lines appended,
    and the withdrawal's mark, and the root's membership and progress, the membership checked against the records.
    While a drawn pair has no record yet, nothing goes under results/, the published README is kept, and the reason
    is returned; a withdrawal stops instead."""
    root, public = policy.root, Path(policy.values["public_tree"])
    if withdrawal is None and not (root / "results/progress.json").exists():
        return None
    published, marks = ((tree / WITHDRAWALS).read_bytes() if (tree / WITHDRAWALS).exists() else b""
                        for tree in (public, root))
    if not marks.startswith(published):
        raise LedgerStop(f"{WITHDRAWALS}: the root's is not the published one with lines appended; a withdrawal is "
                         "never undone")
    marks += canonical(withdrawal[1]) if withdrawal else b""
    (scratch / "results").mkdir()
    if marks:
        (scratch / WITHDRAWALS).write_bytes(marks)
    try:
        report.run(policy, consts, scratch / "results")
    except records.Pending as stop:
        if withdrawal:
            raise
        shutil.rmtree(scratch / "results")
        if (public / "results").is_dir():
            shutil.copy2(public / "README.md", scratch / "README.md")
        return str(stop)
    for name in ("membership.txt", "progress.json"):
        if (path := root / "results" / name).exists():
            shutil.copy2(path, scratch / "results" / name)
    (scratch / "results/README.md").replace(scratch / "README.md")
    recs = [json.loads(line) for line in (scratch / "results/records.jsonl").read_text().splitlines()]
    members = [r["pair_id"] for r in recs if r["aggregate"]["member"]]
    if (membership := scratch / "results/membership.txt").exists() and (
            built := membership.read_text().splitlines()[1:]) != members:
        raise LedgerStop("results/membership.txt is not the records' aggregate members in draw order; listed beyond "
                         f"them: {', '.join(sorted(set(built) - set(members))) or 'none'}; not listed: "
                         f"{', '.join(sorted(set(members) - set(built))) or 'none'}")
    return None


def _remove(path: Path) -> None:
    if path.is_dir() and not path.is_symlink():
        shutil.rmtree(path)
    else:
        path.unlink(missing_ok=True)


@dataclass(frozen=True)
class StageReport:
    skipped: list[str]  # allowlisted paths absent from the development repository
    held: list[str]  # GUARDED paths a gate line records a change to, taken from the public tree, their only home
    committed: bool
    late: str | None  # why the results were not staged: a drawn pair with no record yet


def stage(policy, consts, *, dry_run: bool, withdrawal: tuple[str, dict] | None = None) -> StageReport:
    """Stage the development repository `consts.repo` into the public tree: the allowlisted code, the root files
    rendered with the public name and publisher, the recipe identifiers, the results (see `results`) with the mark
    of `withdrawal`, (pair_id, mark), if one is given, the stranger's transcript scrubbed (scrub_transcript), and
    on the first stage the gate file carried from its bootstrap copy. A GUARDED path is taken from the public tree
    once a gate line records a change to it: the public copy is then its only home. Everything is assembled and
    checked in a scratch directory before anything is written, the planted entries (see `planted`) and the privacy
    and house sweeps among the checks; a dry run stops there. Otherwise a withdrawal's gate line and mark are
    recorded, the planted fixture sources go beside the tree, and the result is committed as the project
    identity."""
    dev, root, public = consts.repo, policy.root, Path(policy.values["public_tree"])
    named = names(policy, consts)
    if empty := [key for key, value in named.items() if not value]:
        raise LedgerStop(f"{' and '.join(empty)} empty in recipe/constants.toml: nothing is staged before the "
                         "project's public name and publisher exist")
    recorded = {row[1] for row in gatefile.rows(policy)}
    held = [rel for rel, gates in GUARDED.items() if gates & recorded]
    copied, overlay = ALLOWLIST + tuple(GUARDED), devoverlay.load(policy)
    (root / "tmp").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=root / "tmp") as scratch:
        scratch = Path(scratch)
        skipped = []
        for rel in copied:
            source = (public if rel in held else dev) / rel
            if not source.exists():
                skipped.append(rel)
            elif source.is_dir():
                shutil.copytree(source, scratch / rel, ignore=IGNORED)
            else:
                (scratch / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, scratch / rel)
        for name in ROOT_FILES:
            text = (dev / "templates" / name).read_text()
            text = text.replace("{public_name}", named["public_name"]).replace("{publisher}", named["publisher"])
            if found := re.findall(r"\{\w+\}", text):
                raise LedgerStop(f"{name.removesuffix('.tmpl')}: unrendered {', '.join(found)}")
            (scratch / name.removesuffix(".tmpl")).write_text(text)
        (scratch / ".gitignore").write_text("results/legs/\n__pycache__/\n")
        if recipe_ids := ids(scratch):
            (scratch / "recipe/ids.txt").write_text(recipe_ids)
        staged = constants.load(scratch)
        late = results(policy, staged, scratch, withdrawal)
        reported = (scratch / "results").is_dir()
        if scrubbed := (public / TRANSCRIPT).exists():
            try:
                text = (public / TRANSCRIPT).read_bytes().decode()
            except UnicodeDecodeError:
                raise LedgerStop(f"{TRANSCRIPT}: not UTF-8") from None
            (scratch / TRANSCRIPT).parent.mkdir(parents=True)
            (scratch / TRANSCRIPT).write_bytes(scrub_transcript(text, policy).encode())
        if not (public / "gates/GATES.md").exists():
            rows = gatefile.rows(policy)
            if not rows or rows[0][1] != "prd-approved" or any(len(row) != 5 or gatefile.problem(*row[1:])
                                                               for row in rows):
                raise LedgerStop("the bootstrap gate file must open with the prd-approved line, and every line in "
                                 "it must keep the gate-file rules")
            (scratch / "gates").mkdir()
            shutil.copy2(root / "gates/GATES.md", scratch / "gates/GATES.md")
        owned = copied + RENDERED + (("results",) if reported else ()) + ((TRANSCRIPT,) if scrubbed else ())
        files = [(p.relative_to(scratch).as_posix(), p) for p in scratch.rglob("*") if p.is_file()]
        files += [(rel, public / rel) for rel in listed(public, scratch / ".gitignore")
                  if not any(PurePosixPath(rel).is_relative_to(path) for path in owned)]
        files = privacy.stored(public, files)
        whole = {hashlib.sha256(p.read_bytes()).digest() for rel in PLANTED for p in (dev / rel).rglob("*")
                 if p.is_file()}
        pairs = planted(dev, staged.published["assembly"], overlay)
        if found := sorted(rel for rel, data in files
                           if hashlib.sha256(data).digest() in whole or any(pair in data for pair in pairs)):
            raise LedgerStop(f"planted fixture entries would be published: {', '.join(found)}")
        privacy.sweep(files, policy, dev=overlay is not None)
        privacy.house(files, policy)
        if dry_run:
            return StageReport(skipped, held, False, late)
        if withdrawal:
            pair_id, mark = withdrawal
            gatefile.append(policy, "withdrawal", "withdrawn", "operator",
                            f"pair={pair_id}; party_class={mark['party_class']}; ground={mark['ground']}",
                            date.fromisoformat(mark["date"]))
            write_atomic(root / WITHDRAWALS, (scratch / WITHDRAWALS).read_bytes())
        for rel in PLANTED:
            _remove(target := root / "fixtures-src" / Path(rel).name)
            if (dev / rel).is_dir():
                shutil.copytree(dev / rel, target)
        if not (public / ".git").exists():
            (public / ".git").mkdir(parents=True)
            git(public, "init", "-q", "--initial-branch=main")
        for rel in owned:
            _remove(public / rel)
        shutil.copytree(scratch, public, dirs_exist_ok=True)
    message = f"Withdraw {withdrawal[0]}" if withdrawal else "Stage the published code, recipe and templates"
    return StageReport(skipped, held, commit(public, policy.values["identity"], message), late)
