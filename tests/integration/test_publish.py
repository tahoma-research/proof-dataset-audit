import pytest
from helpers import PY, git, in_unit

pytestmark = pytest.mark.integration

PUBLISH = """
import ctypes, getpass, os, re, secrets, subprocess, sys
from pathlib import Path
from ledger import cli, policy, publish
token, asked, children = secrets.token_hex(16) + "\\c", [], []  # an echo would cut it short
def core():  # this process's core limit as the kernel applies it: soft, hard, unit
    return " ".join(next(line for line in open("/proc/self/limits") if line.startswith("Max core")).split()[4:7])
getpass.getpass = lambda prompt: asked.append(core()) or token  # the operator, typing at the terminal
os.isatty = lambda fd: True
publish.ORIGIN = re.compile("example::origin")  # the stand-in remote, in GitHub's place
class Popen(subprocess.Popen):
    def __init__(self, args, **kwargs):
        children.append((args, kwargs))
        super().__init__(args, **kwargs)
subprocess.Popen = Popen
print("exit", cli.main(["publish", "--operator", "--tag", "v0-pin", "--policy", *sys.argv[1:]]), "asked", len(asked))
print("dumpable", ctypes.CDLL(None).prctl(3, 0, 0, 0, 0))  # PR_GET_DUMPABLE
print("core when asked", asked)
print("in argv or env", any(token in str(part) for args, kwargs in children
                            for part in [*args, *(kwargs.get("env") or {}).values()]))
print("piped to", [" ".join(args[args.index("push"):]) for args, kwargs in children if kwargs.get("pass_fds")])
pol = policy.load(sys.argv[1])
trees = (pol.path.parent, pol.root, Path(pol.values["public_tree"]))  # the root holds runs/; the tree, its .git
print("in a file", any(token.encode() in path.read_bytes() for tree in trees for path in tree.rglob("*")
                       if path.is_file()))
"""


def test_push_token_only_on_the_push_childs_pipe(staged, stage_policy, tmp_path):
    """publish asks for the push token at the operator's terminal, and a dry run asks for nothing. The token
    reaches only the authenticated dry-run push, which runs before anything is committed or recorded, on a
    pipe its credential helper reads: that helper answers for https://github.com alone, as x-access-token, and
    git's own https helper asks it as the stand-in remote helper here does. The token is in no environment, on
    no command line, in no file and, scrubbed, in no output or run report. publish and the helper, each while it
    holds the token, have a core limit of 1 byte, soft and hard, which a piped core handler cannot ignore."""
    (bin := tmp_path / "bin").mkdir()
    (helper := bin / "git-remote-example").write_text(
        "#!/bin/sh\nprintf 'protocol=https\\nhost=example.invalid\\n\\n' | git credential fill >&2\n"
        "filled=$(printf 'protocol=https\\nhost=github.com\\n\\n' | git credential fill)\n"
        "printf '%s\\n' \"$filled\" >&2\n"
        "awk '/^Max core/ { print \"core\", $5, $6, $7 }' /proc/$$/limits >&2\nexit 1\n")
    helper.chmod(0o755)
    git("-C", staged, "remote", "add", "origin", "example::origin")
    (staged / "responses").mkdir()
    (staged / "responses/2026-12-01-upstream.md").write_text("received\n")  # a commit would move HEAD
    head = git("-C", staged, "rev-parse", "HEAD")
    dry, run = (in_unit(PY, "-c", PUBLISH, stage_policy.path, *dry_run, env={"PATH": f"{bin}:/usr/bin:/bin"},
                        flags=["--property=LimitCORE=infinity"])  # a terminal's ulimit -c may be raised
                for dry_run in (["--dry-run"], []))
    assert dry.out.splitlines() == [
        "dry run: would commit and push as v0-pin to origin; nothing committed, tagged or sent", "exit 0 asked 0",
        "dumpable 1", "core when asked []", "in argv or env False", "piped to []", "in a file False"], dry.out + dry.err
    assert run.out.splitlines() == [
        "exit 2 asked 1", "dumpable 0", "core when asked ['1 1 bytes']", "in argv or env False",
        "piped to ['push --dry-run --atomic origin HEAD:refs/heads/main HEAD:refs/tags/v0-pin']",
        "in a file False"], run.out + run.err
    report = max((stage_policy.root / "runs").glob("*/report.md")).read_text()
    for text in (run.err, report):
        assert "could not read Username for 'https://example.invalid'" in text, text
        assert "username=x-access-token\npassword=[token]\ncore 1 1 bytes" in text, text
    assert git("-C", staged, "rev-parse", "HEAD") == head and not git("-C", staged, "for-each-ref", "refs/ledger/")
