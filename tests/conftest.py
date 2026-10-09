import hashlib
import ipaddress
import json
import platform
import re
import shutil
import subprocess
import uuid
from datetime import date

import pytest
from helpers import REPO, FakeLean, built, write_policy

from ledger import aggregate, confine, constants, envbuild, frame, gatefile, ingest, legs, policy, preflight, stage

CONSTS = constants.load(REPO)
RUN = confine.run  # legs_run puts a FakeLean in its place
SUFFIX = CONSTS.published["assembly"]["suffix_regex"]

# Files a development repository may hold beyond the real code, tests, templates and recipe: some the
# allowlist takes in, some it must leave out. Each holds its own path, so no two have the same digest.
EXTRAS = ("src/ledger/__pycache__/cli.cpython-312.pyc", "lean/audit-pin/Main.lean",
          "lean/audit-pin/.lake/build/Main.olean",
          "fixtures/assembler/a.lean", "fixtures/toy/t.lean", "fixtures/other/o.lean", "fixtures/planted/p.lean",
          "fixtures/proof1b/q.lean", "recipe/notes.txt", "docs/d.md", "ops/o.toml", "CLAUDE.md")


@pytest.fixture
def root(tmp_path):
    (path := tmp_path / "root").mkdir()
    return path


@pytest.fixture
def published():
    """The published constants, the pinned Python replaced by this one."""
    sampling = CONSTS.published["sampling"] | {"python": platform.python_version()}
    return CONSTS.published | {"sampling": sampling}


@pytest.fixture
def build_frame(tmp_path):
    """Build the frame of a release made of `records`, in order; its `work` directory is tmp_path/work."""
    def build(*records):
        release = tmp_path / "release.json"
        release.write_text(json.dumps(list(records)), encoding="utf-8")
        ingest.write(ingest.parse(release, SUFFIX), tmp_path / "work")
        return frame.build(tmp_path / "work" / "entries.jsonl", CONSTS)
    return build


@pytest.fixture
def make_policy(tmp_path, root):
    """Write an operator policy over `root`; keyword arguments override its values."""
    return lambda **overrides: write_policy(tmp_path / "operator.toml", root, **overrides)


@pytest.fixture
def code_repo(tmp_path):
    """A git repository holding a committed copy of the recipe, its memory floors and scope caps set to zero so that
    a test raises them on the loaded constants."""
    repo = tmp_path / "code"
    shutil.copytree(REPO / "recipe", repo / "recipe")
    path = repo / "recipe/constants.toml"
    text = path.read_text()
    for line in ("memory_floor_gib = 8", "swap_floor_gib = 4", "leg_memory_max_mb = 12288",
                 "agg_memory_max_mb = 24576"):
        assert line in text
        text = text.replace(line, line.split("= ")[0] + "= 0")
    path.write_text(text)
    git = ["git", "-C", repo, "-c", "user.name=test", "-c", "user.email=test@example.invalid"]
    for args in (["init", "-q"], ["add", "."], ["commit", "-qm", "recipe"]):
        subprocess.run([*git, *args], check=True)
    return repo


@pytest.fixture
def ready(make_policy, code_repo):
    """A loaded policy whose run lock this process holds, and the committed constants."""
    def make(**overrides):
        pol = policy.load(make_policy(**overrides))
        assert preflight.lock(pol.root) is None
        return pol, constants.load(code_repo)
    return make


@pytest.fixture
def dev_repo(tmp_path):
    """A development repository: the real code, tests, templates and recipe, the project named, and EXTRAS."""
    dev = tmp_path / "dev"
    for rel in ("src", "tests", "templates", "recipe"):
        shutil.copytree(REPO / rel, dev / rel)
    shutil.copy(REPO / "pyproject.toml", dev)
    for rel in EXTRAS:
        (dev / rel).parent.mkdir(parents=True, exist_ok=True)
        (dev / rel).write_text(f"{rel}\n")
    path = dev / "recipe/constants.toml"
    path.write_text(re.sub(r'^public_name = "[^"]*"', 'public_name = "Example Ledger"',
                           re.sub(r'^publisher = "[^"]*"', 'publisher = "Example Organisation"', path.read_text(), flags=re.M),
                           flags=re.M))
    return dev


@pytest.fixture
def stage_policy(make_policy, root, tmp_path):
    """An operator policy to stage under, whose denylist term, scrub entry and host address appear in no
    staged file, and which lists the package name as a scrub term too, with the bootstrap gate file opened by
    the approval line. Its house sweep, a stand-in, finds something only in a house-finding.md."""
    token = uuid.uuid4()
    (denylist := tmp_path / "denylist.txt").write_text(f"# one term\n{token.hex}\n")
    (house := tmp_path / "house-sweep.py").write_text(
        'import sys\nfrom pathlib import Path\n'
        'sys.exit(any(Path(sys.argv[sys.argv.index("--path") + 1]).rglob("house-finding.md")))\n')
    pol = policy.load(make_policy(privacy_denylist=str(denylist), scrub=[f"volume-{token.hex[:12]}", "Ledger"],
                                  host_addresses=[str(ipaddress.IPv6Address(token.int))], house_sweep=str(house)))
    gatefile.append(pol, "prd-approved", "recorded", "operator", "approval date", date(2026, 10, 2))
    return pol


@pytest.fixture
def staged(dev_repo, stage_policy, root):
    """The development repository staged once, and committed, into the policy's public tree."""
    stage.stage(stage_policy, constants.load(dev_repo), dry_run=False)
    return root / "public"


@pytest.fixture
def legs_run(root, make_policy, monkeypatch):
    """Build a run of legs over `n` assembled pairs, in a root whose pin and legacy trees have passed build
    reports; every process the legs start is answered by the returned FakeLean. Returns (run, pairs, lean);
    keyword arguments replace published constants' tables."""
    lean = FakeLean()
    monkeypatch.setattr(confine, "run", lean)

    def make(n: int, envs=("pin", "legacy"), **published):
        seeded = published.get("status", {}).get("stop_loss", False)
        for tree, env, out in (("pin-seeded" if seeded else "pin", "pin", ".lake/build/lib/lean"),
                               ("legacy", "legacy", ".lake/build/lib")):
            name = (REPO / "recipe" / env / "lean-toolchain").read_text().strip()
            toolchain = root / "elan/toolchains" / name.replace("/", "--").replace(":", "---")
            (toolchain / "bin").mkdir(parents=True, exist_ok=True)
            (toolchain / "bin/lean").write_text(name)
            envbuild.record_toolchain(root, toolchain)
            packages = root / "env" / tree / ".lake/packages/mathlib"
            packages.mkdir(parents=True, exist_ok=True)
            (packages / "Mathlib.olean").write_text(f"{tree} as built")
            audit = root / "env" / f"audit-{env}" / envbuild.AUDIT_BIN
            audit.parent.mkdir(parents=True, exist_ok=True)
            audit.write_text(f"ledger-audit {env}")
            report = {"artifact_set_digest": envbuild.artifact_set_digest(root / "env" / tree, toolchain),
                      "lean_path_root": out, "audit_digest": "sha256:" + hashlib.sha256(audit.read_bytes()).hexdigest()}
            (root / "measure" / f"build-{tree}.json").write_text(json.dumps(report))
        work = root / "work"
        (work / "pairs").mkdir(parents=True, exist_ok=True)
        (root / "tmp/r").mkdir(parents=True, exist_ok=True)
        monkeypatch.setenv("TMPDIR", str(root / "tmp/r"))
        (work / "sample.json").write_text("{}")
        consts = constants.Constants(CONSTS.repo, CONSTS.source, CONSTS.published | {
            table: CONSTS.published[table] | values for table, values in published.items()}, CONSTS.env)
        pairs = [{"i": i, "pair_id": f"p{i}__p0", "pair_sha256": f"sha256:{i:064x}", "refusal": None} for i in range(n)]
        for pair in pairs:
            (work / "pairs" / f"{pair['pair_id']}.lean").write_text(
                consts.published["assembly"]["header"] + "theorem t : True := by\n  trivial\n")
        run = legs.prepare(policy.load(make_policy()), consts, work, root / "results", root / "runs/r/logs", envs)
        return run, pairs, lean
    return make


@pytest.fixture
def leg_results(legs_run):
    """Run, pair by pair, the legs of a draw of `cases`: each case maps an environment to the FakeLean answers of
    its leg, or to None for a leg killed on every attempt, and may name the pair's assembly "refusal"; keyword
    arguments replace published constants' tables. Returns the run, and the draw's sample and assembled lines."""
    def make(cases: list[dict], **published):
        run, pairs, lean = legs_run(len(cases), **published)
        draw = []
        for pair, case in zip(pairs, cases):
            pair |= {"refusal": case.get("refusal"), "element_sha256": f"sha256:{pair['i'] + 100:064x}"}
            for env in ("pin", "legacy"):
                if env in case:
                    while case[env] is None and run.progress.attempts(pair["pair_sha256"], env) < run.consts.published[
                            "limits"]["attempt_bound"]:
                        run.progress.start_attempt(pair["pair_sha256"], env)
                    lean.answers = dict(case[env] or {})
                    legs.run_leg(run, pair, env)
            draw.append({"i": pair["i"], "pair_id": pair["pair_id"], "decl": pair["pair_id"].removesuffix("__p0"),
                         "k": 0, "position": pair["i"], "split": "lean_workbook",
                         "element_sha256": pair["element_sha256"]})
        return run, {"draw": draw}, pairs
    return make


@pytest.fixture
def snapshot(leg_results, dev_repo, stage_policy, root, monkeypatch):
    """The development repository, with its classifier table, staged with the results of helpers.built, the
    aggregate's replay returned and its membership the records' members. Returns the public tree and the records."""
    found, run = built(leg_results)
    run.progress.data["sample_sha256"] = "sha256:" + hashlib.sha256((run.work / "sample.json").read_bytes()).hexdigest()
    run.progress.data["aggregate"]["last_replay"] = {"wall_s": 5400.0, "exit": 0, "rejected_constant": None}
    run.progress.save()
    aggregate.write_membership(run.results, [r["pair_id"] for r in found if r["aggregate"]["member"]])
    shutil.copytree(REPO / "classifier", dev_repo / "classifier")
    monkeypatch.setattr(confine, "run", RUN)
    stage.stage(stage_policy, constants.load(dev_repo), dry_run=False)
    return root / "public", found
