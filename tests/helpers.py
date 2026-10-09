"""Test helpers: policy files, a process holding the run lock, and transient systemd user units."""

import contextlib
import hashlib
import json
import os
import subprocess
from pathlib import Path
from types import SimpleNamespace

from ledger import classify, confine, constants, envbuild, records, report
from ledger.types import canonical

REPO = Path(__file__).resolve().parents[1]
SRC = REPO / "src"
PY = "/usr/bin/python3"
ENV = {**os.environ, "PYTHONPATH": str(SRC), "PYTHONDONTWRITEBYTECODE": "1"}
CONSTS = constants.load(REPO)
COMMIT = "312cbaea23f85a932d4dcb774493ecf1e0200aab"  # what a FakeLean answers `git rev-parse HEAD` with
NAMES = {"public_name": "Example Audit", "publisher": "Example Organisation"}
FRAME = {"schema": "frame/1", "entries_sha256": "sha256:" + "0" * 64, "records_total": 140214,
         "split_counts": {"lean_workbook": 57321, "lean_workbook_plus": 82893}, "card_count_lean_workbook": 57231,
         "reconciliation": "counted split values sum to records_total: true", "proofless_excluded": 127391,
         "proof_bearing": 12823, "proof_elements_raw": 223156, "within_entry_exact_duplicates_removed": 0,
         "cross_entry_duplicates_removed": 3416, "eligible_entries": 9407, "drawable_pairs_before_cross_dedupe": 24747,
         "drawable_pairs": 18026,
         "multiplier": {"mean": 17.4, "median": 16, "max": 64, "max_entry": "lean_workbook_698"},
         "refused": {}, "eligible": []}
PIN_OF = {"reproduced": "accepted", "rejected-by-checker": "kernel-reject", "axiom-audit-failure": "audit-failure",
          "rejected-by-replay": "replay-reject", "environment-mismatch": "kernel-reject",
          "environment-undeclared": "elab-error", "timed-out": "timeout-wall-clock", "resource-exhausted": "oom",
          "harness-error": "harness", "unclassified": "unclassified"}
LEGACY_OF = {"rejected-by-checker": "kernel-reject", "axiom-audit-failure": "elab-error",
             "environment-undeclared": "timeout-wall-clock"}
REPORT_PAIRS = [(0, "reproduced"), (0, "rejected-by-checker"), (1, "axiom-audit-failure"), (2, "rejected-by-replay"),
                (3, "environment-mismatch", "kernel-reject", "accepted"), (4, "environment-undeclared"),
                (5, "timed-out"), (6, "resource-exhausted"), (7, "harness-error"), (8, "unclassified"),
                (9, "reproduced")]
PIN_ONLY_PAIRS = [(0, "reproduced"), (0, "environment-undeclared"), (1, "rejected-by-replay"),
                  (2, "environment-undeclared", "kernel-reject", None), (3, "timed-out"), (4, "harness-error")]
MEASURES = {"gates": [], "table_sha256": "sha256:" + "c" * 64, "sample_sha256": "sha256:" + "d" * 64,
            "membership": None, "replay_s": None, "rebuild": [], "pin_build": None, "legacy_build": None,
            "legacy_attempts": [], "projection": None}
REPLAYED = {"replay": {"source": "d44", "constant": "c", "date": "2026-12-01", "at": "2026-12-01T03:00:00Z"}}
HARNESS = {"harness": {"source": "crosspass-d44", "detail": "d", "date": "2026-12-01", "at": "2026-12-01T03:00:00Z"}}
KERNEL = ("Pairs/p1__p0.lean:6:0: error: (kernel) declaration type mismatch, 'p1__p0' has type\n  True\nbut it is "
          "expected to have type\n  False\n")
PROPEXT = {"name": "propext", "module": "Init.Core", "via_own": False}
AUDITED = {"output": json.dumps({"name": "p0__p0", "axioms_collector": [PROPEXT], "axioms_walk": [PROPEXT],
                                 "type_hash": "7", "type_pp": "True", "collector_us": 1, "walk_us": 2}) + "\n"}
CASES = [{"pin": {"compile": {"output_truncated": True}, "audit": AUDITED}, "legacy": {}},
         {"pin": {"compile": {"exit": 1, "output": KERNEL}}, "legacy": {}},
         {"refusal": "unsafe-name", "pin": {}, "legacy": {}}, {"pin": None, "legacy": {}}, {"pin": {}, "legacy": {}},
         {"pin": {"compile": {"exit": 1, "output": KERNEL}}, "legacy": {"compile": {"exit": 1, "output": KERNEL}}},
         {"pin": {"audit": {"output": "{\n"}}, "legacy": {}}]
REPLAY = {"source": "d44", "constant": "p4__p0", "date": "2026-12-01", "at": "2026-12-01T03:00:00Z"}
WITHDRAWN = {"date": "2026-12-20", "party_class": "upstream author", "ground": "licence"}
# `ledger <argv[2:]>` with the recipe and constants taken from the repository argv[1] names.
CLI = ("import sys; from pathlib import Path; from ledger import cli; cli.REPO = Path(sys.argv[1]); "
       "sys.exit(cli.main(sys.argv[2:]))")


def built(leg_results, replay=REPLAY, none=(), **published) -> list[dict]:
    """The records of CASES: the fifth pair rejected by `replay`, the aggregate replay having returned, the
    first withdrawn, and the pairs indexed by `none` declared none; the frame, the draw from it and its assembled
    lines also on disk. The seventh pair's audit line is not JSON, so its pin leg is harness with no row, the error
    its diagnostic."""
    run, sample, pairs = leg_results(CASES, **published)
    (run.work / "frame.json").write_text(json.dumps(FRAME))
    frame_sha256 = "sha256:" + hashlib.sha256((run.work / "frame.json").read_bytes()).hexdigest()
    sample |= {"seed": 0, "frame_sha256": frame_sha256}
    (run.work / "sample.json").write_text(json.dumps(sample))
    (run.work / "assembled.jsonl").write_bytes(b"".join(map(canonical, pairs)))
    run.progress.data |= {"replay_overrides": {pairs[4]["pair_sha256"]: replay},
                          "declared_none": [pairs[n]["pair_sha256"] for n in none],
                          "aggregate": {"state": "replay-returned"}}
    (run.results / "withdrawals.jsonl").write_bytes(canonical({"pair_sha256": pairs[0]["pair_sha256"]} | WITHDRAWN))
    return records.build(sample, pairs, run.progress, run.results, run.table, run.consts), run


def record(name: str, n: int = 1, statement: str = "True", split: str = "lean_workbook") -> dict:
    """A release record declaring `name`, with `n` distinct proof elements (none when n is 0)."""
    return {"formal_statement": f"theorem {name} : {statement} :=  by sorry", "split": split,
            "proof": [f"proof {i}" for i in range(n)]}


def summary_of(pairs: list, rows=(), measures=None, disagree=(), **published) -> dict:
    """The summary of records in draw order, one per pair of `pairs`: (entry, class), or (entry, class, pin outcome,
    legacy outcome, overrides); a pair's k counts its entry's earlier pairs, and its legs hold only their outcomes.
    The legacy leg is absent where the published status (each keyword a published table's values) says the legacy
    environment is unavailable. `rows` are the gate file's, `measures` replace MEASURES's; the pairs at the
    indices in `disagree` have an audit disagreement at the declared revision."""
    pin_only = published.get("status", {}).get("legacy") == "environment-unavailable"
    recs, draw = [], []
    for i, (entry, cls, *given) in enumerate(pairs):
        pin, legacy, overrides = (*given, {})[:3] if given else (PIN_OF[cls], LEGACY_OF.get(cls, "accepted"), {})
        legacy = None if pin_only else legacy
        draw.append(row := {"i": i, "pair_id": f"e{entry}__p{sum(r['position'] == entry for r in draw)}",
                            "decl": f"e{entry}", "k": sum(r["position"] == entry for r in draw), "position": entry,
                            "split": "lean_workbook", "element_sha256": f"sha256:{i:064x}"})
        overrides = {"replay": None, "harness": None} | overrides
        recs.append(row | {
            "pair_sha256": f"sha256:{i + 4096:064x}", "class": cls, "provenance": "from-source", "withdrawn": None,
            "skew_case": legacy and classify.skew_case(pin, legacy, overrides["replay"], overrides["harness"]),
            "mismatch_kernel_rejection": classify.is_mismatch_kernel(cls, "any.kernel" * (pin == "kernel-reject")),
            "legs": {env: outcome and {"outcome": outcome, "audit": None,
                                       "audit_disagreement": env == "legacy" and i in disagree}
                     for env, outcome in (("pin", pin), ("legacy", legacy))},
            "overrides": overrides,
            "recipe_ids": {"pin": "sha256:" + "a" * 64, "legacy": legacy and "sha256:" + "b" * 64}})
    consts = constants.Constants(CONSTS.repo, CONSTS.source, CONSTS.published | NAMES | {
        table: CONSTS.published[table] | values for table, values in published.items()}, CONSTS.env)
    return report.summarize(recs, FRAME, {"seed": 0, "draw": draw}, consts, MEASURES | {"gates": list(rows)} |
                            (measures or {}))


def section(page: str, heading: str) -> str:
    """The text under `heading`, up to the next second-level heading."""
    return page.split(heading, 1)[1].split("\n## ", 1)[0]


def toml(values: dict) -> str:
    """Render a policy (strings, integers, booleans, lists of strings, tables of strings) as TOML."""
    def value(v):
        if isinstance(v, bool):
            return str(v).lower()
        if isinstance(v, dict):
            return "{ " + ", ".join(f"{k} = {value(x)}" for k, x in v.items()) + " }"
        return json.dumps(v)
    return "".join(f"{k} = {value(v)}\n" for k, v in values.items())


CONTAINER = {"schema": "policy/1", "kind": "container", "root": ".", "confinement": "none", "disk_floor_gb": 0,
             "disk_need_gb": 1}


def write_policy(path: Path, root: Path, **overrides) -> Path:
    """Write a valid operator policy over `root`, mode 0600, with `overrides` applied; its default denylist,
    beside it, holds one term no test plants."""
    (denylist := path.with_suffix(".denylist")).write_text("denylisted-term-zq\n")
    values = {
        "schema": "policy/1", "kind": "operator", "root": str(root), "root_device_forbidden": False,
        "confinement": "landlock", "disk_floor_gb": 1, "disk_floor_mount": str(root),
        "slice": "ledger.slice",
        "privacy_denylist": str(denylist), "scrub": ["example-host"],
        "public_tree": str(root / "public"),
        "identity": {"name": "Example Project", "email": "project@example.invalid"},
        "host_addresses": ["192.0.2.1"],
        "house_sweep": "/home/example/house-sweep.py",
    } | overrides
    path.write_text(toml(values))
    path.chmod(0o600)
    return path


def git(*args) -> str:
    """Run git as the test itself, never confined, and return its standard output."""
    return subprocess.run(["git", *map(str, args)], check=True, capture_output=True, text=True).stdout


@contextlib.contextmanager
def hold_lock(root: Path, *argv: str):
    """A separate process holding the run lock on `root` until the block exits, `argv` among its arguments."""
    holder = subprocess.Popen(
        [PY, "-c", "import sys; from pathlib import Path; from ledger import preflight;"
                   "preflight.lock(Path(sys.argv[1])); print('held', flush=True); sys.stdin.read()", root, *argv],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, env=ENV)
    try:
        assert holder.stdout.readline() == "held\n"
        yield holder
    finally:
        holder.stdin.close()
        holder.wait(timeout=10)


def unit_setenv(env=None) -> list[str]:
    """The systemd-run flags giving a unit this source tree, `env`, and this process's LEDGER_HOST_LOCK and
    LEAN_NUM_THREADS where they are set, so the unit's calls take the host lock and Lean its worker cap. A unit a
    test starts by hand that runs Lean takes these too."""
    host = {k: v for k, v in os.environ.items() if k in ("LEDGER_HOST_LOCK", "LEAN_NUM_THREADS")}
    return [f"--setenv={k}={v}" for k, v in
            {"PYTHONPATH": SRC, "PYTHONDONTWRITEBYTECODE": "1", **host, **(env or {})}.items()]


def in_unit(*argv, flags=(), env=None, timeout=300) -> SimpleNamespace:
    """Run argv as a transient systemd user service, the context every real run has, with `unit_setenv(env)`, and
    assert that its AppArmor label is `unconfined`. Returns its pid (argv is exec'd in place, so the pid is argv's),
    exit status, stdout and stderr."""
    result = subprocess.run(
        ["systemd-run", "--user", "--wait", "--pipe", "--quiet", "--collect", "--expand-environment=no",
         *unit_setenv(env), *flags, "/bin/sh", "-c",
         'read -r label < /proc/self/attr/current; echo "$label $$"; exec "$@"', "sh", *map(str, argv)],
        stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=timeout)
    head, _, out = result.stdout.partition("\n")
    label, _, pid = head.rpartition(" ")
    assert label == "unconfined", f"not a user-unit context: {head!r} {result.stderr}"
    return SimpleNamespace(pid=int(pid), code=result.returncode, out=out, err=result.stderr)


class FakeLean:
    """Stands in for confine.run in unit tests of legs, the aggregate and environment builds: records each call as
    (step, cmd, cwd) and answers it as `answers[step]` says, Proc fields over a clean exit (a list: one per call, in
    turn). The audit's default is one allowlist-only line per declaration, the walk's that no member reaches the
    constant; the compile writes its olean and ilean, and /usr/bin/time -v its report, as they would. A fetch's git
    reads its package's manifest revision, Lake's LEAN_PATH names the tree's .lake/build/lib/lean, an audit project's
    build writes ledger-audit and a tree's build a package olean holding `olean`. The other arguments of each call
    are kept in `kwargs`, in turn."""

    def __init__(self):
        self.calls, self.answers, self.kwargs, self.olean = [], {}, [], "built"

    def __call__(self, cmd, *, cwd, **kwargs):
        step = ("git" if Path(cmd[0]).name == "git" else "walk" if "walk" in cmd else "audit" if "audit" in cmd
                else "replay" if "leanchecker" in cmd else "build" if "build" in cmd else "compile" if "-i" in cmd
                else "lake")
        self.calls.append((step, cmd, cwd))
        self.kwargs.append(kwargs)
        name = cmd[-1].removeprefix("Pairs/").removesuffix(".lean")
        decls = [cmd[i + 1] for i, arg in enumerate(cmd) if arg == "--decl"]
        packages = cwd.parent.name == "packages" and json.loads((cwd.parents[2] / "lake-manifest.json").read_text())
        output = {"git": next((p["rev"] for p in packages["packages"] if p["name"] == cwd.name), "") if packages
                  else COMMIT,
                  "replay": f"replaying {cmd[-1]}{' with --fresh' * ('--fresh' in cmd)}\n",
                  "compile": "", "build": "", "walk": '{"member": null, "reason": "none"}\n',
                  "lake": f"{cwd}/.lake/build/lib/lean\n" if "printenv" in cmd else "",
                  "audit": "".join(json.dumps({"name": decl, "axioms_collector": [], "axioms_walk": [],
                                               "type_hash": "1", "type_pp": "True", "collector_us": 0,
                                               "walk_us": 0}) + "\n" for decl in decls)}[step]
        if step == "build" and cwd.name.startswith("audit-"):
            (cwd / envbuild.AUDIT_BIN).parent.mkdir(parents=True, exist_ok=True)
            (cwd / envbuild.AUDIT_BIN).write_text(f"ledger-audit {cwd.name}")
        elif step == "build" and "Aggregate" not in cmd:
            for directory in (".lake/build/lib/lean", ".lake/packages/mathlib"):
                (cwd / directory).mkdir(parents=True, exist_ok=True)
            (cwd / ".lake/packages/mathlib/Mathlib.olean").write_text(self.olean)
        if step == "compile":
            Path(cmd[cmd.index("-i") - 1]).write_text(name)
            Path(cmd[cmd.index("-i") + 1]).write_text(name)
        if "/usr/bin/time" in cmd and "-o" in cmd:
            Path(cmd[cmd.index("-o") + 1]).write_text("\tMaximum resident set size (kbytes): 4242\n")
        answer = self.answers.get(step, {})
        answer = answer.pop(0) if isinstance(answer, list) else answer
        return confine.Proc(**{"exit": 0, "killed": None, "oom_kill": 0, "wall_s": 1.0, "peak_mem_kb": 1000,
                               "output": output} | answer)


LEGS = """
import dataclasses, json, os, shutil, sys
from pathlib import Path
from ledger import REPO, confine, constants, legs, policy
pol = policy.load(sys.argv[1])
confine.apply_fs(pol)
spec = json.loads(Path(sys.argv[2]).read_text())
Path(spec["logs"]).mkdir(parents=True, exist_ok=True)
(tmp := pol.root / "tmp" / Path(spec["logs"]).parent.name).mkdir(parents=True, exist_ok=True)
os.environ["TMPDIR"] = str(tmp)
consts = constants.load(REPO)
run = legs.prepare(pol, consts, Path(spec["work"]), Path(spec["results"]), Path(spec["logs"]), ("pin", "legacy"))
if spec["pass1"]:
    legs.pass1(run, [pair for pair, _, _ in spec["cases"]], ceiling_s=1e9)
for pair, env, limits in [] if spec["pass1"] else spec["cases"]:
    published = consts.published | {"limits": consts.published["limits"] | limits}
    rss = published["limits"].pop("rss", False)
    published["assembly"] = consts.published["assembly"] | published["limits"].pop("assembly", {})
    leg = legs.run_leg(dataclasses.replace(run, consts=dataclasses.replace(consts, published=published)), pair, env, rss)
    print(json.dumps(leg), flush=True)
shutil.rmtree(tmp)
"""


def legs_spec(dev_root: Path, tmp: Path, cases: list, pass1: bool = False) -> tuple[list, Path, Path]:
    """Write the pairs of `cases`, each (pair_id, text, env, overrides of the published limits, `rss` and an
    `assembly` table among them), into a work directory and a spec for LEGS; the results and logs go beneath the
    development root, where no call writes. Returns the policy and spec arguments of LEGS, and that scratch
    directory."""
    work, scratch = tmp / "work", dev_root / "runs" / f"legs-{tmp.name}"
    (work / "pairs").mkdir(parents=True)
    (work / "sample.json").write_text(str(tmp))  # a draw of this test's own, so a progress file of its own
    rows = []
    for name, text, env, limits in cases:
        (work / "pairs" / f"{name}.lean").write_text(text)
        pair = {"i": len(rows), "pair_id": name, "refusal": None,
                "pair_sha256": "sha256:" + hashlib.sha256(text.encode()).hexdigest()}
        rows.append([pair, env, limits])
    spec = tmp / "spec.json"
    spec.write_text(json.dumps({"work": str(work), "results": str(scratch / "results"), "logs": str(scratch / "logs"),
                                "cases": rows, "pass1": pass1}))
    return [write_policy(tmp / "policy.toml", dev_root), spec], scratch


def run_legs(dev_root: Path, tmp: Path, cases: list) -> tuple[list[dict], Path]:
    """Run each case as one leg in the development environment's trees, from a systemd user unit, under the dev
    overlay. Returns the leg results in order and the scratch directory holding results/."""
    args, scratch = legs_spec(dev_root, tmp, cases)
    run = in_unit(PY, "-c", LEGS, *args, env={"LEDGER_DEV_ROOT": dev_root}, timeout=1800)
    assert run.code == 0, run.err[-3000:]
    return [json.loads(line) for line in run.out.splitlines()], scratch
