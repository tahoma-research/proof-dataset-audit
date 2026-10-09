import contextlib
import dataclasses
import hashlib
import io
import json
import re
import shutil
from collections import Counter
from types import SimpleNamespace

import pytest
from helpers import REPO, FakeLean, record

from ledger import (aggregate, confine, constants, datefree, envbuild, frame, gatefile, ingest, legs, modes, policy,
                    probes, records, report, sample)
from ledger.types import LedgerStop, canonical

ELAB = {"exit": 1, "output": "Pairs/x.lean:3:2: error: unsolved goals"}  # the pin's elab-error row


@pytest.fixture
def world(root, make_policy, tmp_path, monkeypatch, capsys):
    """A published tree of the recipe, the classifier and the audit projects, its summary naming the sample of a release
    of three single-proof entries; elan in place under the root; every toolchain install and the release's download
    answered by stand-ins, every process by FakeLean. `go(**kwargs)` runs `ledger run` with the published constants'
    tables replaced as given, and returns its exit and output; `steps` records, in turn, each install, the download,
    each tree's fetch and build, each leg by environment, the aggregate's build and replay, and the records;
    `facts` holds what its run report says."""
    repo, release = tmp_path / "published", tmp_path / "release.json"
    for top in ("recipe", "classifier", "lean"):
        shutil.copytree(REPO / top, repo / top, ignore=shutil.ignore_patterns(".lake"))
    release.write_text(json.dumps([record(f"t{i}", 1, f"P{i}") for i in range(3)]))
    consts = dataclasses.replace(constants.load(REPO), repo=repo)
    work = tmp_path / "draw"
    ingest.write(ingest.parse(release, consts.published["assembly"]["suffix_regex"]), work)
    drawn = canonical(sample.draw(frame.build(work / "entries.jsonl", consts), consts.published))
    (repo / "results").mkdir()
    summary = {"sample_sha256": "sha256:" + hashlib.sha256(drawn).hexdigest(),
               "canonical_subset_sha256": "sha256:" + "0" * 64}
    (root / "elan/bin").mkdir(parents=True)
    (root / "elan/bin/elan").touch()
    steps, lean = [], FakeLean()

    def install(pol, consts, env, logs):
        name = (consts.repo / "recipe" / env / "lean-toolchain").read_text().strip()
        (toolchain := envbuild.toolchain_dir(pol.root, name) / "bin").mkdir(parents=True)
        (toolchain / "lean").write_text(name)
        envbuild.record_toolchain(pol.root, toolchain.parent)
        steps.append(f"install {env}")

    def recorded(module, name, step):
        real = getattr(module, name)
        monkeypatch.setattr(module, name, lambda *args, **kwargs: steps.append(step(*args)) or real(*args, **kwargs))
    monkeypatch.setattr(probes, "install_toolchain", install)
    monkeypatch.setattr(ingest, "fetch", lambda consts, pol: steps.append("download") or release)
    recorded(envbuild, "fetch", lambda pol, consts, logs, env, *_: f"fetch {env}")
    recorded(envbuild, "build", lambda pol, consts, logs, env, *_: f"build {env}")
    recorded(legs, "run_leg", lambda run, pair, env, *_: f"leg {env}")
    recorded(aggregate, "build", lambda *_: "aggregate build")
    recorded(aggregate, "replay", lambda *_: "aggregate replay")
    recorded(records, "build", lambda *_: "records")
    monkeypatch.setattr(confine, "run", lean)
    monkeypatch.setenv("TMPDIR", "/unused")  # the run sets its own; this makes monkeypatch restore it
    pol = policy.load(make_policy())
    runs, facts = iter(range(1, 100)), {}

    def go(pair=None, with_legacy=False, **tables) -> tuple[int, str]:
        published = consts.published | {table: consts.published[table] | values for table, values in tables.items()}
        (repo / "results/summary.json").write_text(json.dumps(summary))
        (run_dir := root / "runs" / f"2026-12-0{next(runs)}T044500").mkdir(parents=True)
        facts.clear()
        code = datefree.run(pol, dataclasses.replace(consts, published=published), run_dir, facts, pair=pair,
                            with_legacy=with_legacy)
        return code, capsys.readouterr().out
    return SimpleNamespace(go=go, steps=steps, lean=lean, summary=summary, repo=repo, root=root, facts=facts)


def compressed(steps: list[str]) -> list[str]:
    return [step for i, step in enumerate(steps) if i == 0 or steps[i - 1] != step]


def test_full_step_list_order(world):
    """The full run, one environment at a time: the pin's toolchain, the release, the pin tree, every pin leg, the
    aggregate's build and replay, then the legacy toolchain, tree and every legacy leg, then the records. A pair
    whose lines the aggregate's build fails on is harness-error, and the report says what decided its class."""
    # covers: test_one_env_at_a_time_order
    world.lean.answers = {"build": [{}, {}, {"exit": 1, "output": "error: Aggregate.lean:5:0: x\n"}, {}, {}, {}]}
    assert world.go()[0] == 0
    assert compressed(world.steps) == [
        "install pin", "download", "fetch pin", "build pin", "leg pin", "aggregate build", "aggregate replay",
        "install legacy", "fetch legacy", "build legacy", "leg legacy", "records"]
    assert world.steps.count("leg pin") == world.steps.count("leg legacy") == 3
    assert world.facts["classes"] == Counter({("reproduced", "pin accepted and legacy accepted"): 2, ("harness-error",
        "pin accepted and legacy accepted, decided by the aggregate's build, which failed on its lines"): 1})


def test_ignores_published_progress_and_records(world, monkeypatch):
    """A published progress file listing every pair complete is never read: the run writes its own under
    run-<run-id>/ and runs every leg, and as it ends deletes everything there but its records, a symlink as the link
    alone, and an entry it cannot delete named on stderr with the rest deleted all the same; the operator's own
    results are untouched."""
    (world.repo / "results/progress.json").write_text("not read\n")
    (world.root / "results").mkdir()
    (world.root / "results/progress.json").write_text("the operator's\n")
    (outside := world.root / "outside/kept").mkdir(parents=True)
    own, real = world.root / "run-2026-12-01T044500", records.build

    def plant(sample, pairs, prog, results, *rest):  # a symlink to a directory, and a directory it cannot empty
        (results.parent / "link").symlink_to(outside.parent)
        (own / "stuck").mkdir()
        (own / "stuck/file").touch()
        (own / "stuck").chmod(0o500)
        return real(sample, pairs, prog, results, *rest)
    monkeypatch.setattr(records, "build", plant)
    try:
        with contextlib.redirect_stderr(err := io.StringIO()):
            world.go()
        assert world.steps.count("leg pin") == 3
        assert (world.root / "results/progress.json").read_text() == "the operator's\n"
        assert len((own / "results/records.jsonl").read_text().splitlines()) == 3
        assert sorted(p.relative_to(own).as_posix() for p in own.rglob("*")) == [
            "results", "results/records.jsonl", "stuck", "stuck/file"]
        assert outside.is_dir() and err.getvalue().startswith("ledger run: not deleted: [Errno 13] Permission denied")
    finally:  # so that the tmp directory can be removed
        if (own / "stuck").exists():
            (own / "stuck").chmod(0o700)


def test_redraw_equals_published_sample(world):
    """A redraw that is not the published sample stops the run before any tree is built, naming both digests; the
    run's directory is emptied all the same, its toolchain included. Without elan in place, the run stops before it
    makes anything."""
    published = world.summary["sample_sha256"]
    world.summary["sample_sha256"] = "sha256:" + "f" * 64
    with pytest.raises(LedgerStop, match=f"the redraw is sample {published}, not the published sample sha256:f+$"):
        world.go()
    assert "fetch pin" not in world.steps and "install pin" in world.steps
    assert [p.name for p in (world.root / "run-2026-12-01T044500").rglob("*")] == ["results"]
    (world.root / "elan/bin/elan").unlink()
    with pytest.raises(LedgerStop, match="elan/bin/elan is missing: elan is placed at provisioning, and nothing in the "
                                         "pipeline installs it$"):
        world.go()
    assert not (world.root / "run-2026-12-02T044500").exists()


def test_full_run_prints_canonical_subset_hash(world):
    """The run prints its own canonical-subset hash beside the published one, and `4b: EQUAL` exactly when they are
    equal: timings that differ from the published run's leave it EQUAL; a class that differs makes it DIFFERENT."""
    # covers: test_4b_equal_ignores_timing_fields
    code, out = world.go()
    mine = re.search(r"^canonical subset (sha256:\w+)$", out, re.M)[1]
    assert code == 0 and out.endswith("4b: DIFFERENT\n") and f"published canonical subset sha256:{'0' * 64}" in out
    world.summary["canonical_subset_sha256"] = mine
    world.lean.answers = {step: {"wall_s": 99.0} for step in ("compile", "replay", "audit")}
    assert world.go()[1].endswith(f"canonical subset {mine}\npublished canonical subset {mine}\n4b: EQUAL\n")
    world.lean.answers = {"compile": [{}, {}, ELAB, {}, {}, {}]}  # the third pair's pin leg fails to elaborate
    assert world.go()[1].endswith("4b: DIFFERENT\n")


def test_4b_says_when_only_resource_classes_differ(world):
    """Where the run's own records differ from the published records.jsonl only in pairs timed-out or
    resource-exhausted on one side, a line after the DIFFERENT verdict says so; where any other pair differs too, none
    does; and where the published records cannot be read, the verdict stands and a line after it says so."""
    world.go()
    mine = [json.loads(line) for line in (world.root / "run-2026-12-01T044500/results/records.jsonl").read_text()
            .splitlines()]
    for classes, note in ((["timed-out"], "\n4b: only in timed-out or resource-exhausted classes, which turn on the "
                                          "machine's time and memory"), (["timed-out", "rejected-by-checker"], "")):
        published = [r | {"class": cls} for r, cls in zip(mine, classes)] + mine[len(classes):]
        (world.repo / "results/records.jsonl").write_bytes(records.dump(published))
        world.summary["canonical_subset_sha256"] = report.canonical_subset(published)
        assert world.go()[1].endswith(f"4b: DIFFERENT{note}\n")
    (world.repo / "results/records.jsonl").write_text("{\n")
    assert "4b: DIFFERENT\n4b: the published records.jsonl cannot be compared with this run's: JSONDecodeError" in (
        world.go()[1])


@pytest.mark.parametrize("status, absent", [({"legacy": "environment-unavailable"}, "install legacy"),
                                            ({"independent_check": "replay-unavailable"}, "aggregate replay")],
                         ids=["test_no_legacy_when_unavailable", "test_no_replay_when_replay_unavailable"])
def test_branch_skips_its_step(world, status, absent):
    """Where the published constants record the legacy environment unavailable, no legacy toolchain, tree or leg; where
    they record the replay unavailable, the aggregate is built and not replayed."""
    assert world.go(status=status)[0] == 0
    assert absent not in world.steps and "records" in world.steps
    assert ("leg legacy" in world.steps) == ("legacy" not in status)


def test_deletes_pin_tree_when_disk_fits_one(world, monkeypatch):
    """When the free space above the policy's floor holds one tree only, the pin's is deleted before the legacy one is
    built, and kept when it holds both."""
    monkeypatch.setattr(confine, "free_gb", lambda mount: 100.0)
    real, seen = envbuild.fetch, []
    monkeypatch.setattr(envbuild, "fetch", lambda pol, consts, logs, env, *rest: seen.append(
        (env, (pol.root / "env/pin").exists())) or real(pol, consts, logs, env, *rest))
    assert world.go()[0] == 0 and seen == [("pin", False), ("legacy", False)]
    monkeypatch.setattr(confine, "free_gb", lambda mount: 1e6)
    assert world.go()[0] == 0 and seen[-1] == ("legacy", True)
    legacy = constants.load(REPO).published["budgets"]["legacy_env_gb"]
    monkeypatch.setattr(confine, "free_gb", lambda mount: legacy + 0.5)  # the legacy tree, not above the 1 GB floor
    assert world.go()[0] == 0 and seen[-1] == ("legacy", False)


def test_run_uses_seeded_recipe_under_stop_loss(world):
    """Under the stop-loss the run fetches the seeded recipe, its dependency layers by the cache's get, with network,
    and builds and runs its legs in that tree."""
    assert world.go(status={"stop_loss": True})[0] == 0
    assert [s for s in world.steps if s.startswith(("fetch pin", "build pin"))] == ["fetch pin-seeded",
                                                                                    "build pin-seeded"]
    seeded = world.root / "run-2026-12-01T044500/env/pin-seeded"
    assert any(cmd[-3:] == ["exe", "cache", "get"] and cwd == seeded and kwargs["net"]
               for (_, cmd, cwd), kwargs in zip(world.lean.calls, world.lean.kwargs))
    assert any(step == "compile" and cwd == seeded for step, _, cwd in world.lean.calls)


def test_never_reads_date(world, monkeypatch):
    """The run consults neither D+0 nor the mode table."""
    for module, name in ((gatefile, "d0"), (modes, "action"), (modes, "rebuild_night")):
        monkeypatch.setattr(module, name, lambda *_: pytest.fail(f"{name} read"))
    assert world.go()[0] == 0


def test_pair_prints_digest_and_outcome(world):
    """`run --pair` takes the pair by its digest or its pair_id, runs its pin leg alone, and prints its digest, its pin
    outcome and, the outcome determining it, its class; it builds no legacy environment."""
    # covers: test_pair_never_builds_legacy_for_pin_determined_class
    world.go()
    pair = json.loads((world.root / "run-2026-12-01T044500/results/records.jsonl").read_text().splitlines()[1])
    world.steps.clear()
    for chosen in (pair["pair_sha256"], pair["pair_id"]):
        assert world.go(pair=chosen) == (0, f"pair_sha256 {pair['pair_sha256']}\npin outcome accepted\n"
                                            "class reproduced\n")
        assert world.facts["classes"] == Counter({("reproduced", "pin accepted"): 1})
    assert world.steps.count("leg pin") == 2
    assert not any("legacy" in step or "aggregate" in step for step in world.steps)


def test_pair_exits_3_when_declared_needed(world):
    """A pair whose pin leg fails leaves its class to the declared environment: it says so and exits 3, building no
    legacy environment, unless the legacy environment is unavailable, or --with-legacy, which runs its legacy leg and
    prints the class."""
    world.lean.answers = {"compile": ELAB}
    code, out = world.go(pair="t0__p0")
    assert code == datefree.NEEDS_DECLARED
    assert out.endswith("pin outcome elab-error\nclass needs the declared environment\n")
    assert world.go(pair="t0__p0", status={"legacy": "environment-unavailable"})[0] == 0
    assert not any("legacy" in step for step in world.steps)
    world.lean.answers = {"compile": [ELAB, ELAB]}
    assert world.go(pair="t0__p0", with_legacy=True) == (0, f"pair_sha256 {out.split()[1]}\npin outcome elab-error\n"
                                                            "class rejected-by-checker\n")
    assert "leg legacy" in world.steps
