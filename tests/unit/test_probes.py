"""The D+7 probe through `ledger probe d7`. confine.run is replaced by a recorder that answers as each tool would
(elan leaving a toolchain in the directory it was given), so the conditions, the install record and the gate
lines under test are the code's own."""

import json
import re
import shutil
from pathlib import Path
from types import SimpleNamespace

import pytest
from helpers import record

from ledger import REPO, cli, confine, constants, envbuild, fixtures, frame, gatefile, ingest, policy, probes, sample
from ledger.types import LedgerStop

PIN, LEGACY = ((REPO / "recipe" / env / "lean-toolchain").read_text().strip() for env in ("pin", "legacy"))


class FakeRun:
    """Stands in for confine.run, answering as each tool would: elan leaves the toolchain it is asked for in the
    directory it was given, git ls-remote names `mathlib`, git rev-parse a legacy package's manifest revision,
    leanchecker prints the replay line. `answers` overrides, by a call's last argument, its exit status and output;
    such an elan call installs nothing."""

    def __init__(self, repo: Path):
        self.calls, self.answers = [], {}
        manifest = json.loads((repo / "recipe/legacy/lake-manifest.json").read_text())
        self.revs = {p["name"]: p["rev"] for p in manifest["packages"]}
        self.mathlib = self.revs["mathlib"]

    def __call__(self, cmd, *, cwd, writes, net=False, env=None, memory_max_mb=None, log=None, timeout_s=None):
        self.calls.append(SimpleNamespace(cmd=[Path(cmd[0]).name, *cmd[1:]], writes=writes, net=net,
                                          timeout_s=timeout_s))
        name, exit, output = Path(cmd[0]).name, 0, ""
        if cmd[-1] in self.answers:
            exit, output = self.answers[cmd[-1]]
        elif name == "elan":
            installed = cwd / "toolchains" / envbuild.toolchain_dir(cwd, cmd[-1]).name  # cwd is its ELAN_HOME
            (installed / "bin").mkdir(parents=True)
            (installed / "bin/lean").write_text(cmd[-1])
        elif "ls-remote" in cmd:
            output = f"{self.mathlib}\t{cmd[-2]}\n"
        elif "rev-parse" in cmd:
            output = self.revs[cwd.name]
        elif "leanchecker" in cmd:
            output = "replaying Toy.Entry with --fresh\n"
        elif "pytest" in cmd:
            output = "3 passed in 0.1s\n"
        return confine.Proc(exit, None, None, 0.1, None, output)


@pytest.fixture
def world(code_repo, make_policy, root, monkeypatch, capsys, tmp_path):
    """`probe(pairs)` runs `ledger probe d7` over a release of that many single-proof entries and returns its
    exit status and, by condition letter, whether it was printed met and its evidence. elan is in place, a
    Landlock layer stands applied, and podman's storage.conf, beneath HOME, names an existing graph root under the
    ledger root."""
    fake, self_tests = FakeRun(code_repo), []
    release = tmp_path / "release.json"
    (root / "elan/bin").mkdir(parents=True)
    (root / "elan/bin/elan").touch()
    (root / "podman/storage").mkdir(parents=True)
    conf = tmp_path / "home/.config" / probes.STORAGE_CONF
    conf.parent.mkdir(parents=True)
    conf.write_text(f'[storage]\ndriver = "overlay"\ngraphroot = "{root}/podman/storage"\n')
    monkeypatch.setenv("HOME", str(tmp_path / "home"))
    for name in ("CONTAINERS_STORAGE_CONF", "XDG_CONFIG_HOME"):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setattr(cli, "REPO", code_repo)
    monkeypatch.setattr(confine, "apply_fs", lambda pol: "landlock (stand-in)")  # the real one confines this process
    monkeypatch.setattr(confine, "stop_leftover_scopes", lambda root: None)
    monkeypatch.setattr(confine, "run", fake)
    monkeypatch.setattr(confine, "self_test",
                        lambda pol: self_tests.append(pol) or confine.ConfineReport("unconfined", {"probe": True}))
    monkeypatch.setattr(ingest, "fetch", lambda consts, pol: release)
    monkeypatch.setenv("TMPDIR", "/unused")  # cli.main rewrites TMPDIR; this makes monkeypatch restore it
    path = make_policy()

    def probe(pairs=300):
        release.write_text(json.dumps([record(f"t{i}", 1, f"P{i}") for i in range(pairs)]), encoding="utf-8")
        code = cli.main(["probe", "d7", "--policy", str(path)])
        printed = re.findall(r"^\(([a-f])\) (met|unmet): (.*)$", capsys.readouterr().out, re.M)
        return code, {letter: (state == "met", evidence) for letter, state, evidence in printed}
    return SimpleNamespace(fake=fake, root=root, conf=conf, probe=probe, self_tests=self_tests,
                           pol=policy.load(path))


DRAWN = [("d7-frame", "measured"), ("d7-sample", "drawn: the whole frame")]


@pytest.mark.parametrize("pairs, broken, unmet, gates, networked", [
    (200, None, [], [*DRAWN, ("d7", "met")], ["elan", "git", "elan", "python"]),
    (150, None, ["d", "e"], [("d7-frame", "frame<200: swap-to-alternate"), ("d7", "unmet: (d)")],
     ["elan", "git", "elan", "python"]),
    (200, "toolchain", ["c"], [*DRAWN, ("d7", "unmet: (c)")], ["elan", "git", "elan", "python"]),
    (200, "tag", ["c"], [*DRAWN, ("d7", "unmet: (c)")], ["elan", "git", "python"]),
], ids=["test_d7_all_six_met_writes_frame_sample_d7_lines", "test_frame_below_200_stops_swap",
        "test_first_unmet_stops_no_build", "test_first_unmet_stops_no_build-tag-not-the-recipe-commit"])
def test_d7(world, pairs, broken, unmet, gates, networked):
    """The probe prints six conditions with their evidence, writes the frame and sample lines it has figures for
    and then the d7 line (met, or the first unmet condition), and exits 0 only when all six are met. A frame
    below 200 drawable pairs is not drawn from; one below the sample size is drawn whole. The Mathlib tag is
    resolved, writing nothing, before the legacy toolchain is downloaded, and one naming another commit stops
    (c). Every toolchain the probe installs is installed by a networked call that writes its staging directory
    alone, and its digest recorded; nothing else has network, pip installs hash-pinned wheels alone, (a) reports
    the run's own self-test, and no environment build starts."""
    # covers: test_frame_below_1000_takes_all
    if broken == "toolchain":
        world.fake.answers[LEGACY] = (1, "error: no such toolchain")
    if broken == "tag":
        world.fake.mathlib = "0" * 40
    code, found = world.probe(pairs)
    assert list(found) == list("abcdef") and [k for k, (met, _) in found.items() if not met] == unmet
    assert code == (2 if unmet else 0)
    assert [row[1:3] for row in gatefile.rows(world.pol)] == gates
    reasons = {row[1]: row[4] for row in gatefile.rows(world.pol)}
    assert f"drawable_pairs={pairs}" in reasons["d7-frame"]
    assert reasons["d7"] == "; ".join(f"{k}={'unmet' if k in unmet else 'met'}" for k in "abcdef")
    if "e" not in unmet:
        drawn = json.loads((world.root / "work/sample.json").read_text())
        assert len(drawn["draw"]) == drawn["drawable_frame_size"] == pairs
        assert reasons["d7-sample"] == f"seed=0; pairs={pairs}; distinct_entries={pairs}"
    recorded = json.loads((world.root / envbuild.TOOLCHAINS).read_text())
    installed = sorted((world.root / "elan/toolchains").iterdir())
    assert recorded == {t.name: envbuild.toolchain_digest(t) for t in installed} and len(installed) == 2 - bool(broken)
    assert [call.cmd[0] for call in world.fake.calls if call.net] == networked
    assert all(call.writes == [world.root / "elan/staging"] for call in world.fake.calls if call.cmd[0] == "elan")
    assert all(call.writes == [] for call in world.fake.calls if call.cmd[0] == "git")
    assert len(world.self_tests) == 1 and "confinement self-test passed (label unconfined)" in found["a"][1]
    pip = next(call.cmd for call in world.fake.calls if "pip" in call.cmd)  # hash-pinned wheels only
    assert pip[-5:] == ["--only-binary", ":all:", "--require-hashes", "-r", str(probes.REQUIREMENTS)]
    assert not (world.root / "env/pin/.lake/build").exists()


@pytest.mark.parametrize("graphroot, via", [
    ("{tmp}/elsewhere", None), ("{root}/podman/link", None), ("{root}/podman/missing", None), (None, None),
    ("{tmp}/elsewhere", "CONTAINERS_STORAGE_CONF"), ("{tmp}/elsewhere", "XDG_CONFIG_HOME"),
], ids=["elsewhere", "symlink-out", "missing", "no-storage-conf", "CONTAINERS_STORAGE_CONF", "XDG_CONFIG_HOME"])
def test_podman_store_must_be_under_root(world, tmp_path, monkeypatch, graphroot, via):
    """Condition (a) is unmet unless podman's storage.conf names, as its graph root, an existing directory that
    resolves under the ledger root; podman itself is never run. The file is the one podman reads: the one
    CONTAINERS_STORAGE_CONF names, else the one under XDG_CONFIG_HOME, else the one under ~/.config."""
    (tmp_path / "elsewhere").mkdir()
    (world.root / "podman/link").symlink_to(tmp_path / "elsewhere")
    conf = world.conf
    if via:  # the default file stays good, and XDG_CONFIG_HOME names it unless it is the variable under test
        conf = tmp_path / "other" / probes.STORAGE_CONF
        conf.parent.mkdir(parents=True)
        monkeypatch.setenv("XDG_CONFIG_HOME", str(world.conf.parents[1]))
        monkeypatch.setenv(via, str(conf if via == "CONTAINERS_STORAGE_CONF" else tmp_path / "other"))
    if graphroot:
        conf.write_text(f'[storage]\ngraphroot = "{graphroot.format(tmp=tmp_path, root=world.root)}"\n')
    else:
        conf.unlink()
    code, found = world.probe()
    assert code == 2 and [k for k, (met, _) in found.items() if not met] == ["a"]
    assert "podman" in found["a"][1] and "confinement self-test passed" in found["a"][1]
    assert "podman" not in [call.cmd[0] for call in world.fake.calls]


def test_toy_fresh_asserts_replaying_line(world):
    """Condition (b) is unmet unless leanchecker prints the `replaying Toy.Entry with --fresh` line, whatever its
    exit."""
    world.fake.answers[probes.TOY] = (0, "")
    code, found = world.probe()
    assert code == 2 and [k for k, (met, _) in found.items() if not met] == ["b"]


def test_elan_missing_stops_clearly(world):
    """Without the elan placed at provisioning, every toolchain install stops before any call, saying so;
    the venv, which needs no elan, is still installed and (f) met."""
    (world.root / "elan/bin/elan").unlink()
    code, found = world.probe()
    assert code == 2 and [k for k, (met, _) in found.items() if not met] == ["a", "b", "c"]
    assert all("placed at provisioning" in found[k][1] for k in "ac") and "venv with pytest==" in found["f"][1]
    assert [call.cmd[0] for call in world.fake.calls if call.net] == ["python"]  # pip alone


@pytest.mark.parametrize("stages, says", [(None, "staged no"), ("link", "a symbolic link"),
                                          ("other", "the recorded one stands")],
                         ids=["stages-nothing", "stages-a-link", "digest-differs"])
def test_reinstall_keeps_the_recorded_toolchain(world, monkeypatch, stages, says):
    """A re-install that stages nothing, stages a link, or one whose digest is not the one recorded at the first
    install, stops (a) and leaves the installed toolchain and its recorded digest as they were, so (b) still runs
    on it."""
    pin, record = envbuild.toolchain_dir(world.root, PIN), world.root / envbuild.TOOLCHAINS
    (pin / "bin").mkdir(parents=True)
    (pin / "bin/lean").write_text("the first install")
    envbuild.record_toolchain(world.root, pin)
    before = record.read_text()
    if stages != "other":
        world.fake.answers[PIN] = (0, "")  # elan exits 0
    if stages == "link":  # a link to the installed toolchain, whose digest is the recorded one
        def run(cmd, **kwargs):
            if cmd[-1] == PIN:
                (kwargs["cwd"] / "toolchains").mkdir()
                (kwargs["cwd"] / "toolchains" / pin.name).symlink_to(pin)
            return world.fake(cmd, **kwargs)
        monkeypatch.setattr(confine, "run", run)
    code, found = world.probe()
    assert [k for k, (met, _) in found.items() if not met] == ["a"] and says in found["a"][1]
    assert json.loads(record.read_text())[pin.name] == json.loads(before)[pin.name]
    assert (pin / "bin/lean").read_text() == "the first install"


@pytest.mark.parametrize("broken, unmet, says", [
    ("toy-build", ["b"], "lake build of the toy exited 1"),
    ("unreconciled", ["d", "e"], "do not sum to the record count"),
    ("error", ["e"], "KeyError: 'seed'"),
], ids=["toy-build", "unreconciled", "error"])
def test_a_failing_probe_fails_its_condition_alone(world, monkeypatch, broken, unmet, says):
    """A probe that fails for any reason, an unexpected error included, leaves its own condition unmet with the
    cause as its evidence; the others are still probed and the d7 line is written. The toy's build stops (b) by
    its own exit status, and frame figures whose split counts do not reconcile stop (d)."""
    if broken == "toy-build":
        world.fake.answers["build"] = (1, "error: Toy/Entry.lean: unknown identifier")
    if broken == "unreconciled":
        build = frame.build

        def unreconciled(*args):
            built = build(*args)
            built.summary["reconciliation"] = "counted split values sum to records_total: false"
            return built
        monkeypatch.setattr(frame, "build", unreconciled)
    if broken == "error":
        monkeypatch.setattr(sample, "draw", lambda built, published: {}["seed"])
    code, found = world.probe()
    assert code == 2 and [k for k, (met, _) in found.items() if not met] == unmet and says in found[unmet[0]][1]
    assert gatefile.rows(world.pol)[-1][1:3] == ("d7", f"unmet: ({unmet[0]})")


def test_without_landlock_no_self_test(world, monkeypatch):
    """Where no Landlock layer applies, as under a container policy, (a) runs no self-test and says so."""
    monkeypatch.setattr(confine, "apply_fs", lambda pol: None)
    code, found = world.probe()
    assert code == 0 and world.self_tests == [] and "no confinement self-test" in found["a"][1]


@pytest.fixture
def legacy(code_repo, make_policy, root, monkeypatch, tmp_path):
    """The D+14 probes' world: the legacy toolchain installed and recorded, the audit projects beside the recipe,
    the run's TMPDIR, and every call answered by FakeRun."""
    toolchain = envbuild.toolchain_dir(root, LEGACY)
    (toolchain / "bin").mkdir(parents=True)
    (toolchain / "bin/lean").write_text(LEGACY)
    envbuild.record_toolchain(root, toolchain)
    shutil.copytree(REPO / "lean", code_repo / "lean", ignore=shutil.ignore_patterns(".lake"))
    (root / "tmp/run").mkdir(parents=True)
    monkeypatch.setenv("TMPDIR", str(root / "tmp/run"))
    monkeypatch.setattr(confine, "run", fake := FakeRun(code_repo))
    (tmp_path / "logs").mkdir()
    return SimpleNamespace(pol=policy.load(make_policy()), consts=constants.load(code_repo), logs=tmp_path / "logs",
                           fake=fake, root=root)


def test_cache_probe_failure_builds_from_source_same_cap(legacy):
    """The cache probe fetches the legacy tree without its cache, then, with network, the declared revision's cache
    for one low module alone, the two within its 4-hour line. One that leaves no olean does not serve, whatever its
    exit, and is recorded so; the legacy environment's own fetch then downloads no cache, so it is built from
    source, its attempts given the same 36 hours."""
    legacy.fake.answers[probes.CACHE_MODULE] = (0, "No files to download")  # exits 0, leaving no olean
    assert probes.d14_cache_probe(legacy.pol, legacy.consts, legacy.logs) is False
    row = gatefile.rows(legacy.pol)[-1]
    assert row[1:3] == ("legacy-cache-probe", "does not serve") and row[4].endswith("exit=0; killed=None; olean=False")
    cache = [c for c in legacy.fake.calls if "cache" in c.cmd]
    assert [(c.cmd[-3:], c.net) for c in cache] == [(["cache", "get", probes.CACHE_MODULE], True)]
    fetched = next(c for c in legacy.fake.calls if c.cmd[-2:] == ["env", "true"])
    assert fetched.timeout_s == probes.D14_LINE_S > cache[0].timeout_s > probes.D14_LINE_S - 60  # what the fetch left
    envbuild.fetch(legacy.pol, legacy.consts, legacy.logs, "legacy")
    assert [c for c in legacy.fake.calls if "cache" in c.cmd] == cache
    assert envbuild.check_attempt(legacy.root, legacy.consts, "legacy", "pin", 1) == envbuild.LEGACY_CAP_S == 36 * 3600


def test_collector_failure_unavailable_at_once(legacy):
    """A legacy audit project that does not elaborate at the declared toolchain is recorded so, with Lake's exit,
    and makes the legacy environment unavailable at once, in the constants and the gate file, before any build."""
    legacy.fake.answers["build"] = (1, "error: unknown constant 'Lean.Elab.Command.CollectAxioms.collect'")
    assert probes.d14_legacy_collector(legacy.pol, legacy.consts, legacy.logs) is False
    assert [row[1:3] for row in gatefile.rows(legacy.pol)] == [("legacy-collector", "does not elaborate"),
                                                                ("legacy-status", "environment-unavailable")]
    assert "collector_exit=1" in gatefile.rows(legacy.pol)[-1][4]
    assert constants.load(legacy.consts.repo).published["status"]["legacy"] == "environment-unavailable"
    assert [(c.cmd, c.timeout_s) for c in legacy.fake.calls] == [(["lake", "build"], probes.D14_LINE_S)]


@pytest.mark.parametrize("answers, timing", [
    ({"replay": {"exit": 1, "wall_s": 900.0, "output": "replaying Aggregate with --fresh\nuncaught exception: while "
                 "replaying declaration 'planted_false':\n(kernel) declaration type mismatch\n"}}, 900.0),
    ({"replay": {"exit": -9, "killed": "wall-clock", "wall_s": 14399.0}}, probes.D14_LINE_S),
    ({"build": {"exit": -9, "killed": "wall-clock"}}, probes.D14_LINE_S),
    ({"replay": {"exit": -9, "killed": "oom"}}, None),
], ids=["replay_timed", "replay_at_line_4h", "build_at_line_4h", "replay_oom_stops"])
def test_proof1b_timing_capped_4h(legs_run, root, answers, timing):
    """The proof-1b timing: the fixture project made ready as proof 1b makes it, its aggregate over every fixture
    pair, the plant's included, built, then replayed once with --fresh under /usr/bin/time -v, the two inside the
    4-hour line. The figure is the replay's wall-clock, its rejection of the plant included; a run reaching the line
    is recorded as 4 hours; a replay killed for memory gives no figure and stops."""
    run, _, lean = legs_run(0, ("pin",))
    shutil.copytree(REPO / "fixtures/proof1b", root / "fixtures-src/proof1b")
    lean.answers |= answers
    if timing is None:
        with pytest.raises(LedgerStop, match="killed oom"):
            probes.d14_proof1b_timing(run.pol)
    else:
        assert probes.d14_proof1b_timing(run.pol) == timing
    built = (root / "fixtures-run/env/proof1b/Aggregate.lean").read_text()
    assert built.startswith(fixtures.HEADER) and all(name in built for name in (fixtures.PLANTED, fixtures.VICTIM))
    calls = [(step, cmd, kw["timeout_s"]) for (step, cmd, _), kw in zip(lean.calls, lean.kwargs) if step != "git"]
    assert [step for step, _, _ in calls] == ["build"] + ["replay"] * ("build" not in answers)
    assert calls[0][2] == probes.D14_LINE_S
    for _, cmd, timeout_s in calls[1:]:
        assert {"/usr/bin/time", "-v", "--fresh"} <= set(cmd) and probes.D14_LINE_S - 60 < timeout_s < probes.D14_LINE_S
