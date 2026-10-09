"""The D+14 measurement. The projection and its outcome are computed from recorded figures alone, so each branch is
a fixture; the run that records them is driven through the legs and the aggregate with every process answered."""

import dataclasses
import json
import shutil
from datetime import date

import pytest
from helpers import REPO

from ledger import constants, gatefile, measure, preflight, probes
from ledger.types import LedgerStop

H = 3600
S, CEILING = 1000, 50400
TODAY = date(2026, 11, 16)
PAIRS = [("accepted", 5.0, 2.0, 2_000_000), ("elab-error", 20.0, None, 1_000_000), ("accepted", 12.0, 50.0, 1_500_000)]
KEYS = {"limits": ("replay_cap_s", "replay_cap_rule"), "sampling": ("cut_n",), "status": ("independent_check",)}
DEFAULTS = {"replay_cap_s": 43200, "replay_cap_rule": "default", "cut_n": 0, "independent_check": "pending"}
HEADER = constants.load(REPO).published["assembly"]["header"]


def theorem(name: str) -> str:
    return f"{HEADER}theorem {name} : True := by\n  trivial\n"


def aggregate(members: int, build, replay) -> dict:
    """An aggregate's record: its build's wall-clock or "line" (killed at its 4-hour line); its replay's wall-clock,
    "killed", (constant, member) for a rejection, or None where none ran."""
    line = build == "line"
    return {"members": [f"p{i}__p0" for i in range(members)],
            "build": {"wall_s": 4 * H + 2.5 if line else build, "exit": -9 if line else 0,
                      "killed": "wall-clock" if line else None, "peak_mem_kb": 8_000_000},
            "audit": {"wall_s": 1.0, "exit": 0, "killed": None, "peak_mem_kb": 6_000_000} if members else None,
            "replay": None if replay is None else _replay(replay)}


def _replay(replay) -> dict:
    if replay == "killed":
        return {"wall_s": 1.0, "exit": -9, "killed": "wall-clock", "max_rss_kb": None, "rejected_constant": None,
                "member": None}
    constant, member = replay if isinstance(replay, tuple) else (None, None)
    return {"wall_s": 1.0 if constant else replay, "exit": 1 if constant else 0, "killed": None,
            "max_rss_kb": 4_000_000, "rejected_constant": constant, "member": member}


def measured(root, E=3600.0, T=None, Eb=600.0, Tb=700.0, M=10, pairs=PAIRS):
    """measure/d14 under `root`, as the run records it: the pilot pairs, the baseline, and the pilot aggregate unless
    no pilot pair compiled clean (M = 0)."""
    d = root / measure.DIR
    d.mkdir(parents=True)
    files = {"pairs": [{"pair_id": f"p{i}__p0", "outcome": o, "compile_s": c, "replay_s": r, "peak_mem_kb": k}
                       for i, (o, c, r, k) in enumerate(pairs)],
             "baseline": aggregate(0, Eb, E), "pilot": aggregate(M, Tb, T) if M else None}
    for name, value in files.items():
        if value is not None:
            (d / f"{name}.json").write_text(json.dumps(value))
    return d


def published(consts) -> dict:
    loaded = constants.load(consts.repo).published
    return {key: loaded[table][key] for table, keys in KEYS.items() for key in keys}


UNAVAILABLE = {"independent_check": "replay-unavailable"}


@pytest.mark.parametrize("figures, outcome, sets, expect", [
    ({"T": "killed"}, "replay-unavailable", UNAVAILABLE, {"E": 3600.0, "T": None, "B": 15900.0}),
    ({"Eb": "line", "E": None, "Tb": 14500.0}, "replay-unavailable", UNAVAILABLE,
     {"Eb": 14400.0, "E": None, "mb": 10.0, "B": 36600.0}),
    ({"T": ("Mathlib.Foo", None)}, "replay-unavailable", UNAVAILABLE, {"constant": "Mathlib.Foo"}),
    ({"E": 30000.0, "T": 30100.0}, "replay-unavailable", UNAVAILABLE, {"B": 15900.0}),
    ({"E": 30000.0, "T": 30100.0, "Tb": 620.0}, "cap-reset",
     {"replay_cap_s": 45000, "replay_cap_rule": "reset", "independent_check": "available"}, {"m": 0, "P": 30000.0}),
    ({"E": 30000.0, "T": 32000.0, "Tb": 620.0}, "cap-reset",
     {"replay_cap_s": 50400, "replay_cap_rule": "reset", "cut_n": 102, "independent_check": "available"},
     {"m": 200.0, "N": 102}),
    ({"T": 4100.0}, "rescope",
     {"replay_cap_s": 50400, "replay_cap_rule": "rescope", "cut_n": 792, "independent_check": "available"},
     {"P": 53600.0, "N": 792}),
    ({"T": 3880.0}, "default",
     {"replay_cap_s": 47400, "replay_cap_rule": "max(12h,1.5P)", "independent_check": "available"},
     {"m": 28.0, "P": 31600.0, "mean_compile_s": 37 / 3}),
    ({"T": 3780.0}, "default",
     {"replay_cap_s": 43200, "replay_cap_rule": "max(12h,1.5P)", "independent_check": "available"}, {"m": 0}),
    ({"M": 0}, "default", {"replay_cap_s": 43200, "replay_cap_rule": "max(12h,1.5P)", "independent_check": "available"},
     {"M": 0, "m": 20.0, "mb": 20.0, "P": 23600.0, "B": 30900.0}),
    ({"T": 3960.0}, "default",
     {"replay_cap_s": 50400, "replay_cap_rule": "max(12h,1.5P)", "independent_check": "available"}, {"P": 39600.0}),
    ({"T": "killed", "Tb": 1000.0}, "replay-unavailable", UNAVAILABLE | {"cut_n": 825}, {"B": 60900.0, "N": 825}),
], ids=["test_outcome_replay_unavailable_no_return", "test_outcome_replay_unavailable_build_line",
        "test_outcome_replay_unavailable_unresolved_rejection", "test_outcome_replay_unavailable_fit",
        "test_outcome_cap_reset", "test_reset_branch_P_over_14h_rescope", "test_outcome_rescope_N",
        "test_outcome_default_cap", "test_noise_rule_m_zero", "test_m_zero_members_uses_slowest_pair",
        "test_single_night_cap", "test_build_rescope_on_replay_unavailable"])
def test_one_gate_line_per_outcome(ready, figures, outcome, sets, expect):
    """From recorded figures alone, with S = 1000 and the 14-hour ceiling, the projection takes the first outcome that
    applies. Recording it writes the constants that outcome sets, then a rescope line where it cuts the sample, then
    exactly one d14-outcome line carrying the outcome, its reason and every figure labelled extrapolated, then the
    d14 line; the projection is kept beside the measurements, labelled extrapolated too."""
    # covers: test_truncated_run_never_computes_E_T, test_build_line_4h_stands_in, test_cap_clamped_14h,
    # covers: test_projection_labelled_extrapolated
    pol, consts = ready()
    found = measure.project(measured(pol.root, **figures), S, CEILING)
    assert found["outcome"] == outcome and expect.items() <= found.items()
    measure.record(pol, consts, found, TODAY)
    assert published(consts) == DEFAULTS | sets
    rows = [row[1:5] for row in gatefile.rows(pol)]
    assert [row[0] for row in rows] == ["rescope"] * ("cut_n" in sets) + ["d14-outcome", "d14"]
    assert rows[-2][1] == outcome and rows[-2][3].startswith(f"extrapolated: {found['reason']}; ")
    assert rows[-1][1:] == ("met", "pipeline", f"outcome={outcome}")
    assert "Mathlib.Foo" in rows[-2][3] if "constant" in expect else "constant=" not in rows[-2][3]
    kept = json.loads((pol.root / measure.DIR / "projection.json").read_text())
    assert kept == found | {"label": "extrapolated"}


def test_replay_memory_floor_is_peak_x1_25(ready):
    """The pilot replay's maximum resident set x 1.25 is the replay memory floor; 1.5 x the largest pilot leg peak
    the leg ceiling; 1.5 x the larger of the pilot aggregate's build and audit peaks the aggregate's; each in MiB,
    rounded up."""
    pol, consts = ready()
    measure.record(pol, consts, measure.project(measured(pol.root, T=3880.0), S, CEILING), TODAY)
    limits = constants.load(consts.repo).published["limits"]
    assert (limits["replay_memory_floor_mib"], limits["leg_memory_max_mb"], limits["agg_memory_max_mb"]) == (
        4883, 2930, 11719)


@pytest.fixture
def pilot_run(legs_run, code_repo, monkeypatch):
    """A pin run over `n` pairs, each a theorem under the header; each legacy probe only writes its line, the
    proof-1b timing gives 1.5 hours, and the preflight checks nothing."""
    monkeypatch.setattr(preflight, "CHECKS", ())
    monkeypatch.setattr(probes, "d14_proof1b_timing", lambda pol: 1.5 * H)
    for probe, line in (("d14_cache_probe", ("legacy-cache-probe", "serves")),
                        ("d14_legacy_collector", ("legacy-collector", "elaborates"))):
        monkeypatch.setattr(probes, probe, lambda pol, consts, logs, line=line:
                            gatefile.append(pol, *line, "pipeline", "recorded", TODAY))

    def make(n: int):
        run, pairs, lean = legs_run(n, ("pin",))
        run = dataclasses.replace(run, consts=dataclasses.replace(run.consts, repo=code_repo))
        shutil.copytree(REPO / "classifier", code_repo / "classifier")
        for pair in pairs:
            (run.work / "pairs" / f"{pair['pair_id']}.lean").write_text(theorem(pair["pair_id"]))
        return run, pairs, lean
    return make


def d14(run):
    return measure.d14(run.pol, run.consts, run.work, run.results, run.logs, TODAY)


def rejecting(name: str) -> dict:
    return {"exit": 1, "wall_s": 150.0,
            "output": f"replaying Aggregate with --fresh\nwhile replaying declaration '{name}':\n(kernel) mismatch\n"}


def test_T_M_from_rerun_toy_excluded(pilot_run, monkeypatch):
    """The run: the pilot is the pairs attempted before its 25-hour line. The baseline aggregate, the header over
    the toy entry alone, is built and replayed first; then the pilot aggregate, the toy and the clean pilot pairs,
    is built, audited and replayed. A replay rejecting a member makes it rejected-by-replay (d14-pilot) and removes
    it, and the one re-run over the rest gives T and M, the toy not counted. The three replays share the 24-hour
    line: the pilot's is what the baseline left, the re-run's what the pilot left. Each aggregate's calls log under
    its own label. Each legacy probe runs while its line is absent; the proof-1b timing is recorded with the
    figures. A run that ends without its outcome, for any cause, writes the d14 line unmet with that cause; once the
    outcome is recorded, the command refuses."""
    run, pairs, lean = pilot_run(5)
    with monkeypatch.context() as m, pytest.raises(LedgerStop):
        m.setattr(preflight, "CHECKS", (preflight._lock,))
        d14(run)  # a preflight refusal: this process holds no run lock
    with pytest.raises(FileNotFoundError):
        d14(run)  # no assembled.jsonl
    assert [row[1:5] for row in gatefile.rows(run.pol)[-4::3]] == [
        ("d14", "unmet", "pipeline", "LedgerStop: run lock: not held by this process"),
        ("d14", "unmet", "pipeline", f"FileNotFoundError: {gatefile.WITHHELD}")]
    (run.work / "assembled.jsonl").write_text("".join(json.dumps(pair) + "\n" for pair in pairs))
    lean.answers["compile"] = [{"wall_s": 9 * H}, {"wall_s": 9 * H, "exit": 1, "output": "error: unknown x"},
                               {"wall_s": 9 * H}]  # 27 hours by the third: the pilot stops there
    lean.answers["replay"] = [{}, {}, {"wall_s": 100.0}, rejecting("p2__p0"), {"wall_s": 120.0}]
    found = d14(run)
    d = run.pol.root / measure.DIR
    assert [p["pair_id"] for p in json.loads((d / "pairs.json").read_text())] == ["p0__p0", "p1__p0", "p2__p0"]
    assert json.loads((d / "proof1b.json").read_text()) == {"timing_s": 1.5 * H}
    assert [json.loads((d / f"{name}.json").read_text())["members"] for name in ("baseline", "pilot", "rerun")] == [
        [], ["p0__p0", "p2__p0"], ["p0__p0"]]
    assert (run.results / "membership.txt").read_text().splitlines()[1:] == ["p0__p0"]  # the walk's, per aggregate
    toy = (REPO / "fixtures/toy/Toy/Entry.lean").read_text()
    assert (run.pol.root / "env/pin/Aggregate.lean").read_text() == theorem("p0__p0") + "\n" + toy
    assert [s for s, _, _ in lean.calls][-8:] == ["build", "replay"] + ["build", "audit", "replay"] * 2
    assert [kw["log"].name for kw in lean.kwargs[-8:]] == [
        "aggregate-baseline-build.log", "aggregate-baseline-replay.log",
        *(f"aggregate-{name}-{step}.log" for name in ("pilot", "rerun") for step in ("build", "audit", "replay"))]
    assert [kw["timeout_s"] for kw in lean.kwargs[-8:]][1::3] == [24 * H, 24 * H - 100.0, 24 * H - 250.0]
    override = json.loads((run.results / "progress.json").read_text())["replay_overrides"][pairs[2]["pair_sha256"]]
    assert (override["source"], override["constant"]) == ("d14-pilot", "p2__p0")
    assert (found["E"], found["T"], found["M"], found["m"]) == (100.0, 120.0, 1, 20.0)
    rows = [row[1:3] for row in gatefile.rows(run.pol)]
    assert rows == [("d14", "unmet"), ("legacy-cache-probe", "serves"), ("legacy-collector", "elaborates"),
                    ("d14", "unmet"), ("d14-outcome", "default"), ("d14", "met")]
    with pytest.raises(LedgerStop, match="d14-outcome"):
        d14(run)
    assert [row[1:3] for row in gatefile.rows(run.pol)] == rows


@pytest.mark.parametrize("n, replays, outcome, M, removed", [
    (1, [{}, {}, rejecting("p0__p0")], "default", 0, {"p0__p0"}),
    (2, [{}, {}, {}, rejecting("p1__p0"), rejecting("p0__p0")], "replay-unavailable", 1, {"p1__p0", "p0__p0"}),
], ids=["only_member_rejected_no_rerun", "rerun_rejection_removed_unavailable"])
def test_pilot_rejections(pilot_run, n, replays, outcome, M, removed):
    """A pilot replay rejecting its only member leaves no re-run: M = 0, its rule giving m and mb. A member the one
    re-run rejects is removed as the first was, and the outcome is replay-unavailable. An earlier run's figures
    under measure/d14/ are gone before this run records its own."""
    run, pairs, lean = pilot_run(n)
    (run.work / "assembled.jsonl").write_text("".join(json.dumps(pair) + "\n" for pair in pairs))
    (d := run.pol.root / measure.DIR).mkdir(parents=True)
    (d / "rerun.json").write_text(json.dumps(aggregate(1, 600.0, 4000.0)))  # an earlier run's
    lean.answers["replay"] = replays
    found = d14(run)
    assert (found["outcome"], found["M"]) == (outcome, M) and (d / "rerun.json").exists() == (M > 0)
    by_id = {pair["pair_sha256"]: pair["pair_id"] for pair in pairs}
    overrides = json.loads((run.results / "progress.json").read_text())["replay_overrides"]
    assert {by_id[sha] for sha in overrides} == removed and {o["source"] for o in overrides.values()} == {"d14-pilot"}
    if M == 0:
        assert (found["m"], found["mb"]) == (1.0, 1.0)
    else:
        assert found["reason"] == "the pilot re-run rejected a member"


@pytest.mark.parametrize("answers, cause", [
    ({"build": [{}, {"exit": 1}]}, "the pilot aggregate's build exited 1 (killed None)"),
    ({"build": [{"exit": -9, "killed": "oom"}]}, "the baseline aggregate's build exited -9 (killed oom)"),
    ({"replay": [{}, {}, {"exit": -9, "killed": "oom"}]}, "the pilot aggregate's replay was killed for memory"),
], ids=["build_error", "build_oom", "replay_oom"])
def test_unmet_with_cause(pilot_run, answers, cause):
    """An aggregate build that errors or is killed for memory, or a replay killed for memory, ends the run with the
    d14 line unmet, its cause named, and no outcome."""
    run, pairs, lean = pilot_run(1)
    (run.work / "assembled.jsonl").write_text(json.dumps(pairs[0]) + "\n")
    lean.answers |= answers
    with pytest.raises(LedgerStop):
        d14(run)
    rows = gatefile.rows(run.pol)
    assert rows[-1][1:3] == ("d14", "unmet") and cause in rows[-1][4] and "d14-outcome" not in {r[1] for r in rows}


@pytest.mark.parametrize("pairs, limit", [
    ([("accepted", 100.0, 300.0, 1), ("elab-error", 900.0, None, 1), ("accepted", 200.0, 20.0, 1)],
     (1500, "5x-slowest-clean")),
    ([("elab-error", 100.0, None, 1), ("timeout-wall-clock", 300.0, None, 1)], (1800, "5x-slowest-any-floor-30min")),
], ids=["test_frozen_limit_5x_slowest_clean", "test_frozen_limit_fallback_floor_30min"])
def test_frozen_limit(tmp_path, pairs, limit):
    """D+21's per-pair limit is 5 x the slowest compile or replay wall-clock of a pilot pair that compiled clean;
    with none clean, 5 x the slowest pilot pair of any outcome, at least 30 minutes; the rule used is returned."""
    assert measure.frozen_limit(measured(tmp_path, pairs=pairs)) == limit


def test_empty_pilot_figures_stop(tmp_path):
    """M = 0 with no pilot pair's compile wall-clock, no pilot pair recorded at all, or a cut leaving fewer than one
    pair: a stop naming the cause."""
    with pytest.raises(LedgerStop, match="rescope: no cut fits, N=0"):
        measure.project(measured(tmp_path / "cut", E=28000.0, T=228000.0, Tb=600.0), S, CEILING)
    d = measured(tmp_path, M=0, pairs=[("timeout-wall-clock", None, None, None)])
    with pytest.raises(LedgerStop, match="M = 0 and no pilot pair"):
        measure.project(d, S, CEILING)
    (d / "pairs.json").write_text("[]")
    with pytest.raises(LedgerStop, match="no D[+]14 pilot pair"):
        measure.frozen_limit(d)
