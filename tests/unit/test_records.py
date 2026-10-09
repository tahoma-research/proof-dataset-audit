import hashlib
import json
import shutil

import pytest
from helpers import FRAME, REPLAY, REPO, WITHDRAWN, built

from ledger import cli, confine, constants, privacy, records, report, stage
from ledger.types import LedgerStop, canonical

KILLED = {"outcome": "unclassified", "table_row": None, "diagnostic": "no outcome: run killed", "compile": None,
          "replay": None, "audit": None, "audit_disagreement": False}


def pin(line: dict, **fields) -> dict:
    """A record line with its pin leg's `fields` replaced."""
    return line | {"legs": line["legs"] | {"pin": line["legs"]["pin"] | fields}}


def forged(line: dict, cls: str, **fields) -> dict:
    """`line` with its pin leg's `fields` replaced and the class, skew case and kernel flag made to agree, the
    pair out of the aggregate: a forgery consistent everywhere the leg's own facts are not read."""
    return pin(line, **fields) | {"class": cls, "skew_case": None, "mismatch_kernel_rejection": False,
                                  "aggregate": {"member": False, "removed_cause": None, "fresh": "not-run"}}


def oom(line: dict, attempts: int) -> dict:
    """`line`'s pin leg forged to an oom at `attempts`, everything the leg's facts give made to agree."""
    leg = line["legs"]["pin"]
    return forged(line, "resource-exhausted", outcome="oom", table_row="any.oom", attempts=attempts,
                  compile=leg["compile"] | {"oom_kill": 1})


def unmatched(line: dict, attempts: int) -> dict:
    """`line`'s pin leg forged to unclassified at `attempts`: its diagnostics no row's pattern matches."""
    leg = line["legs"]["pin"]
    return forged(line, "unclassified", outcome="unclassified", table_row="any.unmatched", attempts=attempts,
                  compile=leg["compile"] | {"diagnostics": "x"})


def fresh(line: dict, value: str) -> dict:
    return line | {"aggregate": line["aggregate"] | {"fresh": value}}


def override(line: dict, kind: str, **fields) -> dict:
    return line | {"overrides": line["overrides"] | {kind: (line["overrides"][kind] or {}) | fields}}


def test_schema_valid(leg_results):
    """Every record validates against the published schema."""
    jsonschema = pytest.importorskip("jsonschema")
    schema = json.loads((REPO / "docs/spec/schemas/record.schema.json").read_text())
    for record in built(leg_results)[0]:
        jsonschema.validate(record, schema)


def test_record_fields(leg_results):
    """Every record carries its derived class, skew case, kernel shortlist flag, aggregate status and withdrawal,
    whether each stage's output was truncated, and no absolute path; a pilot's replay override is not the
    aggregate's fresh replay rejecting the pair; a published cut leaves the pairs after it without a record."""
    # covers: test_no_absolute_paths
    found, _ = built(leg_results)
    member, out = {"member": True, "removed_cause": None, "fresh": "accepted"}, {"member": False, "removed_cause": None,
                                                                                 "fresh": "not-run"}
    assert [(r["class"], r["skew_case"], r["mismatch_kernel_rejection"], r["aggregate"], r["withdrawn"])
            for r in found] == [
        ("reproduced", "both", False, member, WITHDRAWN),
        ("environment-mismatch", "declared-only", True, out, None),
        ("harness-error", None, False, out, None),
        ("unclassified", None, False, out, None),
        ("rejected-by-replay", "declared-only", False,
         {"member": False, "removed_cause": "rejected-by-replay", "fresh": "rejected"}, None),
        ("rejected-by-checker", "fails-both", False, out, None),
        ("harness-error", None, False, out, None)]
    assert found[6]["legs"]["pin"]["diagnostic"].startswith("JSONDecodeError: ")
    assert report.canonical_subset(found) == report.canonical_subset(found[1:])  # the withdrawn first
    assert {env: {stage: leg[stage] and leg[stage]["output_truncated"] for stage in ("compile", "replay", "audit")}
            for env, leg in found[0]["legs"].items()} == {"pin": {"compile": True, "replay": False, "audit": False},
                                                         "legacy": {"compile": False, "replay": None, "audit": False}}
    assert not privacy.ROOTED.search(records.dump(found).decode())
    pilot, _ = built(leg_results, replay=REPLAY | {"source": "d14-pilot"})
    assert pilot[4]["aggregate"] == {"member": False, "removed_cause": "rejected-by-replay", "fresh": "not-run"}
    cut, _ = built(leg_results, status={"independent_check": "replay-unavailable"}, sampling={"cut_n": 2})
    assert [r["aggregate"]["fresh"] for r in cut] == ["replay-unavailable"] * 2


def test_from_records_reproduces_byte_for_byte_without_leg_files(leg_results, tmp_path, make_policy, monkeypatch,
                                                                  capsys):
    """`report --from-records`: the published records and table alone, with no leg result, progress file or draw
    present, derive every record again to the same bytes."""
    found, run = built(leg_results)
    (path := tmp_path / "records.jsonl").write_bytes(records.dump(found))
    shutil.rmtree(run.results)
    shutil.rmtree(run.work)
    assert records.from_records(path, run.table, run.consts) == path.read_bytes()
    monkeypatch.setattr(confine, "apply_fs", lambda pol: None)  # the real one would also confine this process
    assert cli.main(["report", "--from-records", str(path), "--policy", str(make_policy())]) == 0
    assert capsys.readouterr().out == (f"records.jsonl: every record derived again, byte for byte; "
                                       f"sha256:{hashlib.sha256(path.read_bytes()).hexdigest()}; canonical subset "
                                       f"{report.canonical_subset(found)}\n")


def test_report_writes_records(leg_results, make_policy, monkeypatch, capsys):
    """`report`, with no option, writes results/records.jsonl as records.build gives it from the draw, its
    assembled lines, the leg results and the progress file on disk, then summary.json and index.json from those
    records, the index holding the records' and the summary's sha256; README.md and FINDING_REPORT.md only once the
    project has a name, under the development overlay its stand-in, an older snapshot's removed until then. A
    second run writes the same bytes. The withdrawn record enters no count, and no replay figure stands once the
    last replay has not returned."""
    # covers: test_report_end_to_end, test_rerun_is_byte_identical
    found, run = built(leg_results)
    run.consts.published.update(public_name="", publisher="")  # the project unnamed, as before D+0 staging
    run.progress.data["sample_sha256"] = "sha256:" + hashlib.sha256((run.work / "sample.json").read_bytes()).hexdigest()
    run.progress.data["aggregate"]["last_replay"] = {"wall_s": 5400.0, "exit": 0, "rejected_constant": None}
    run.progress.save()
    monkeypatch.setattr(confine, "apply_fs", lambda pol: None)  # the real one would also confine this process
    (run.results / "README.md").write_text("an older snapshot's\n")
    load = constants.load
    monkeypatch.setattr(constants, "load", lambda repo: (c := load(repo), c.published.update(public_name="", publisher=""))[0])
    assert cli.main(["report", "--policy", str(make_policy())]) == 0
    written = {name: (run.results / name).read_bytes() for name in ("records.jsonl", "summary.json", "index.json")}
    assert written["records.jsonl"] == records.dump(found) and not (run.results / "README.md").exists()
    assert capsys.readouterr().out.splitlines() == [
        *(f"{name} sha256:{hashlib.sha256(data).hexdigest()}" for name, data in written.items()),
        "README.md and FINDING_REPORT.md not rendered: public_name or publisher empty in recipe/constants.toml"]
    index, summary = json.loads(written["index.json"]), json.loads(written["summary.json"])
    assert index["snapshot"]["records_sha256"] == "sha256:" + hashlib.sha256(written["records.jsonl"]).hexdigest()
    assert index["snapshot"]["summary_sha256"] == "sha256:" + hashlib.sha256(written["summary.json"]).hexdigest()
    assert (summary["publisher"], summary["replay_hours"], summary["pairs"], summary["withdrawn"]) == (
        "", 1.5, len(found) - 1, 1)
    assert summary["sample_sha256"] == run.progress.data["sample_sha256"]
    monkeypatch.setenv("LEDGER_DEV_ROOT", str(run.pol.root))
    (run.pol.root / "dev-overlay.toml").write_text('header = "import Lean\\n"\nbuild_targets = []\n')
    digests = report.write(run.pol, run.consts, found)  # a second cli.main here would meet this process's run lock
    assert list(digests) == ["records.jsonl", "summary.json", "README.md", "FINDING_REPORT.md", "index.json"]
    assert report.write(run.pol, run.consts, found) == digests
    run.progress.data["aggregate"]["state"] = "rejected-rerun-pending"
    run.progress.save()
    report.write(run.pol, run.consts, found)
    assert json.loads((run.results / "summary.json").read_text())["replay_hours"] is None
    assert json.loads((run.results / "summary.json").read_text())["publisher"] == stage.PLACEHOLDER


def redraw(work, draw) -> None:
    (work / "sample.json").write_text(json.dumps(json.loads((work / "sample.json").read_text()) | {"draw": draw}))


@pytest.mark.parametrize("edit, reason", [
    pytest.param(lambda found, work: (work / "frame.json").write_text(json.dumps(FRAME | {"seed": 1})),
                 "was not drawn from work/frame.json", id="test_context_derived_not_from_filename"),
    pytest.param(lambda found, work: redraw(work, [{"i": r["i"], **{k: r[k] for k in ("pair_id", "decl", "k",
                                                                                       "position", "split")},
                                                    "element_sha256": "sha256:" + "e" * 64} for r in found]),
                 "not the draw's pairs", id="records_of_another_draw"),
])
def test_report_refuses(leg_results, edit, reason):
    """The report reads the draw and the frame from work/, so a draw not from that frame, or records not that
    draw's, stop it, and nothing is written."""
    found, run = built(leg_results)
    edit(found, run.work)
    with pytest.raises(LedgerStop, match=reason):
        report.write(run.pol, run.consts, found)
    assert not any((run.results / name).exists() for name in ("records.jsonl", "summary.json"))


@pytest.mark.parametrize("edit, reason", [
    pytest.param(lambda lines: lines + lines[:1], "duplicate pair_id", id="test_duplicate_pair_fails"),
    pytest.param(lambda lines: [lines[0] | {"classifier_version": "v2"}, *lines[1:]], "classifier v2",
                 id="test_classifier_version_matches"),
    pytest.param(lambda lines: [lines[0] | {"class": "rejected-by-checker"}, *lines[1:]], "do not derive",
                 id="class_edited"),
    pytest.param(lambda lines: [lines[0], pin(lines[1], outcome="elab-error"), *lines[2:]], "the table derives",
                 id="outcome_edited"),
    pytest.param(lambda lines: [lines[0], pin(lines[1], table_row=None), *lines[2:]], "not a record/1",
                 id="no_row_without_diagnostic"),
    pytest.param(lambda lines: [lines[0], forged(lines[1], "unclassified", **KILLED, attempts=1), *lines[2:]],
                 "after 1 attempts", id="killed_shape_below_the_bound"),
    pytest.param(lambda lines: [lines[0], oom(lines[1], 1), *lines[2:]], "after 1 attempts", id="oom_below_the_bound"),
    pytest.param(lambda lines: [lines[0], unmatched(lines[1], 1), *lines[2:]], "after 1 attempts",
                 id="unclassified_below_the_bound"),
    *[pytest.param(lambda lines, n=n: [pin(lines[0], attempts=n), *lines[1:]], f"after {n!r} attempts",
                   id=f"attempts_{n!r}") for n in (0, 99, "1")],
    pytest.param(lambda lines: [lines[0], forged(lines[1], "harness-error", outcome="harness", table_row=None,
                                                 diagnostic="x", compile={k: v for k, v in lines[1]["legs"]["pin"][
                                                     "compile"].items() if k != "diagnostics"}), *lines[2:]],
                 "not a record/1", id="harness_leg_stage_key_deleted"),
    pytest.param(lambda lines: [*lines[:5], lines[5] | {"declared": "unavailable", "class": "environment-undeclared",
                                                        "skew_case": None,
                                                        "legs": lines[5]["legs"] | {"legacy": None},
                                                        "recipe_ids": lines[5]["recipe_ids"] | {"legacy": None}}],
                 "the legacy environment is", id="declared_unavailable_while_the_legacy_environment_stands"),
    pytest.param(lambda lines: [lines[0], forged(lines[1], "harness-error", outcome="harness", table_row=None,
                                                 diagnostic="JSONDecodeError: x"), *lines[2:]],
                 "the table derives", id="harness_leg_forged"),
    pytest.param(lambda lines: [lines[0], fresh(lines[1], "accepted"), *lines[2:]], "do not derive",
                 id="fresh_accepted_on_a_non_member"),
    pytest.param(lambda lines: [fresh(lines[0], "rejected"), *lines[1:]], "do not derive",
                 id="fresh_rejected_without_d44"),
    pytest.param(lambda lines: [*lines[:4], fresh(lines[4], "not-run"), *lines[5:]], "do not derive",
                 id="fresh_not_run_on_d44_rejection"),
    pytest.param(lambda lines: [*lines[:4], override(lines[4], "replay", at="0"), *lines[5:]], "not a record/1",
                 id="override_at_malformed"),
    pytest.param(lambda lines: [*lines[:4], override(lines[4], "replay", source="d30"), *lines[5:]],
                 "not a record/1", id="replay_override_source_unknown"),
    pytest.param(lambda lines: [override(lines[0], "harness", source="d30", detail="x", date="2026-12-01",
                                         at="2026-12-01T03:00:00Z"), *lines[1:]], "not a record/1",
                 id="harness_override_source_unknown"),
    pytest.param(lambda lines: [pin(lines[0], diagnostic="x"), *lines[1:]], "not a record/1",
                 id="diagnostic_on_a_leg_with_a_row"),
    pytest.param(lambda lines: [lines[1], lines[0], *lines[2:]], "draw order", id="lines_reordered"),
    pytest.param(lambda lines: [pin(lines[0], audit_disagreement=True), *lines[1:]], "do not derive",
                 id="audit_disagreement_edited"),
    pytest.param(lambda lines: [lines[0], lines[1] | {"aggregate": lines[1]["aggregate"] | {"member": True}},
                                *lines[2:]], "do not derive", id="aggregate_member_edited"),
    pytest.param(lambda lines: [lines[0] | {"declared": "Standing"}, *lines[1:]], "not a record/1",
                 id="declared_unknown"),
    pytest.param(lambda lines: [lines[0] | {"class": "verified"}, *lines[1:]], "not a record/1", id="class_unknown"),
    pytest.param(lambda lines: [lines[0] | {"legs": lines[0]["legs"] | {"pin": {
        k: v for k, v in lines[0]["legs"]["pin"].items() if k != "path_residue"}}}, *lines[1:]], "not a record/1",
                 id="leg_field_missing"),
    pytest.param(lambda lines: [pin(lines[0], compile={}), *lines[1:]], "not a record/1 record$",
                 id="stage_keys_missing"),
    pytest.param(lambda lines: [pin(lines[0], audit=lines[0]["legs"]["pin"]["audit"] | {"decls": [{}]}), *lines[1:]],
                 "a field is malformed", id="decl_malformed"),
    pytest.param(lambda lines: [lines[0] | {"withdrawn": {"x": 1}}, *lines[1:]], "not a record/1",
                 id="withdrawn_malformed"),
    pytest.param(lambda lines: [lines[0] | {"provenance": "verified"}, *lines[1:]], "not a record/1",
                 id="provenance_unknown"),
    pytest.param(lambda lines: [lines[0] | {"dev_overlay": False}, *lines[1:]], "not a record/1",
                 id="dev_overlay_false"),
    pytest.param(lambda lines: [lines[0] | {"legs": lines[0]["legs"] | {"legacy": lines[0]["legs"]["legacy"] | {
        "replay": lines[0]["legs"]["pin"]["replay"]}}}, *lines[1:]], "not a record/1", id="legacy_leg_replay_stage"),
    pytest.param(lambda lines: [lines[0], [1, 2], *lines[1:]], "not a record/1", id="line_a_list"),
    pytest.param(lambda lines: [lines[0], None, *lines[1:]], "not a record/1", id="line_null"),
    pytest.param(lambda lines: [pin(lines[0], compile=lines[0]["legs"]["pin"]["compile"] | {"x": 1}), *lines[1:]],
                 "not a record/1", id="stage_key_stray"),
    *[pytest.param(lambda lines, fact=fact: [lines[0], forged(lines[1], "harness-error", outcome="harness",
                                                              table_row=None, diagnostic="x", compile=lines[1]["legs"][
                                                                  "pin"]["compile"] | fact), *lines[2:]],
                   "a field is malformed", id=f"harness_leg_{next(iter(fact))}_mistyped")
      for fact in ({"oom_kill": "x"}, {"diagnostics": 5})],
    pytest.param(lambda lines: [pin(lines[0], replay=None), *lines[1:]], "not a record/1",
                 id="pin_accepted_replay_null"),
    pytest.param(lambda lines: [lines[0] | {"recipe_ids": lines[0]["recipe_ids"] | {"legacy": None}}, *lines[1:]],
                 "not a record/1", id="recipe_legacy_null_with_a_legacy_leg"),
    pytest.param(lambda lines: [*lines[:4], override(lines[4], "replay", source=["d44"]), *lines[5:]],
                 "not a record/1", id="override_source_a_list"),
    pytest.param(lambda lines: [*lines[:4], override(lines[4], "replay", date="2026-12-02"), *lines[5:]],
                 "not a record/1", id="override_date_vs_at"),
    pytest.param(lambda lines: [pin(lines[0], compile=lines[0]["legs"]["pin"]["compile"] | {"wall_s": float("nan")}),
                                *lines[1:]], "line 1: not JSON", id="number_nan"),
])
def test_from_records_refuses(leg_results, tmp_path, edit, reason):
    """Records that are not one derivation by this classifier, a pair twice or out of draw order, a class,
    outcome, audit disagreement or aggregate status the table and overrides do not give, a leg with no row that
    is neither killed at the attempt bound nor harness from audited declarations the table cannot read, a
    diagnostic on a leg with a row, a retryable outcome below the attempt bound or attempts out of its range, a
    declared status the constants contradict, or a record malformed, not an object, with a stage key missing or
    one the stage does not have, a replay on the legacy leg or none before the pin leg's audit, a legacy recipe
    without a legacy leg, a number that is NaN, or with an unknown declared status, class, provenance,
    withdrawal, overlay mark, override source or override time, or an override date not its time's, are refused
    rather than re-derived."""
    # covers: test_duplicates_rejected, test_class_leg_consistency
    found, run = built(leg_results)
    (path := tmp_path / "records.jsonl").write_bytes(b"".join(canonical(r) for r in edit(found)))
    with pytest.raises(LedgerStop, match=reason):
        records.from_records(path, run.table, run.consts)


def test_from_records_accepts_a_retryable_outcome_at_the_bound(leg_results, tmp_path):
    """The forgeries refused below the attempt bound are otherwise consistent: at the bound they derive again, the
    residual 04 § 8 states."""
    found, run = built(leg_results)
    for forgery in (oom, unmatched):
        lines = [found[0], forgery(found[1], 3), *found[2:]]
        (path := tmp_path / "records.jsonl").write_bytes(records.dump(lines))
        assert records.from_records(path, run.table, run.consts) == path.read_bytes()


def test_from_records_refuses_declared_standing_while_the_legacy_environment_is_unavailable(leg_results, tmp_path):
    """Records made while the legacy environment is unavailable derive again; one of them edited to a standing
    declared revision is refused."""
    found, run = built(leg_results, status={"legacy": "environment-unavailable"})
    (path := tmp_path / "records.jsonl").write_bytes(records.dump(found))
    assert records.from_records(path, run.table, run.consts) == path.read_bytes()
    path.write_bytes(records.dump([found[0] | {"declared": "standing"}, *found[1:]]))
    with pytest.raises(LedgerStop, match="the legacy environment is environment-unavailable"):
        records.from_records(path, run.table, run.consts)


def test_from_records_accepts_declared_none_while_the_legacy_environment_is_unavailable(leg_results, tmp_path):
    """Records made while the legacy environment is unavailable, one pair declared none, derive again; that pair
    with a legacy recipe and no legacy leg is refused."""
    found, run = built(leg_results, none=(1,), status={"legacy": "environment-unavailable"})
    assert [r["declared"] for r in found[:3]] == ["unavailable", "none", "unavailable"]
    (path := tmp_path / "records.jsonl").write_bytes(records.dump(found))
    assert records.from_records(path, run.table, run.consts) == path.read_bytes()
    path.write_bytes(records.dump([found[0], found[1] | {"recipe_ids": found[0]["recipe_ids"] | {"legacy": "x"}},
                                   *found[2:]]))
    with pytest.raises(LedgerStop, match="not a record/1"):
        records.from_records(path, run.table, run.consts)


def test_from_records_refuses_members_whose_fresh_replay_differs(leg_results, tmp_path):
    """The aggregate's fresh replay is one run: two members of one record set, one accepted by it and one not
    run, are refused."""
    found, run = built(leg_results, replay=None)
    assert [r["aggregate"]["fresh"] for r in found if r["aggregate"]["member"]] == ["accepted", "accepted"]
    (path := tmp_path / "records.jsonl").write_bytes(records.dump([*found[:4], fresh(found[4], "not-run"),
                                                                   *found[5:]]))
    with pytest.raises(LedgerStop, match="the aggregate's fresh replay"):
        records.from_records(path, run.table, run.consts)


@pytest.mark.parametrize("edit, reason", [
    pytest.param(lambda data: data.replace(b"\n", b"\n{not json\n", 1), "line 2: not JSON", id="not_json"),
    pytest.param(lambda data: b"[" * 100_000 + b"]" * 100_000 + b"\n" + data, "line 1: not JSON", id="nested_deep"),
    pytest.param(lambda data: data.replace(b"\n", b"\n\n", 1), "line 2: not JSON", id="empty_line"),
    pytest.param(lambda data: data[:-1], "line 7, p6__p0, do not derive", id="final_newline_missing"),
    pytest.param(lambda data: data.replace(b"\n", b"\r\n"), "line 1, p0__p0, do not derive", id="crlf"),
    pytest.param(lambda data: json.dumps(json.loads(data.splitlines()[0])).encode() + b"\n"
                 + b"".join(data.splitlines(keepends=True)[1:]), "line 1, p0__p0, do not derive",
                 id="line_not_canonical"),
])
def test_from_records_refuses_bytes(leg_results, tmp_path, edit, reason):
    """A line that is not JSON is refused by its number; bytes that differ where no record does name the first
    line that differs."""
    # covers: test_line_numbers_and_malformed_lines
    found, run = built(leg_results)
    (path := tmp_path / "records.jsonl").write_bytes(edit(records.dump(found)))
    with pytest.raises(LedgerStop, match=reason):
        records.from_records(path, run.table, run.consts)
