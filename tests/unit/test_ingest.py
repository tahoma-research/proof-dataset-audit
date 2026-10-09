import dataclasses
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace

import pytest
from helpers import PY, REPO, in_unit

from ledger import cli, confine, constants, ingest
from ledger.types import LedgerStop

SUFFIX = constants.load(REPO).published["assembly"]["suffix_regex"]


def sha(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def body(name):
    """A fixture's JSON lines (its header comment lines start with #)."""
    lines = (REPO / f"fixtures/assembler/{name}.jsonl").read_text(encoding="utf-8").splitlines()
    return [json.loads(line) for line in lines if not line.startswith("#")]


def real(name):
    """The release record a fixture was re-serialised from."""
    return body(name)[0]


def entries(tmp_path, *records):
    """Ingest `records` as a release file, in order."""
    release = tmp_path / "release.json"
    release.write_text(json.dumps(list(records)), encoding="utf-8")
    return list(ingest.parse(release, SUFFIX))


def test_entries_keep_position_split_and_proof_digests(tmp_path):
    """Each entry carries its position in the file, the split field's own value (never a Hugging Face split
    name), the statement verbatim, and a digest of each proof element."""
    # covers: test_hash_and_position_recorded, test_split_is_field_value_not_hf_split, test_split_revision_unit_recorded
    proofless, bearing = real("proofless"), real("proof_bearing")
    first, second = entries(tmp_path, proofless, bearing)
    assert (first.position, first.split, first.proofs, first.element_sha256) == (
        0, "lean_workbook_plus", [], [])
    assert (second.position, second.split, second.decl) == (1, "lean_workbook", "lean_workbook_146")
    assert second.formal_statement == bearing["formal_statement"]
    assert second.element_sha256 == [sha(bearing["proof"][0].encode())] and second.refusal is None


def test_within_entry_exact_dedupe_first_kept(tmp_path):
    """Exact duplicate proof elements collapse to the first occurrence, order kept; the raw length is recorded."""
    record = real("proof_bearing") | {"proof": ["a", "b\nc", "a", "d", "b\nc"]}
    (entry,) = entries(tmp_path, record)
    assert (entry.proofs_raw, entry.proofs) == (5, ["a", "b\nc", "d"])
    assert entry.element_sha256 == [sha(p.encode()) for p in entry.proofs]


@pytest.mark.assembler
def test_decl_token_definition(tmp_path):
    """The name is the maximal run after the first whole-word theorem or lemma and whitespace, up to
    whitespace or ( ) { } [ ] :. The release's records give the accepted names; the shapes it lacks (`lemma`,
    `__`, `/` or NUL, a statement with no keyword or without the suffix, a `--` comment before the suffix) are
    SYNTHETIC statements that are refused, never dropped and never accepted."""
    # covers: test_double_underscore_refused
    real_entries = entries(tmp_path, real("proof_bearing"), real("proofless"))
    assert [(e.decl, e.refusal) for e in real_entries] == [
        ("lean_workbook_146", None), ("lean_workbook_plus_37430", None)]
    statements = body("synthetic_refusals")
    refused = entries(tmp_path, *(real("proof_bearing") | {"formal_statement": s} for s in statements))
    assert [(e.decl, e.refusal, e.formal_statement) for e in refused] == [
        ("a__b", "double-underscore", statements[0]), ("c__d", "double-underscore", statements[1]),
        (None, "no-decl", statements[2]), ("foo", "suffix-mismatch", statements[3]),
        ("a/b", "unsafe-name", statements[4]), ("a\0b", "unsafe-name", statements[5]),
        ("foo", "comment-before-suffix", statements[6])]


@pytest.mark.assembler
def test_name_collision_later_refused(tmp_path):
    """A name equal to an earlier record's is refused; the earlier record keeps it. A record refused for another
    reason keeps nothing: the same name later is accepted."""
    record = real("proof_bearing")
    assert [e.refusal for e in entries(tmp_path, record, record)] == [None, "name-collision"]
    refused = record | {"formal_statement": record["formal_statement"].replace("by sorry", "by simp")}
    assert [e.refusal for e in entries(tmp_path, refused, record)] == ["suffix-mismatch", None]


@pytest.mark.parametrize("edit", [
    pytest.param({"split": None}, id="null-split"),
    pytest.param({"split": ""}, id="empty-split"),
    pytest.param({"proof": None}, id="null-proof"),
    pytest.param({"proof": ["a", 1]}, id="non-string-element"),
    pytest.param({"formal_statement": 5}, id="non-string-statement"),
    pytest.param({"split": ...}, id="missing-split"),
    pytest.param({"formal_statement": ...}, id="missing-statement"),
    pytest.param({"proof": ...}, id="missing-proof"),
])
def test_record_with_wrong_field_type_fails(tmp_path, edit):
    """A record whose split, statement or proof is missing or has the wrong type (`...` deletes the field)
    stops ingest naming its position."""
    # covers: test_missing_any_of_three_fails
    record = {k: v for k, v in (real("proof_bearing") | edit).items() if v is not ...}
    with pytest.raises(LedgerStop, match="record 1: split must be"):
        entries(tmp_path, real("proof_bearing"), record)


def test_ingest_prints_dataset_sha(code_repo, make_policy, monkeypatch, capsys, tmp_path):
    """`ledger ingest` prints the dataset sha256 the fetch asserted, beside the revision."""
    # covers: test_hash_and_position_recorded
    release = tmp_path / "release.json"
    release.write_text(json.dumps([real("proof_bearing")]), encoding="utf-8")
    monkeypatch.setattr(cli, "REPO", code_repo)
    monkeypatch.setattr(confine, "apply_fs", lambda pol: None)  # in place of the real one, which would also confine this process
    monkeypatch.setattr(ingest, "fetch", lambda consts, pol: release)
    monkeypatch.setenv("TMPDIR", "/unused")  # cli.main rewrites TMPDIR; this makes monkeypatch restore it
    assert cli.main(["ingest", "--policy", str(make_policy())]) == 0
    assert "- result: exit 0\n" in next((tmp_path / "root/runs").glob("*/report.md")).read_text()
    assert f"sha256 {constants.load(REPO).source['sha256']}," in capsys.readouterr().out


def test_declared_toolchain_captured():
    """The publisher's declared toolchain is the recipe's `[declared]` block, verbatim, and is not the pin's."""
    consts = constants.load(REPO)
    assert consts.source["declared"]["lean"] == "leanprover/lean4:v4.8.0-rc1"
    assert consts.source["declared"]["lean"] != consts.env["pin"]["lean"]


def test_source_without_declared_block_refused(code_repo):
    """A source with no `[declared]` block is refused, never filled in with the pin's toolchain."""
    # covers: test_no_declaration_recorded_as_none
    path = code_repo / "recipe/source.toml"
    path.write_text(path.read_text().split("[declared]")[0])
    with pytest.raises(LedgerStop, match="declared"):
        constants.load(code_repo)


def test_bad_download_is_not_kept(ready, monkeypatch):
    """A download that does not match the recipe stops ingest and is removed, not left at the final name, so
    the next run fetches again. curl follows https alone, redirects included, and at most five redirects."""
    pol, consts = ready()
    served = [b"an error page served with 200"]

    def curl(argv, **_):
        assert " --proto =https --proto-redir =https --max-redirs 5 " in " ".join(argv)
        Path(argv[argv.index("--output") + 1]).write_bytes(served[0])
        return SimpleNamespace(exit=0, output="")
    monkeypatch.setattr(confine, "run", curl)
    with pytest.raises(LedgerStop, match="does not match the recipe"):
        ingest.fetch(consts, pol)
    assert list((pol.root / "dataset").iterdir()) == []
    served[0] = b"good"
    consts = dataclasses.replace(consts, source=consts.source | {"bytes": 4, "sha256": sha(b"good")[7:]})
    assert ingest.fetch(consts, pol).name == consts.source["file"]
    assert [p.name for p in (pol.root / "dataset").iterdir()] == [consts.source["file"]]


def test_sha_mismatch_stops(ready):
    """A dataset file on disk whose size or sha256 differs from the recipe stops ingest; the recipe's own
    file is accepted."""
    pol, consts = ready()
    data = b"release bytes"
    path = pol.root / "dataset" / consts.source["file"]
    path.parent.mkdir()
    consts = dataclasses.replace(consts, source=consts.source | {"bytes": len(data), "sha256": sha(data)[7:]})
    for altered in (b"release byteX", data[:-1]):
        path.write_bytes(altered)
        with pytest.raises(LedgerStop, match="does not match the recipe"):
            ingest.fetch(consts, pol)
    path.write_bytes(data)
    assert ingest.fetch(consts, pol) == path


def test_unreachable_source_stops(make_policy, code_repo, root):
    """A source that cannot be reached stops the fetch and leaves no dataset file."""
    script = (
        "import dataclasses, sys\nfrom pathlib import Path\n"
        "from ledger import constants, ingest, policy\nfrom ledger.types import LedgerStop\n"
        "pol, consts = policy.load(Path(sys.argv[1])), constants.load(Path(sys.argv[2]))\n"
        "url = consts.source['url'].replace('huggingface.co', 'unreachable.invalid')\n"
        "try:\n    ingest.fetch(dataclasses.replace(consts, source=consts.source | {'url': url}), pol)\n"
        "except LedgerStop as stop:\n    print(stop)\n")
    run = in_unit(PY, "-c", script, make_policy(), code_repo)
    assert run.code == 0 and run.out.startswith("ingest.fetch: curl exited"), run.err
    assert list((root / "dataset").iterdir()) == []
