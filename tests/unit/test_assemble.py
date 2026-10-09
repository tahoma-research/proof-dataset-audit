import hashlib
import json

import pytest
from helpers import REPO

from ledger import assemble, constants, frame, ingest, sample
from ledger.types import LedgerStop

pytestmark = pytest.mark.assembler
ASSEMBLY = constants.load(REPO).published["assembly"]
FIXTURES = REPO / "fixtures/assembler"
HEADER = "import Mathlib\nimport Aesop\nset_option maxHeartbeats 400000\nopen BigOperators Real Nat Topology Rat\n"
LEAN_WORKBOOK_146_P0 = HEADER + (
    "theorem lean_workbook_146__p0 : ∀ x : ℝ, cos (3 * x) = cos (2 * x + x) := by\n"
    "  intro x\n"
    "  ring_nf\n")
LEAN_WORKBOOK_PLUS_12768_P0 = HEADER + (
    "theorem lean_workbook_plus_12768__p0 :\n"
    "  ((∑ k in (Nat.divisors 768), k) / 768 - (∑ k in (Nat.divisors 384), k) / 384) = 1 / 192 := by\n"
    "  -- The key insight is that `768` and `384` are both powers of `2`, so we can use the formula\n"
    "  -- for geometric series to sum the divisors. `norm_cast` is used to normalize the numerical\n"
    "  -- expressions and perform the division.\n"
    "  \n"
    "  simp only [Nat.divisors, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]\n"
    "  norm_cast\n")


def sha(data: str | bytes) -> str:
    return "sha256:" + hashlib.sha256(data.encode() if isinstance(data, str) else data).hexdigest()


def fixture(name: str) -> tuple[list[str], list]:
    """A fixture's comment lines and its JSON values."""
    lines = (FIXTURES / f"{name}.jsonl").read_text(encoding="utf-8").splitlines()
    return [line for line in lines if line.startswith("#")], [json.loads(line) for line in lines if line[:1] != "#"]


def record(name: str) -> dict:
    return fixture(name)[1][0]


@pytest.fixture
def pair(build_frame):
    """Assemble pair k of the frame built from `record` alone, the draw's row naming the frame's digest for k
    unless `row` overrides it."""
    def assemble_one(record, k=0, **row):
        entry = build_frame(record).eligible[0]
        row = {"i": 0, "k": k, "position": 0, "pair_id": f"{entry.decl}__p{k}",
               "element_sha256": entry.element_sha256[k]} | row
        return assemble.assemble_pair(row, entry, ASSEMBLY)
    return assemble_one


def refusal_key(assembled) -> str:
    return sha(f"refused\t0\t0\t{assembled.element_sha256}")


def test_bytes_header_newline_no_blank_line_terminal_newline(pair):
    """# covers: test_single_proof_shape, test_every_line_indented_two, test_trailing_ws_stripped_one_space
    # covers: test_real_double_space_suffix_matches
    A real single-proof record ending `x)  :=  by sorry` assembles to the published header, then on its next
    byte the renamed statement, one space, `:= by`, a newline, every line of the element (the continuation
    line too) indented two spaces, and one terminal newline."""
    assert pair(record("proof_bearing")).text.encode() == LEAN_WORKBOOK_146_P0.encode()


def test_multiline_statement_body_verbatim(pair):
    """# covers: test_element_split_on_lf_trailing_lf_removed_empty_lines_indented, test_carriage_return_refused
    A real multi-line statement keeps its line break and indentation, losing only the three spaces before
    `:=`; the element's empty line is indented like every other. No element of the release ends in a newline
    or holds a carriage return or another line separator: on the real element, one trailing newline is
    removed, U+2028 splits nothing, and a carriage return is refused."""
    real = record("multiline_statement")
    assert pair(real).text.encode() == LEAN_WORKBOOK_PLUS_12768_P0.encode()
    first, *rest = real["proof"]
    edited = pair(real | {"proof": [first + "\u2028 \n\n", *rest]})
    assert edited.text == LEAN_WORKBOOK_PLUS_12768_P0[:-1] + "\u2028 \n  \n"
    refused = pair(real | {"proof": [first.replace("\n", "\r\n"), *rest]})
    assert (refused.refusal, refused.text, refused.pair_sha256) == ("carriage-return", None, refusal_key(refused))


@pytest.mark.parametrize("name", ["proof_bearing", "multiline_statement"])
def test_named_real_pair_digests(pair, name):
    """The pair digest a real fixture records is the digest of the text assembled from it."""
    comments, (real,) = fixture(name)
    ((pair_id, digest),) = [line.split()[2:] for line in comments if line.startswith("# pair_sha256 ")]
    assembled = pair(real, assemble.demangle(pair_id, ASSEMBLY["name_mangle"])[1])
    assert (assembled.pair_id, assembled.pair_sha256, sha(assembled.text)) == (pair_id, digest, digest)


def test_kth_element_after_dedupe(pair, build_frame):
    """# covers: test_element_digest_matches_frame, test_shifted_index_fails
    The derived fixture repeats its element 0 at index 1, so its list after dedupe is the release's own: pair
    1 carries the release's element 1, never raw element 1, and the digest of the element it carries is the
    frame's for that entry and index. A pair whose element is not the one the frame names stops the run."""
    derived = record("duplicate_element")
    raw, frame_digests = derived["proof"], build_frame(derived).eligible[0].element_sha256
    assembled = pair(derived, 1)
    assert assembled.text.endswith(":= by\n  rw [← sub_nonneg]\n  nlinarith [sq_nonneg (a * b - 4)]\n")
    assert assembled.element_sha256 == frame_digests[1] == sha(raw[2]) != sha(raw[1])
    with pytest.raises(LedgerStop, match="digest"):
        pair(derived, 1, element_sha256=frame_digests[0])


@pytest.mark.parametrize("name, text", [
    pytest.param("synthetic_one_space", LEAN_WORKBOOK_146_P0, id="test_synthetic_one_space_matches"),
    pytest.param("synthetic_by_in_body", HEADER + "theorem synthetic_by_in_body__p0 (h : 1 = 1 := by\n    rfl) : True"
                 " := by\n  intro x\n  ring_nf\n", id="test_by_in_body_assembles_unrefused"),
])
def test_synthetic_statement_assembles(pair, name, text):
    """A SYNTHETIC statement assembles unrefused: one whose suffix has one space where the release has two, to
    the same text; one whose body carries `:= by` and a newline, with the element placed after the declaration,
    never mistaken for a missing substitution."""
    (statement,) = fixture(name)[1]
    assert pair(record("proof_bearing") | {"formal_statement": statement}).text == text


@pytest.mark.parametrize("statement, refusal", [
    pytest.param("theorem foo : True := by simp", "suffix-mismatch", id="test_no_spacing_match_is_harness_error"),
    pytest.param("example : True := by sorry", "no-decl", id="test_no_theorem_token_is_harness_error"),
])
def test_unassemblable_statement_refused(pair, statement, refusal):
    """A SYNTHETIC statement the rule cannot assemble is refused with its cause and keyed by the refusal key;
    it has no text, so nothing is checked."""
    assert statement in fixture("synthetic_refusals")[1]
    refused = pair(record("proof_bearing") | {"formal_statement": statement})
    assert (refused.refusal, refused.text, refused.pair_sha256) == (refusal, None, refusal_key(refused))


def test_only_ascii_whitespace_is_whitespace(pair):
    """A no-break space is content: before `:=` the statement body keeps it, and after `sorry` the suffix does
    not match."""
    real = record("proof_bearing")
    kept = pair(real | {"formal_statement": real["formal_statement"].replace(")  :=", ")\u00a0  :=")})
    assert kept.text == LEAN_WORKBOOK_146_P0.replace(") :=", ")\u00a0 :=")
    assert pair(real | {"formal_statement": real["formal_statement"] + "\u00a0"}).refusal == "suffix-mismatch"


def test_open_inside_proof_unmoved(pair):
    """A command in a proof element, here a `section` and a `local instance` as an `open` would be, stays where its
    author wrote it, inside the indented proof; the header is the published one, unchanged."""
    assert pair(record("synthetic_scope_leak")).text == HEADER + (
        "theorem synthetic_scope_leak__p0 : (2 : ℕ) + 2 = 4 := by\n  norm_num\n  section\n"
        "  local instance : Add ℕ := ⟨Nat.add⟩\n")


def test_names_unique_and_demangle_roundtrip(build_frame, published, tmp_path):
    """# covers: test_header_byte_identical_pair_and_aggregate (pair half; the aggregate half is C8's)
    Every pair written for a draw over the real fixtures is the file its assembled line's digest names, begins
    with the published header byte for byte (the pinned heartbeat limit in it), and declares a name no other
    pair has, which the published de-mangling splits back into its entry's name and index. A drawn
    name-collision is a line keyed by its refusal key under its position's pair_id, and no file; work/pairs/
    holds this draw's texts alone."""
    collision = record("proof_bearing") | {"formal_statement": "theorem lean_workbook_146 : True := by sorry"}
    built = build_frame(*map(record, ("proof_bearing", "multiline_statement", "duplicate_element")), collision)
    work = tmp_path / "work"
    frame.write(built, work)
    drawn = sample.draw(built, published)
    (work / "pairs").mkdir()
    (work / "pairs" / "stale.lean").write_text("earlier run")
    digest, counts = assemble.write_pairs(drawn, built, ASSEMBLY, work)
    data = (work / "assembled.jsonl").read_bytes()
    lines = [json.loads(line) for line in data.splitlines()]
    assert digest == sha(data) and [line["i"] for line in lines] == list(range(6))
    assert counts == {None: 5, "name-collision": 1}
    assert ASSEMBLY["header"] == HEADER and f"set_option maxHeartbeats {ASSEMBLY['max_heartbeats']}\n" in HEADER
    names = []
    for line, row in zip(lines, drawn["draw"]):
        if line["refusal"]:
            assert (line["pair_id"], line["refusal"], line["pair_sha256"]) == (
                "#3__p0", "name-collision", sha(f"refused\t3\t0\t{row['element_sha256']}"))
            continue
        text = (work / "pairs" / f"{line['pair_id']}.lean").read_bytes()
        assert sha(text) == line["pair_sha256"] and text.startswith(HEADER.encode())
        names.append(ingest.DECL.search(text.decode()[len(HEADER):])[1])
        assert assemble.demangle(names[-1], ASSEMBLY["name_mangle"]) == (row["decl"], row["k"])
    assert len(set(names)) == len(names) == 5
    assert sorted(path.stem for path in (work / "pairs").iterdir()) == sorted(names)
    with pytest.raises(LedgerStop, match="not a pair name"):
        assemble.demangle("lean_workbook_146", ASSEMBLY["name_mangle"])


def test_disagreeing_inputs_stop(build_frame, published, tmp_path):
    """Nothing is assembled from a draw that is not of frame.json, from a frame.json that is not of
    entries.jsonl, or from a draw row naming a position outside the frame."""
    built, work = build_frame(record("proof_bearing")), tmp_path / "work"
    frame.write(built, work)
    drawn = sample.draw(built, published)
    for sample_, frame_, reason in (
            (drawn | {"frame_sha256": "sha256:" + "0" * 64}, built, "frame_sha256"),
            (drawn | {"draw": [drawn["draw"][0] | {"position": 1}]}, built, "outside the frame"),
            (drawn, build_frame(record("proof_bearing"), record("multiline_statement")), "not this frame")):
        with pytest.raises(LedgerStop, match=reason):
            assemble.write_pairs(sample_, frame_, ASSEMBLY, work)
    assert not (work / "pairs").exists() and not (work / "assembled.jsonl").exists()


def test_no_positive_fixture_is_synthetic():
    """Each assembler fixture names on line 1 the release record it was cut from, or is marked SYNTHETIC or
    DERIVED, and one alone is DERIVED. A fixture vouches for an assembled pair by recording its digest, and no
    SYNTHETIC fixture records one."""
    kinds = []
    for path in sorted(FIXTURES.glob("*.jsonl")):
        lines = path.read_text(encoding="utf-8").splitlines()
        kinds.append(lines[0].split(":")[0])
        assert kinds[-1] in ("# source", "# SYNTHETIC", "# DERIVED"), path.name
        assert kinds[-1] != "# SYNTHETIC" or not any(line.startswith("# pair_sha256 ") for line in lines), path.name
    assert kinds.count("# DERIVED") == 1
