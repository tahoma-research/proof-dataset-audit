import json
import re

import pytest
from helpers import PIN_ONLY_PAIRS, REPORT_PAIRS, section, summary_of

from ledger import report

ROUTE_ONE = ("2026-11-01", "route-one", "skew framing invoked", "pipeline", "21 of 30 pilot pairs")
CHECK = ("2026-11-20", "palomar-check", "policy unchanged", "assistant", "https://palomar.example.invalid/about")
BUILT = {"legacy_attempts": [{"n": 1, "date": "2026-10-15", "wall_s": 72000, "result": "ok"}],
         "legacy_build": {"wall_s": 72000}, "pin_build": {"wall_s": 30240}}
VARIANTS = {"standard": summary_of(REPORT_PAIRS), "skew": summary_of(REPORT_PAIRS, [ROUTE_ONE], BUILT),
            "pin-only": summary_of(PIN_ONLY_PAIRS, status={"legacy": "environment-unavailable"}, measures={
                "legacy_attempts": [{"n": n, "date": f"2026-10-1{n + 4}", "wall_s": 43200, "result": result}
                                    for n, result in ((1, "fail"), (2, "fail"), (3, "cap"))]}),
            "replay-unavailable": summary_of(REPORT_PAIRS, status={"independent_check": "replay-unavailable"})}
CONDITIONS = {  # the facts that make a conditional statement render, each over the standard framing
    "stop-loss": summary_of(REPORT_PAIRS, status={"stop_loss": True}),
    "divergent": summary_of(REPORT_PAIRS, measures={"rebuild": [{"n": 1, "date": "2026-11-03",
                                                          "result": "artifact-divergent-outcome-match"}]}),
    "rebuild-failed": summary_of(REPORT_PAIRS, measures={"rebuild": [
        {"n": n, "date": f"2026-11-0{n + 2}", "result": "fail"} for n in (1, 2, 3)]}),
    "checks": summary_of(REPORT_PAIRS, [CHECK]),
    "measured": summary_of(REPORT_PAIRS, measures={"pin_build": {"wall_s": 30240,
                                                                 "artifact_set_digest": "sha256:" + "d" * 64}}),
}
NUMBER = re.compile(r"(?<![\w.,])\d[\d,.]*")  # a figure, never the digits inside a name such as python3 or v4.8.0
SPELLED = re.compile(r"\b(?:two|three|four|five|six|seven|eight|nine|ten|eleven|twelve|\w+teen|twenty|thirty|"
                     r"forty|fifty|sixty|seventy|eighty|ninety|hundred|thousand)\b", re.IGNORECASE)


def numbers(text: str) -> set[float]:
    return {float(n.rstrip(".,").replace(",", "")) for n in NUMBER.findall(text)}


def readme(name: str) -> str:
    """The README rendered from the named summary, whitespace collapsed so that a statement reads across line wraps."""
    return " ".join(report.render(VARIANTS.get(name) or CONDITIONS[name])["README.md"].split())


S = ("standard",)
FLOOR = "Whether the kernel soundness bugs fixed in Lean v4.33.1 existed at the declared toolchain is not established."
STATEMENTS = [  # name, the summaries across which its text varies, the texts it holds or a test of the README
    ("integrity", ("standard", "pin-only"), lambda r: r.split(" ", 3)[3].startswith(
        "An evaluation-integrity check of a published proof corpus, and of how it reproduces across Lean versions")
     and "harm" not in r),
    ("compile_is_not_verification", S, ["Why compile success is not verification Compilation is not verification."]),
    ("reproduced_means_checks", S, ['"reproduced" means the proof checks, not that the statement says what its author '
                                    'intended']),
    ("reproducibility_not_soundness", S, ["Reproducibility is not soundness."]),
    ("declared_check_compilation_and_audit_only", S, ["declared revision is compilation plus the axiom audit only"]),
    ("cache_asymmetry", ("standard", "stop-loss"), ["At the pin it never stands in for building the statements under "
                                                    "audit, because downloaded build outputs are the publisher's own",
                                                    "At the declared revision the cache is permitted, because"]),
    ("replay_cap_is_a_budget", S, ["a cap of 12 hours of wall-clock. The cap is a schedule budget, not a prediction"]),
    ("shortlist_is_candidates", S, ["a shortlist of candidates for later cross-kernel checking, neither a finding nor "
                                    "a bound.", FLOOR]),
    ("shortlist_not_computable", ("pin-only",), ["the shortlist is not computable on this branch, which is not the "
                                                 "same as zero.", FLOOR]),
    ("image_not_evidence", S, ["is a convenience and not evidence"]),
    ("notice_is_a_courtesy", S, ["The notice is a courtesy, not a request for consent"]),
    ("clean_room_reproduction", S, ["by an agent that did not build the pipeline. It is not a third-party "
                                    "reproduction."]),
    ("artifact_set_divergent", ("divergent",), ["the artifact set did not reproduce byte for byte while the outcomes "
                                                "did"]),
    ("stop_loss_limitation", ("stop-loss",), lambda r: "**Cache-seeded limitation.** The from-source Mathlib build "
     "did not complete within its budget" in r and "built over dependency layers seeded from the upstream cache, its "
     "audited statements from source" in r and not re.search("built from source,|Mathlib build,|every Lake call", r)),
    ("outside_checks_cited", ("checks",), ["- 2026-11-20, `palomar-check`: policy unchanged. "
                                           "https://palomar.example.invalid/about"]),
    ("minimum_maintenance", S, ["## If development stops This snapshot stays as it is."]),
    ("procedure_cost_first", ("standard", "measured", "stop-loss"), lambda r: re.match(
        r"Reproducing even one pair first costs a [^`]*Mathlib build", section(r, "## Reproduce one pair "))
     and "From the root of a clone of this repository, `sh recipe/stranger.sh --pair <pair_id>`" in r),
    ("invitation_to_reproduce", S, ["Any reader is invited to reproduce any one pair with this published command"]),
    ("rebuild_all_failed", ("rebuild-failed",), ["publishes the recipe plus the artifact manifest, with the "
                                                 "divergence recorded, and exact reproducibility of the environment "
                                                 "moves to a later phase"]),
    ("network_claim", S, ["the build step can open no socket of any kind",
                          "Only the separate fetch steps reach the network, over TCP."]),
    ("reconciliation_beside_card", S, lambda r: "The card states 57,231 records with the `split` value "
     "`lean_workbook`, against 57,321 counted in the file; the counted `split` values (`lean_workbook` 57,321, "
     "`lean_workbook_plus` 82,893) sum to the file's 140,214 records" in r
     and "check" not in section(r, "The source is ").split("###")[0]),
    ("residual_forged_errors", S, ["can print forged `error:` lines", "That moves pairs only into a class excluded "
                                                                      "from both rates"]),
    ("residual_single_member_kill", S, ["a risk to finishing, never a false verification"]),
]


@pytest.mark.parametrize("names, check", [pytest.param(names, check, id=f"test_readme_required_statement_{name}")
                                          for name, names, check in STATEMENTS])
def test_readme_required_statement(names, check):
    """Every statement the README must carry renders, in plain words, from each summary across which its text
    varies; one the standard framing does not carry renders where its fact is recorded and not there."""
    def holds(r: str) -> bool:
        return bool(check(r)) if callable(check) else all(text in r for text in check)
    for name in names:
        assert holds(readme(name)), name
    assert "standard" in names or not holds(readme("standard"))


def test_readme_names_from_constants():
    """The public name and the publisher come from the summary, which takes them from recipe/constants.toml; the
    templates name neither."""
    other = VARIANTS["standard"] | {"public_name": "Another Audit", "publisher": "Another Organisation"}
    page = report.render(other)["README.md"]
    assert page.startswith("# Another Audit\n") and "Another Organisation re-checked" in page
    assert not any("Example" in path.read_text() for path in report.TEMPLATES.iterdir())


def test_all_framings_render():
    """Every framing and the replay-unavailable variant render with no unfilled marker and whole tables, the same
    bytes each time; the skew and pin-only framings lead with the method and the table, never with a rate; beside
    the skew table stands the count of pairs left out of it, and the skew framing states what the declared
    environment cost; and the replay-unavailable variant says verified only to call no pair so, never says that the
    whole-environment replay runs, and its finding report says the replay did not run."""
    for name, summary in VARIANTS.items():
        pages = report.render(summary)
        assert pages == report.render(summary)
        for page in pages.values():
            assert not re.search(r"\$|\{\{|\{[\w-]+\}|None", page), name
            for table in re.findall(r"(?:^\|.*\n)+", page, re.MULTILINE):
                assert len({line.count("|") for line in table.splitlines()}) == 1, (name, table)
        lead = "".join(pages["README.md"].split("\n\n")[1:3])
        rated = name in ("standard", "replay-unavailable")
        assert ("%" in lead) == ("The mathematical non-reproduction rate" in lead) == rated, name
        text, replayed = " ".join(" ".join(pages.values()).split()), name != "replay-unavailable"
        assert ("verified" in text.lower().replace("no pair is called verified", "")) == replayed, name
        assert ("replays once" in text) == replayed, name
        assert ("replay did not run" in pages["FINDING_REPORT.md"]) != replayed, name
        assert ("Pairs not in the table, for want of a result at the pin or of a check at the declared revision: 4."
                in text) == (name != "pin-only"), name
    assert "build attempts, each with its wall-clock: attempt 1 on 2026-10-15, ok after 20 hours." in readme("skew")
    assert "takes `--with-legacy`, which builds that environment too: its build took 20 hours here" in readme("skew")


def test_pin_only_denominator_label():
    """The pin-only entry rate names its denominator as the pin-countable entries, never the entries represented."""
    r = readme("pin-only")
    assert "Entry level: 2 of 3 pin-countable entries fail at the pin, 66.67%." in r and "represented" not in r


def test_every_rendered_number_traces_to_the_context():
    """Every figure in the rendered pages is a figure of summary.json, in every framing and condition, whatever its
    thousands separators and trailing zeros, and none is spelled out; the templates carry none of their own, except
    the cited evidence paragraph, which is the same in every snapshot."""
    # covers: test_templates_carry_no_numerals_of_their_own
    evidence = " ".join((report.TEMPLATES / "evidence.md").read_text().split())
    for path in report.TEMPLATES.iterdir():
        if path.name != "evidence.md":
            assert not NUMBER.findall(re.sub(r"\{[\w-]+\}", "", path.read_text())), path.name
    for summary in [*VARIANTS.values(), *CONDITIONS.values()]:
        figures = numbers(json.dumps(summary))
        for page in report.render(summary).values():
            text = " ".join(page.split()).replace(evidence, "")
            assert numbers(text) <= figures and not SPELLED.search(text)


def test_environment_classes_neutral_language():
    """The finding report's environment-class section never says error, wrong, bug or incorrect, in any framing, and
    attributes no cause to an environment-undeclared pair."""
    for summary in VARIANTS.values():
        found = " ".join(section(report.render(summary)["FINDING_REPORT.md"], "## About the environment").split())
        assert not re.search(r"error|wrong|bug|incorrect", found, re.IGNORECASE)
        assert "no comparison with the declared revision exists" in found and "so no cause is attributed" in found
