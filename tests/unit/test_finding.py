from helpers import HARNESS, PIN_ONLY_PAIRS, REPLAYED, REPORT_PAIRS, section, summary_of

from ledger import report

SECTIONS = {"## About the mathematics": report.MATHEMATICS,
            "## About the environment": report.ENVIRONMENT, "## Not resolved": report.UNRESOLVED}


def test_named_output_factual_separates_math_from_env():
    """FINDING_REPORT.md lists every pair that did not reproduce under its class, the mathematics classes, the
    environment classes and the unresolved ones each in a section of their own, every pair with the command that
    reproduces it (with the declared environment where its class needs it), and states the response window in
    days; on the pin-only branch the one mathematics class kept is the pin kernel's replay rejection. A pair whose
    class a check over many pairs decided carries the full run with that check named, and the sentence saying what
    the full run does renders only beside such a pair, with no replay on the replay-unavailable branch; a pair a
    trial run before the full run decided names that trial and its gate line and carries no command; a command with
    the declared environment carries that build's cost, and the README offers one only where the declared
    environment stands; a pair whose two runs of its own pin check disagreed carries `run --pair` and the statement
    that running it twice and comparing reproduces the disagreement, and the cost of a command's first run is the
    environment as built, cache-seeded under the stop-loss; the README's example pair is one whose own pin leg
    decides its class, and with no such pair there is no example."""
    page = report.render(summary_of(REPORT_PAIRS))["FINDING_REPORT.md"]
    assert list(SECTIONS) == sorted(SECTIONS, key=page.index)
    assert "with a response window of 14 days" in page and "published beside this report, under `responses/`" in page
    seen = []
    for entry, cls, *_ in REPORT_PAIRS:
        pair, needs = f"e{entry}__p{seen.count(entry)}", cls not in report.PIN_DECIDED
        seen.append(entry)
        listed = f"| `{pair}` | `{report.RUN} --pair {pair}{' --with-legacy' * needs}`"
        for heading, classes in SECTIONS.items():
            assert (listed in section(page, heading)) == (cls in classes), (heading, pair)
    pin_only = report.render(summary_of(PIN_ONLY_PAIRS, status={"legacy": "environment-unavailable"}))
    mathematics = section(pin_only["FINDING_REPORT.md"], "## About the mathematics")
    assert "### `rejected-by-replay`" in mathematics and "rejected-by-checker" not in mathematics
    assert f"| `e2__p0` | `{report.RUN} --pair e2__p0` |" in section(pin_only["FINDING_REPORT.md"],
                                                                     "## About the environment")
    assert "which also builds the declared environment: it needs 120 GB of disk, and no build time is recorded" in page
    assert "--with-legacy" not in pin_only["README.md"] and "the full `run`" not in page and "none can" not in page
    pages = report.render(summary_of([(0, "rejected-by-replay", "accepted", "accepted", REPLAYED),
                                      (1, "harness-error", "accepted", "accepted", HARNESS), (2, "timed-out"),
                                      (3, "harness-error", "accepted", "accepted",
                                       {"harness": HARNESS["harness"] | {"source": "d21-rehearsal"}}),
                                      (4, "rejected-by-replay", "accepted", "accepted",
                                       {"replay": REPLAYED["replay"] | {"source": "d14-pilot"}}),
                                      (5, "harness-error", "accepted", "accepted",
                                       {"harness": HARNESS["harness"] | {"source": "crosspass-d21"}}),
                                      (6, "rejected-by-replay", "accepted", "accepted",
                                       {"replay": REPLAYED["replay"] | {"source": "d21-pilot"}}),
                                      (7, "harness-error", "accepted", "accepted",
                                       {"harness": HARNESS["harness"] | {"source": "aggregate-elab"}})],
                                     status={"stop_loss": True}))
    decided = " ".join(pages["FINDING_REPORT.md"].split())
    assert (f"| `e0__p0` | `{report.RUN}`: the whole-environment replay, which re-checks every passing pair "
            "together in one module, rejected it |") in decided
    assert (f"| `e1__p0` | `{report.RUN}`: checked together with the other passing pairs in one module, it gave a "
            "different result from its own check, a harness failure |") in decided
    assert (f"| `e3__p0` | `{report.RUN} --pair e3__p0`: its check at the pin gave different outcomes in the two "
            "trial runs before the full run, a harness failure; running this command twice and comparing the outcomes "
            "is what reproduces the disagreement |") in decided
    assert ("| `e4__p0` | In the first of two trial runs before the full run, which replayed the first sampled pairs "
            "that passed together in one module, that replay rejected it; no command re-creates that trial: the pair's "
            "own line in `results/records.jsonl` records the rejection, its constant and its date, and the trial is on "
            "its dated `d14-outcome` line in `gates/GATES.md` |") in decided
    assert "| `e5__p0` | In the second of two trial runs" in decided
    assert ("| `e6__p0` | In the second of two trial runs before the full run, which replayed the first sampled pairs "
            "that passed together in one module, that replay rejected it; no command re-creates that trial: the pair's "
            "own line in `results/records.jsonl` records the rejection, its constant and its date, and the trial is on "
            "its dated `d21-pilot` line in `gates/GATES.md` |") in decided
    assert (f"| `e7__p0` | `{report.RUN}`: it failed to compile together with the other passing pairs in one module, "
            "a harness failure |") in decided
    assert "from a clone of this repository, or the reason none can;" in decided
    assert ("the full `run`: it builds the pinned environment, checks every sampled pair there, builds the passing "
            "pairs together into one module and replays that module;") in decided
    unreplayed = report.render(summary_of([(0, "harness-error", "accepted", "accepted", HARNESS)],
                                          status={"independent_check": "replay-unavailable"}))
    assert ("checks every sampled pair there and builds the passing pairs together into one module, which this "
            "snapshot does not replay;") in " ".join(unreplayed["FINDING_REPORT.md"].split())
    assert "For example" not in unreplayed["README.md"]
    assert "its first run costs a Mathlib build over dependency layers seeded from the upstream cache" in decided
    assert "from source" not in decided and f"{report.RUN} --pair e2__p0\n" in pages["README.md"]
