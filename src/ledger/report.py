"""Reporting: the published records summarised into results/summary.json, rendered through templates/report/ into
the README and FINDING_REPORT.md, and indexed with every hash a reader needs in results/index.json. Every figure
comes from the records, the frame, the draw, the published constants and the recorded measurements; the prose
carries none of its own."""

import dataclasses
import hashlib
import json
import math
import re
import tomllib
from collections import Counter, defaultdict
from pathlib import Path

from ledger import REPO, classify, gatefile, preflight, progress, records, stage
from ledger.types import LedgerStop, canonical, write_atomic

MATHEMATICS = ("rejected-by-checker", "axiom-audit-failure", "rejected-by-replay")
ENVIRONMENT = ("environment-mismatch", "environment-undeclared")
UNRESOLVED = ("timed-out", "resource-exhausted", "harness-error", "unclassified")
EXCLUDED = {*ENVIRONMENT, *UNRESOLVED}  # out of both rates' denominators
PIN_DECIDED = {*UNRESOLVED, "rejected-by-replay", "reproduced"}  # classes the pin leg alone decides
SKEW = ("both", "pin-only", "declared-only", "fails-both", "unverifiable-declared")
CONFIDENCE, Z = 95, 1.959964  # the interval's level in percent, and its two-sided normal quantile
WINDOW_DAYS = 14  # the upstream authors' response window
TOOLCHAIN_FLOOR = "v4.33.1"  # the release that fixed the six kernel soundness bugs
REBUILD_ATTEMPTS = 3
RUN = "sh recipe/stranger.sh"  # the published procedure, from a clone's root
TEMPLATES = REPO / "templates/report"
CONTAINER = "recipe/policy/container.toml"  # the policy recipe/stranger.sh runs under, whose disk a reader provides
CHECKS = ("palomar-check", "independent-audit-check")
FULL_RUN = {"d44", "crosspass-d44", "aggregate-elab"}  # override sources the full run's own aggregate decides
TRIALS = {"d14-pilot", "d21-pilot", "crosspass-d21"}  # override sources a trial run before the full run decided


def _hours(seconds: float | None) -> float | int | None:
    return None if seconds is None else int(h) if (h := round(seconds / 3600, 1)).is_integer() else h


def _rate(numerator: int, denominator: int, sizes: list[int] | None = None) -> dict:
    """numerator ÷ denominator as a percentage. Given the countable cluster sizes (pairs per countable entry), also
    deff = Σm² ÷ Σm, their histogram, and the Wilson score interval at 95 %, nominal and with each half-width
    widened by √deff; defined at a zero numerator, absent at a zero denominator."""
    found = {"numerator": numerator, "denominator": denominator,
             "percent": round(100 * numerator / denominator, 2) if denominator else None}
    if sizes is None:
        return found
    deff = sum(m * m for m in sizes) / sum(sizes) if sizes else None
    found |= {"deff": deff and round(deff, 4), "cluster_sizes": {str(m): n for m, n in sorted(Counter(sizes).items())}}
    if denominator:
        n, p = denominator, numerator / denominator
        centre = (p + Z * Z / (2 * n)) / (1 + Z * Z / n)
        half = Z * math.sqrt(p * (1 - p) / n + Z * Z / (4 * n * n)) / (1 + Z * Z / n)
        found["confidence_percent"] = CONFIDENCE
        found["interval_percent"] = {name: [round(100 * max(0.0, centre - w), 2), round(100 * min(1.0, centre + w), 2)]
                                     for name, w in (("nominal", half), ("widened", half * math.sqrt(deff)))}
    return found


def _rates(recs: list[dict], countable, fails) -> dict:
    """The pair-level rate, failing pairs over countable pairs, with its interval; and the entry-level rate,
    countable entries every one of whose countable pairs fails over countable entries, an entry countable when
    one of its pairs is."""
    entries = defaultdict(list)
    for r in recs:
        if countable(r):
            entries[r["position"]].append(r)
    counted = [r for pairs in entries.values() for r in pairs]
    return {"pair": _rate(sum(map(fails, counted)), len(counted), [len(pairs) for pairs in entries.values()]),
            "entry": _rate(sum(all(map(fails, pairs)) for pairs in entries.values()), len(entries))}


def _pin_fails(r: dict) -> bool:
    return r["legs"]["pin"]["outcome"] in classify.FAILS | {"replay-reject"} or r["overrides"]["replay"] is not None


def _one(recs: list[dict], get, what: str):
    if len(found := {get(r) for r in recs} - {None}) > 1:
        raise LedgerStop(f"the records name more than one {what}: {sorted(found)}")
    return next(iter(found), None)


def subset(recs: list[dict]) -> list[tuple[str, str, str]]:
    """Each record's pair digest, class and axiom list, withdrawn records left out."""
    return [(r["pair_sha256"], r["class"], records.axioms(r["pair_id"], r["legs"]["pin"]["audit"]))
            for r in recs if r["withdrawn"] is None]


def canonical_subset(recs: list[dict]) -> str:
    """records.subset_sha256 over the records' subset."""
    return records.subset_sha256(subset(recs))


def framing(consts, rows: list[tuple]) -> str:
    """pin-only where the legacy environment is unavailable; else skew where the gate file holds a route-one line
    or a route-two line whose verdict is skew; else standard. Never from the rates or their interval."""
    if consts.published["status"]["legacy"] == "environment-unavailable":
        return "pin-only"
    if any(row[1] == "route-one" or row[1] == "route-two" and row[2] == gatefile.SKEW for row in rows):
        return "skew"
    return "standard"


def summarize(recs: list[dict], frame: dict, sample: dict, consts, measures: dict) -> dict:
    """summary.json's content from the records of the draw (each derived again from its own facts), the frame,
    the draw, the published constants and the measurements: the gate rows, the classifier table's and sample.json's
    sha256, and whichever of the membership, the replay, the environment builds and attempts, the projection and
    the rebuild attempts are recorded. Withdrawn records are left out of every count. Stops unless the records are
    the draw's pairs up to the published cut, in order, each with the draw's identity."""
    published, source, pin_env = consts.published, consts.source, consts.env["pin"]
    drawn = sample["draw"][:published["sampling"]["cut_n"] or None]
    if len(recs) != len(drawn) or any(canonical({k: r[k] for k in row}) != canonical(row)
                                      for r, row in zip(recs, drawn)):
        raise LedgerStop("the records are not the draw's pairs in sample.json, in order, up to the published cut")
    kept = [r for r in recs if r["withdrawn"] is None]
    pin_only = (shape := framing(consts, measures["gates"])) == "pin-only"
    classes = Counter(r["class"] for r in kept)
    pin_build, legacy_build = measures["pin_build"] or {}, measures["legacy_build"] or {}
    membership = measures["membership"]
    decided = {  # the pairs whose class differs from the one their pin leg alone gives
        r["pair_id"]: (r["overrides"]["replay"] or r["overrides"]["harness"])["source"] for r in kept
        if r["class"] in PIN_DECIDED and r["class"] != classify.derive(r["legs"]["pin"]["outcome"], None, None, None,
                                                                       "none")}
    container = tomllib.loads((consts.repo / CONTAINER).read_text())
    summary = {
        "schema": "summary/1", "public_name": published["public_name"], "publisher": published["publisher"],
        "framing": shape, "status": published["status"],
        "source": {key: source[key] for key in ("name", "repo", "revision", "file", "url", "bytes", "sha256",
                                                "record_unit", "licence", "declared")},
        "frame": {key: value for key, value in frame.items() if key not in ("schema", "entries_sha256", "eligible")},
        "frame_below_sample_size": frame["drawable_pairs"] < published["sampling"]["sample_size"],
        "seed": sample["seed"], "sample_sha256": measures["sample_sha256"],
        "sample_size": published["sampling"]["sample_size"],
        "max_pairs_per_entry": published["sampling"]["max_pairs_per_entry"],
        "cut_n": published["sampling"]["cut_n"], "pairs": len(kept),
        "distinct_entries": len({r["position"] for r in kept}),
        "split_counts": dict(sorted(Counter(r["split"] for r in kept).items())),
        "withdrawn": len(recs) - len(kept),
        "classes": {cls: classes[cls] for cls in sorted(classify.CLASSES)},
        "skew": None if pin_only else {case: sum(r["skew_case"] == case for r in kept) for case in SKEW},
        "skew_left_out": None if pin_only else sum(r["skew_case"] is None for r in kept),
        "mismatch_kernel_subcount": "not-computable" if pin_only else sum(r["mismatch_kernel_rejection"]
                                                                          for r in kept),
        "bound": sum(map(_pin_fails, kept)) if pin_only else (
            classes["environment-mismatch"] + classes["environment-undeclared"]  # each fails at the pin
            + sum(r["class"] == "rejected-by-replay" and (r["legs"]["legacy"] or {}).get("outcome") in classify.OK
                  for r in kept)),
        "environments": {
            "pin": {key: pin_env[key] for key in ("lean", "mathlib_tag", "mathlib_commit", "arch")} | {
                "recipe_id": _one(kept, lambda r: r["recipe_ids"]["pin"], "pin recipe"),
                "provenance": _one(kept, lambda r: r["provenance"], "provenance"),
                "artifact_set_digest": pin_build.get("artifact_set_digest"),
                "build_hours": _hours(pin_build.get("wall_s"))},
            "legacy": {"lean": source["declared"]["lean"], "mathlib": source["declared"]["mathlib"],
                       "check": "compilation and the axiom audit only",
                       "recipe_id": _one(kept, lambda r: r["recipe_ids"]["legacy"], "legacy recipe"),
                       "build_hours": _hours(legacy_build.get("wall_s")),
                       "attempts": [{"n": a["n"], "date": a["date"], "result": a["result"],
                                     "hours": _hours(a["wall_s"])} for a in measures["legacy_attempts"]]}},
        "membership": membership and {"members": membership["members"], "sha256": f"sha256:{membership['sha256']}"},
        "replay_hours": _hours(measures["replay_s"]),
        "replay_cap_hours": _hours(published["limits"]["replay_cap_s"]),
        "projection": measures["projection"],
        "rebuild_attempts": measures["rebuild"],
        "budgets_gb": published["budgets"],
        "reproduction": {"memory_mib": max(published["limits"][key] for key in preflight.CAPS),
                         "disk_gb": container["disk_floor_gb"] + container["disk_need_gb"]},
        "classifier": {"version": published["classifier"]["version"], "table_sha256": measures["table_sha256"]},
        "canonical_subset_sha256": canonical_subset(recs),
        "environment_axiom_reports": [
            {"pair_id": r["pair_id"], "axioms": sorted({a["name"] for d in r["legs"]["pin"]["audit"]["decls"]
                                                        for a in d["axioms_collector"] + d["axioms_walk"]}
                                                       - set(published["audit"]["allowlist"]))}
            for r in kept if r["legs"]["pin"]["outcome"] == "accepted-env-axiom"],
        "audit_disagreements": sum(any(leg and leg["audit_disagreement"] for leg in r["legs"].values())
                                   for r in kept),
        "checks": [{"date": row[0], "gate": row[1], "verdict": row[2], "reason": row[4]}
                   for row in measures["gates"] if row[1] in CHECKS],
        "listed": {cls: [r["pair_id"] for r in kept if r["class"] == cls] for cls in (*MATHEMATICS, *ENVIRONMENT,
                                                                                      *UNRESOLVED)},
        "decided_by_override": decided,
        "example_pair": next((r["pair_id"] for r in sorted(kept, key=lambda r: r["class"] != "reproduced")
                              if r["class"] in PIN_DECIDED and r["pair_id"] not in decided), None),
        "response_window_days": WINDOW_DAYS, "toolchain_floor": TOOLCHAIN_FLOOR,
    }
    if pin_only:  # no rate about the mathematics: the pin's own outcomes alone
        summary["pin_only_rates"] = _rates(kept, lambda r: r["legs"]["pin"]["outcome"] not in classify.NO_RESULT
                                           and r["overrides"]["harness"] is None, _pin_fails)
    else:
        summary["rates"] = _rates(kept, lambda r: r["class"] not in EXCLUDED, lambda r: r["class"] in MATHEMATICS)
    return summary


def _s(value) -> str:
    return "not recorded" if value is None else f"{value:,}" if isinstance(value, int) else str(value)


def _percent(rate: dict) -> str:
    return "undefined, with no counted unit" if rate["percent"] is None else f"{rate['percent']:.2f}%"


def _interval(rate: dict) -> str:
    if "interval_percent" not in rate:
        return "no interval, with no counted pair"
    (lo, hi), (wlo, whi) = rate["interval_percent"]["nominal"], rate["interval_percent"]["widened"]
    return (f"Wilson {rate['confidence_percent']}% interval {lo:.2f}% to {hi:.2f}%, widened for clustering to "
            f"{wlo:.2f}% to {whi:.2f}% (design effect {rate['deff']})")


def _table(head: tuple, rows: list) -> str:
    return "\n".join(["| " + " | ".join(head) + " |", "|" + "---|" * len(head),
                      *("| " + " | ".join(map(_s, row)) + " |" for row in rows)])


def render(summary: dict) -> dict[str, str]:
    """README.md and FINDING_REPORT.md from summary.json alone: the two documents of templates/report/, each slot
    filled with the block of text.toml.tmpl that the framing, the status and the recorded facts select, and every
    name in braces with a figure from the summary."""
    text = tomllib.loads((TEMPLATES / "text.toml.tmpl").read_text())
    shape, env, frame, source = summary["framing"], summary["environments"], summary["frame"], summary["source"]
    pin_only, rebuild = shape == "pin-only", [a["result"] for a in summary["rebuild_attempts"]]
    rates = summary["pin_only_rates" if pin_only else "rates"]
    legacy, membership = env["legacy"], summary["membership"]
    provenance = "cache-seeded" if summary["status"]["stop_loss"] else "from-source"
    checked = "unavailable" if summary["status"]["independent_check"] == "replay-unavailable" else "available"
    legacy_cost = text["legacy_cost"]["pending" if legacy["build_hours"] is None else "measured"].format(
        hours=_s(legacy["build_hours"]), gb=_s(summary["budgets_gb"]["legacy_env_gb"]))
    values = {
        "public_name": summary["public_name"], "publisher": summary["publisher"], "pairs": summary["pairs"],
        "distinct_entries": summary["distinct_entries"], "seed": str(summary["seed"]),
        "withdrawn": summary["withdrawn"],
        "repo": source["repo"], "revision": source["revision"], "file": source["file"], "bytes": source["bytes"],
        "sha256": source["sha256"], "record_unit": source["record_unit"], "licence": source["licence"]["spdx"],
        "licence_status": source["licence"]["status"], "licence_url": source["licence"]["stated_at"],
        "licence_verbatim": source["licence"]["verbatim"], "licence_traced": source["licence"]["traced_on"],
        "pin_lean": env["pin"]["lean"], "pin_mathlib": env["pin"]["mathlib_tag"],
        "pin_commit": env["pin"]["mathlib_commit"], "pin_arch": env["pin"]["arch"],
        "pin_hours": env["pin"]["build_hours"],
        "built": text["built"][provenance], "build_kind": text["build_kind"][provenance],
        "pin_cache": text["pin_cache"][provenance],
        "legacy_lean": legacy["lean"], "legacy_mathlib": legacy["mathlib"],
        "attempts": "; ".join(f"attempt {a['n']} on {a['date']}, {a['result']} after {a['hours']} hours"
                              for a in legacy["attempts"]) or "no attempt recorded",
        "replay_cap_hours": summary["replay_cap_hours"], "replay_hours": summary["replay_hours"],
        "window": summary["response_window_days"], "floor": summary["toolchain_floor"],
        "subcount": summary["mismatch_kernel_subcount"], "bound": summary["bound"],
        "disagreements": summary["audit_disagreements"], "example": summary["example_pair"], "command": RUN,
        "memory_mib": _s(summary["reproduction"]["memory_mib"]), "disk_gb": _s(summary["reproduction"]["disk_gb"]),
        "per_entry": summary["max_pairs_per_entry"],
        "skew_left_out": summary["skew_left_out"], "legacy_cost": legacy_cost,
        "run_legacy": "" if pin_only else text["full_run"]["declared"].format(cost=legacy_cost),
        "members": membership and membership["members"], "membership_hash": membership and membership["sha256"],
        "card": frame["card_count_lean_workbook"], "counted": frame["split_counts"]["lean_workbook"],
        "records_total": frame["records_total"],
        "split_values": ", ".join(f"`{split}` {n:,}" for split, n in frame["split_counts"].items()),
        "proof_bearing": frame["proof_bearing"], "proofless": frame["proofless_excluded"],
        "within": frame["within_entry_exact_duplicates_removed"], "elements": frame["proof_elements_raw"],
        "cross": frame["cross_entry_duplicates_removed"], "eligible": frame["eligible_entries"],
        "drawable_before": frame["drawable_pairs_before_cross_dedupe"], "drawable": frame["drawable_pairs"],
        "mean": frame["multiplier"]["mean"], "median": frame["multiplier"]["median"],
        "max": frame["multiplier"]["max"], "max_entry": frame["multiplier"]["max_entry"],
        "pair_numerator": rates["pair"]["numerator"], "pair_denominator": rates["pair"]["denominator"],
        "pair_percent": _percent(rates["pair"]), "pair_interval": _interval(rates["pair"]),
        "entry_numerator": rates["entry"]["numerator"], "entry_denominator": rates["entry"]["denominator"],
        "entry_percent": _percent(rates["entry"]),
        "class_table": _table(("class", "pairs"), [(f"`{cls}`", n) for cls, n in summary["classes"].items()]),
        "skew_table": summary["skew"] and _table(("case", "pairs"), [
            (label, summary["skew"][case]) for case, label in zip(SKEW, text["skew_labels"])]),
        "checks": "\n".join(f"- {c['date']}, `{c['gate']}`: {c['verdict']}. {c['reason']}"
                            for c in summary["checks"]),
        "reports": "\n".join(f"- `{r['pair_id']}`: {', '.join(f'`{a}`' for a in r['axioms'])}"
                             for r in summary["environment_axiom_reports"]),
        "figures": _table(("item", "value"), [
            ("`split` values in the sample", ", ".join(f"`{s}` {n:,}" for s, n in summary["split_counts"].items())),
            ("aggregate members", membership and membership["members"]),
            ("whole-environment replay, hours", "did not run" if checked == "unavailable" else summary["replay_hours"]),
            ("storage budgets", ", ".join(f"{v:,} GB for {text['budgets'][k]}"
                                          for k, v in summary["budgets_gb"].items()))]),
    }
    decided = summary["decided_by_override"]

    def reproduce(p: str, legacy_needed: bool) -> str:
        if (source := decided.get(p)) in TRIALS:
            return text["decided"][source]
        if source:
            return f"`{RUN}{'' if source in FULL_RUN else f' --pair {p}'}`: {text['decided'][source]}"
        return (f"`{RUN} --pair {p} --with-legacy`, which also builds the declared environment: {legacy_cost}"
                if legacy_needed else f"`{RUN} --pair {p}`")

    for cls, pairs in summary["listed"].items():
        values[cls] = _table(("pair", "reproduce"), [(f"`{p}`", reproduce(p, not pin_only and cls not in PIN_DECIDED))
                                                     for p in pairs]) if pairs else "No pair."

    def condition(name: str, holds) -> str:
        return text["conditions"][name] if holds else ""

    blocks = {
        "lead": text["lead"]["unavailable" if pin_only else "standing"],
        "verified": text["verified"][checked], "aggregate": text["aggregate"][checked],
        "unreplayed": text["verified"]["unavailable"] if checked == "unavailable" else "",
        "build_figure": text["build_figure"]["pending" if env["pin"]["build_hours"] is None else "measured"],
        "headline": text["headline"][shape], "skew": "" if pin_only else text["skew"],
        "rates": text["rates"]["pin-only" if pin_only else "classes"],
        "shortlist": text["shortlist"]["not-computable" if pin_only else "computable"],
        "declared": text["declared"]["unavailable" if pin_only else "standing"],
        "mathematics": text["mathematics"]["pin-only" if pin_only else "standing"],
        "finding_declared": text["finding_declared"]["unavailable" if pin_only else "standing"],
        "undeclared": text["undeclared"]["unavailable" if pin_only else "standing"],
        "full_run": text["full_run"][checked] if FULL_RUN & set(decided.values()) else "",
        "trial": condition("trial", TRIALS & set(decided.values())),
        "with_legacy": condition("with_legacy", not pin_only),
        "example": condition("example", summary["example_pair"]),
        "stop_loss": condition("stop_loss", summary["status"]["stop_loss"]),
        "divergent": condition("divergent", "artifact-divergent-outcome-match" in rebuild),
        "rebuild_failed": condition("rebuild_failed", rebuild.count("fail") >= REBUILD_ATTEMPTS),
        "outside": condition("outside", summary["checks"]),
        "env_reports": condition("env_reports", summary["environment_axiom_reports"]),
        "membership": condition("membership", membership),
        "replay": condition("replay", summary["replay_hours"] is not None),
        "whole_frame": condition("whole_frame", summary["frame_below_sample_size"]),
        "evidence": (TEMPLATES / "evidence.md").read_text().strip(),
    }
    fill = {key: _s(value) for key, value in values.items()}
    fill |= {key: block.format_map(fill) for key, block in blocks.items()}
    pages = {name: (TEMPLATES / f"{name}.tmpl").read_text().format_map(fill) for name in ("README.md",
                                                                                         "FINDING_REPORT.md")}
    return {name: re.sub(r"\n{3,}", "\n\n", page).strip() + "\n" for name, page in pages.items()}


def index(summary: dict, data: dict[str, bytes | None], image: dict | None) -> dict:
    """index.json (story 79): the source, the snapshot's hashes, each environment's identity, the convenience image
    recorded for the pin's (`image`, from measure/image.json, never evidence), the constants' and the classifier
    table's hashes; `data` holds the bytes of records.jsonl, summary.json, membership.txt (None where absent) and
    constants.toml."""
    digest = {name: blob and "sha256:" + hashlib.sha256(blob).hexdigest() for name, blob in data.items()}
    pin, legacy = summary["environments"]["pin"], summary["environments"]["legacy"]
    return {"source": {key: summary["source"][key] for key in ("url", "revision", "bytes", "sha256")},
            "snapshot": {"records_sha256": digest["records.jsonl"], "summary_sha256": digest["summary.json"],
                         "membership_sha256": digest["membership.txt"],
                         "canonical_subset_sha256": summary["canonical_subset_sha256"]},
            "environments": {"pin": {key: pin[key] for key in ("recipe_id", "artifact_set_digest", "provenance")}
                             | {"image": image and {"digest": image["digest"], "evidential": False}},
                             "legacy": legacy["recipe_id"] and {"recipe_id": legacy["recipe_id"]}},
            "constants_sha256": digest["constants.toml"], "classifier": summary["classifier"]}


def write(pol, consts, recs: list[dict], out: Path | None = None) -> dict[str, str]:
    """`report` over the records records.build gave: read the frame and draw under work/ (the draw's frame_sha256
    must be frame.json's) and the measurements under the root, then write records.jsonl, summary.json and
    index.json into `out`, the root's results/ by default, and README.md and FINDING_REPORT.md once the project has
    a public name and publisher (stage.names), removing an older snapshot's until then. Nothing is written unless
    all of it is made. Returns each written name's sha256."""
    results, root = pol.root / "results", pol.root
    out = out or results
    consts = dataclasses.replace(consts, published=consts.published | stage.names(pol, consts))
    frame_bytes, sample_bytes = (root / "work/frame.json").read_bytes(), (root / "work/sample.json").read_bytes()
    sample = json.loads(sample_bytes)
    if sample["frame_sha256"] != "sha256:" + hashlib.sha256(frame_bytes).hexdigest():
        raise LedgerStop("work/sample.json was not drawn from work/frame.json: its frame_sha256 differs")

    def read(rel: str):
        return json.loads(path.read_text()) if (path := root / rel).exists() else None

    progress, attempts = read("results/progress.json") or {}, read("measure/env-attempts.json") or {}
    aggregate = progress.get("aggregate", {})
    membership = results / "membership.txt"
    head = membership.read_text().split("\n", 1)[0] if membership.exists() else None
    seeded = consts.published["status"]["stop_loss"]
    measures = {
        "gates": gatefile.rows(pol),
        "table_sha256": "sha256:" + hashlib.sha256(
            (consts.repo / consts.published["classifier"]["table"]).read_bytes()).hexdigest(),
        "sample_sha256": "sha256:" + hashlib.sha256(sample_bytes).hexdigest(),
        "membership": head and {k: int(v) if k == "members" else v
                                for k, v in (f.split("=") for f in head.removeprefix("# ").split())},
        "replay_s": aggregate["last_replay"]["wall_s"] if aggregate.get("state") == "replay-returned" else None,
        "rebuild": progress.get("rebuild", {}).get("attempts", []),
        "pin_build": read(f"measure/build-{'pin-seeded' if seeded else 'pin'}.json"),
        "legacy_build": read("measure/build-legacy.json"), "legacy_attempts": attempts.get("legacy", []),
        "projection": read("measure/d14/projection.json"),
    }
    summary = summarize(recs, json.loads(frame_bytes), sample, consts, measures)
    data = records.dump(recs)
    summary_bytes = (json.dumps(summary, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode()
    files = {"records.jsonl": data, "summary.json": summary_bytes}
    if summary["public_name"] and summary["publisher"]:
        files |= {name: page.encode() for name, page in render(summary).items()}
    files["index.json"] = canonical(index(summary, {
        "records.jsonl": data, "summary.json": summary_bytes,
        "membership.txt": membership.read_bytes() if membership.exists() else None,
        "constants.toml": (consts.repo / "recipe/constants.toml").read_bytes()}, read("measure/image.json")))
    for name in ("README.md", "FINDING_REPORT.md"):
        if name not in files:
            (out / name).unlink(missing_ok=True)
    return {name: write_atomic(out / name, blob) for name, blob in files.items()}


def run(pol, consts, out: Path | None = None) -> dict[str, str]:
    """`report`: the records of the draw under work/, built from the leg results the progress file points at, the
    table the constants name and the withdrawals in `out`, the root's results/ by default, then written there by
    `write`. Returns each written name's sha256."""
    results, work = pol.root / "results", pol.root / "work"
    out = out or results
    drawn = (work / "sample.json").read_bytes()
    prog = progress.load(results / "progress.json", "sha256:" + hashlib.sha256(drawn).hexdigest())
    assembled = [json.loads(line) for line in (work / "assembled.jsonl").read_text().splitlines()]
    return write(pol, consts, records.build(json.loads(drawn), assembled, prog, results,
                                            classify.load(consts.repo, consts), consts, out / "withdrawals.jsonl"), out)
