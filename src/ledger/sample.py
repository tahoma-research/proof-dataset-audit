"""Sample: the seeded draw of pairs over a frame, as the published procedure states it."""

import platform
import random
from pathlib import Path

from ledger.frame import Frame
from ledger.types import Digest, LedgerStop, canonical, write_atomic


def draw(frame: Frame, published: dict) -> dict:
    """The sample.json content for `frame` under the recipe's published constants. One generator makes every
    call: first one `sample` of each entry's indices, entries in file order (an entry's pairs are those indices
    ascending), then one `sample` of the sample size over all those pairs in that order; the order it returns
    is the draw order. Stops unless this Python is the one the recipe pins."""
    sampling, mangle = published["sampling"], published["assembly"]["name_mangle"]
    per_entry = sampling["max_pairs_per_entry"]
    if platform.python_version() != sampling["python"]:
        raise LedgerStop(f"Python {platform.python_version()} is not the recipe's {sampling['python']}")
    rng = random.Random(sampling["seed"])
    pairs = [(e, k) for e in sorted(frame.eligible, key=lambda e: e.position)
             for k in sorted(rng.sample(range(len(e.proofs)), min(len(e.proofs), per_entry)))]
    chosen = rng.sample(pairs, min(sampling["sample_size"], len(pairs)))
    if sampling["cut_n"] > 0:
        chosen = chosen[:sampling["cut_n"]]
    return {
        "schema": "sample/1", "seed": sampling["seed"], "sample_size": sampling["sample_size"],
        "cut_n": sampling["cut_n"], "frame_sha256": frame.digest, "python": platform.python_version(),
        "drawable_frame_size": len(pairs), "distinct_entries": len({e.position for e, _ in chosen}),
        "draw": [{"i": i, "pair_id": mangle.format(decl=f"#{e.position}" if e.refusal else e.decl, k=k),
                  "decl": e.decl, "k": k, "position": e.position, "split": e.split,
                  "element_sha256": e.element_sha256[k]} for i, (e, k) in enumerate(chosen)],
    }


def write(sample: dict, work: Path) -> Digest:
    """Write sample.json under `work` and return its digest."""
    return write_atomic(work / "sample.json", canonical(sample))
