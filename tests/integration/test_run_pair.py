import hashlib
import shutil
import subprocess
import tomllib

import pytest
from helpers import CLI, PY, REPO, in_unit, write_policy

from ledger import assemble, constants, frame, ingest, sample
from ledger.types import canonical

pytestmark = [pytest.mark.integration, pytest.mark.slow]

PAIR = "lean_workbook_42840__p9"  # `norm_num at *` over a sum of numerals: it compiles under the overlay's import


def published(dev_root, tmp_path):
    """A committed copy of the recipe, the classifier and the audit projects, its scope caps at 4 GiB, its summary
    naming the sample the published procedure draws from the release; and the digest of PAIR as the dev overlay's
    header assembles it."""
    repo = tmp_path / "published"
    for top in ("recipe", "classifier", "lean"):
        shutil.copytree(REPO / top, repo / top, ignore=shutil.ignore_patterns(".lake"))
    path = repo / "recipe/constants.toml"
    path.write_text(path.read_text().replace("leg_memory_max_mb = 12288", "leg_memory_max_mb = 4096")
                    .replace("agg_memory_max_mb = 24576", "agg_memory_max_mb = 4096"))
    consts = constants.load(repo)
    ingest.write(ingest.parse(dev_root / "dataset/lean_workbook.json", consts.published["assembly"]["suffix_regex"]),
                 work := tmp_path / "work")
    built = frame.build(work / "entries.jsonl", consts)
    drawn = sample.draw(built, consts.published)
    row = next(row for row in drawn["draw"] if row["pair_id"] == PAIR)
    header = tomllib.loads((dev_root / "dev-overlay.toml").read_text())["header"]
    entry = next(entry for entry in built.eligible if entry.position == row["position"])
    digest = assemble.assemble_pair(row, entry, consts.published["assembly"] | {"header": header}).pair_sha256
    (repo / "results").mkdir()
    (repo / "results/summary.json").write_text(
        f'{{"sample_sha256": "sha256:{hashlib.sha256(canonical(drawn)).hexdigest()}"}}\n')
    git = ["git", "-C", repo, "-c", "user.name=test", "-c", "user.email=test@example.invalid"]
    for args in (["init", "-q"], ["add", "."], ["commit", "-qm", "published"]):
        subprocess.run([*git, *args], check=True)
    return repo, digest


def test_one_pair_end_to_end_prints_digest_and_class(dev_root, tmp_path):
    """`ledger run --pair <digest>` from a systemd user unit over the development environment, the pair one of the
    dev sample assembled under the dev overlay: in a run directory of its own, the pin's toolchain installed, the
    release downloaded and redrawn as the published sample, the overlay's target fetched and built from source, and
    the pair's pin leg run; it prints the pair's digest, its pin outcome and its class."""
    repo, digest = published(dev_root, tmp_path)
    before = set(dev_root.glob("run-*"))
    try:
        run = in_unit(PY, "-c", CLI, repo, "run", "--pair", digest, "--policy",
                      write_policy(tmp_path / "policy.toml", dev_root), env={"LEDGER_DEV_ROOT": dev_root}, timeout=5400)
        assert run.code == 0, run.err[-3000:]
        assert run.out.endswith(f"pair_sha256 {digest}\npin outcome accepted\nclass reproduced\n"), run.out[-3000:]
    finally:
        for made in set(dev_root.glob("run-*")) - before:
            shutil.rmtree(made)
