import json
import os
import re
import shutil
import subprocess

import pytest
from helpers import PY, in_unit, write_policy

from ledger import envbuild, gatefile
from ledger import policy as ledger_policy

pytestmark = [pytest.mark.integration, pytest.mark.slow]

# `ledger probe d7` with the recipe taken from the repository named second.
PROBE = ("import sys; from pathlib import Path; from ledger import cli; cli.REPO = Path(sys.argv[2]); "
         "sys.exit(cli.main(['probe', 'd7', '--policy', sys.argv[1]]))")


def test_d7_probe_in_dev_environment(dev_root, code_repo, tmp_path):
    """From a systemd user unit, over a scratch root holding the release file and elan: the probe installs both
    toolchains and records their digests, prints six conditions with evidence, writes its lines to the scratch
    gate file, and exits 0 only when all six are met; here podman's store lies outside the scratch root, so (a)
    may be unmet for that alone. With the legacy toolchain renamed to one that does not exist, (c) is unmet,
    the probe exits 2, and no Mathlib build has started."""
    root = dev_root / "tmp" / f"c5-d7-{os.getpid()}"
    for directory in ("dataset", "elan/bin"):
        (root / directory).mkdir(parents=True)
    shutil.copy(dev_root / "dataset/lean_workbook.json", root / "dataset")
    shutil.copy(dev_root / "elan/bin/elan", root / "elan/bin")
    policy = write_policy(tmp_path / "policy.toml", root)
    pol = ledger_policy.load(policy)

    def probe():
        run = in_unit(PY, "-c", PROBE, policy, code_repo, timeout=3000)
        found = {k: (state == "met", evidence) for k, state, evidence in
                 re.findall(r"^\(([a-f])\) (met|unmet): (.*)$", run.out, re.M)}
        assert list(found) == list("abcdef"), run.out + run.err
        return run.code, found, {row[1]: row[2:] for row in gatefile.rows(pol)}
    try:
        code, found, gates = probe()
        unmet = [k for k, (met, _) in found.items() if not met]
        assert unmet in ([], ["a"]) and "podman" in found["a"][1] if unmet else True, found
        assert code == (2 if unmet else 0)
        assert "replaying Toy.Entry with --fresh" in found["b"][1] and "Mathlib tag" in found["c"][1]
        recorded = json.loads((root / envbuild.TOOLCHAINS).read_text())
        assert recorded == {t.name: envbuild.toolchain_digest(t) for t in (root / "elan/toolchains").iterdir()}
        assert len(recorded) == 2 and "passed" in found["f"][1]
        assert gates["d7-frame"][0] == "measured" and gates["d7-sample"][0] == "drawn"
        assert "pairs=1000;" in gates["d7-sample"][2] and gates["d7"][0] == ("unmet: (a)" if unmet else "met")

        bogus = "leanprover/lean4:v0.0.0-nonexistent"
        (code_repo / "recipe/legacy/lean-toolchain").write_text(bogus + "\n")
        subprocess.run(["git", "-C", code_repo, "-c", "user.name=test", "-c", "user.email=test@example.invalid",
                        "commit", "-qam", "bogus legacy toolchain"], check=True)
        code, found, gates = probe()
        assert code == 2 and not found["c"][0] and f"elan toolchain install {bogus} exited" in found["c"][1]
        assert "c=unmet" in gatefile.rows(pol)[-1][4] and not (root / "env/pin/.lake/build").exists()
    finally:
        shutil.rmtree(root)
