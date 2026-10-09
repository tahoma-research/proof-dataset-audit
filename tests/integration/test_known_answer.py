import hashlib

import pytest
from helpers import REPO

from ledger import constants, frame, sample

pytestmark = [pytest.mark.integration, pytest.mark.assembler]


def test_known_answer_seed0(dev_root):
    """The independent reference computation of the draw, on the real release, at the published seed."""
    consts = constants.load(REPO)
    out = sample.draw(frame.build(dev_root / "work/entries.jsonl", consts),
                      consts.published | {"sampling": consts.published["sampling"] | {"seed": 0}})
    assert (out["drawable_frame_size"], out["distinct_entries"]) == (18026, 966)
    pairs = [(p["decl"], p["k"]) for p in out["draw"]]
    assert pairs[:5] == [("lean_workbook_8241", 6), ("lean_workbook_plus_17739", 4), ("lean_workbook_15515", 11),
                         ("lean_workbook_plus_73903", 16), ("lean_workbook_50571", 7)]
    lines = "".join(f"{d}\t{k}\n" for d, k in pairs)
    assert hashlib.sha256(lines.encode()).hexdigest() == "521e35c1a407d114b49d9303af678bb758c91be298284d5e1a41331993e0a3db"
