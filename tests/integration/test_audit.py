import os
import shutil
import tomllib
from pathlib import Path

import pytest
from helpers import run_legs

pytestmark = pytest.mark.integration

LIB = "audit_lib__p0"  # compiled first; the import cases use its axioms, through theorems, and its sorry
BODIES = {
    LIB: "axiom libAx : (3:ℕ) = 3\ntheorem libThm : (3:ℕ) = 3 := libAx\ntheorem libSorry : (4:ℕ) = 4 := by sorry\n"
         "axiom outerAx : Function.const ℕ True (sorryAx ℕ false)\ntheorem libOuter : True := outerAx\n"
         f"theorem {LIB} : (3:ℕ) = 3 := by\n  exact libThm\n",
    "own_axiom": "axiom ownAx : (1:ℕ) = 2\ntheorem own_axiom__p0 : (1:ℕ) = 2 := by\n  exact ownAx\n",
    "import_only": "theorem import_only__p0 : (3:ℕ) = 3 := by\n  exact libThm\n",
    "allowlist": "theorem allowlist__p0 (a b : ℝ) : a + b = b + a := by\n  exact add_comm a b\n",
    "sorry": "theorem sorry__p0 : (2:ℕ) = 2 := by\n  sorry\n",
    "sorry_import": "theorem sorry_import__p0 : (4:ℕ) = 4 := by\n  exact libSorry\n",
    "behind": "theorem behind__p0 : True := by\n  exact libOuter\n",
    "native": "theorem native__p0 : 2 + 2 = 4 := by\n  native_decide\n",
    "closure": "def closureHelper : (3:ℕ) = 3 := libAx\n"
               "theorem closure__p0 : (3:ℕ) = 3 ∧ (3:ℕ) = 3 := by\n  exact ⟨libThm, closureHelper⟩\n",
    "large": "theorem large__p0 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b + a := add_pos (mul_pos ha hb) ha\n",
}
IMPORTS = {"import_only", "sorry_import", "behind", "closure"}
LEGACY = set(BODIES) - {"import_only"}


@pytest.fixture(scope="module")
def audited(tmp_path_factory):
    """Every constructed pair compiled and audited at the pin and, all but one, at the declared revision, the
    library pair first in each; legs by (case, env)."""
    if not os.environ.get("LEDGER_DEV_ROOT"):
        pytest.skip("LEDGER_DEV_ROOT is unset: integration tests need the development environment")
    dev_root = Path(os.environ["LEDGER_DEV_ROOT"])
    header = tomllib.loads((dev_root / "dev-overlay.toml").read_text())["header"]
    cases = []
    for env in ("pin", "legacy"):
        for case, body in BODIES.items():
            if env == "pin" or case in LEGACY:
                name = case if case == LIB else f"{case}__p0"
                imports = f"import Pairs.{LIB}\n" if case in IMPORTS else ""
                cases.append((name, imports + header + body, env, {"assembly": {"header": imports + header}}))
    legs, scratch = run_legs(dev_root, tmp_path_factory.mktemp("audit"), cases)
    yield {(leg["pair_id"].removesuffix("__p0"), leg["env"]): leg for leg in legs}
    shutil.rmtree(scratch)


def walked(leg) -> dict:
    return {a["name"]: a for a in leg["audit"]["decls"][0]["axioms_walk"]}


@pytest.mark.parametrize("env", ["pin", "legacy"])
@pytest.mark.parametrize("case, outcome", [
    ("own_axiom", "audit-failure"), ("allowlist", "accepted"), ("sorry", "audit-failure"),
    ("sorry_import", "audit-failure"), ("behind", "audit-failure"), ("native", "audit-failure"),
    ("closure", "audit-failure"),
], ids=["test_own_file_axiom_fails", "test_allowlist_only_passes", "test_sorry_is_sorryax",
        "test_sorryax_via_import_is_own_bad", "test_axiom_behind_axiom_caught_by_walk",
        "test_native_decide_is_audit_failure", "test_via_own_is_closure_not_search_order"])
def test_audit_case(audited, case, outcome, env):
    """Each constructed pair reaches the outcome the axiom rules give, at both toolchains, by the paths below;
    every leg audits exactly its own declaration, so the audited count matches the count of accepted entries."""
    # covers: test_direct_sorry_via_own, test_count_matches_accepted
    leg = audited[case, env]
    assert leg["outcome"] == outcome, leg
    assert [d["name"] for d in leg["audit"]["decls"]] == [leg["pair_id"]]
    found, allow = walked(leg), {"propext", "Classical.choice", "Quot.sound"}
    collected = {a["name"] for a in leg["audit"]["decls"][0]["axioms_collector"]}
    if case == "own_axiom":
        assert found["ownAx"]["module"] is None
    elif case == "allowlist":
        assert set(found) <= allow and collected <= allow
    elif case == "sorry":  # :- by sorry: the declaration itself uses sorryAx
        assert found["sorryAx"]["via_own"] is True
    elif case == "sorry_import":  # reached only through an imported theorem, and a failure still
        assert found["sorryAx"]["via_own"] is False
    elif case == "behind":  # sorryAx, in the imported outerAx's type, reached only through the imported libOuter
        assert found["sorryAx"]["via_own"] is False and found["outerAx"]["module"] == f"Pairs.{LIB}"
        # At legacy the collector does not look inside an axiom's type, so the walk alone fails the pair.
        assert ("sorryAx" not in collected) is leg["audit"]["disagreement"] is (env == "legacy")
    elif case == "native":  # an own native_decide axiom at the pin; Lean.ofReduceBool used directly at legacy
        own = [n for n, a in found.items() if a["module"] is None and "_native" in n]
        assert own if env == "pin" else found["Lean.ofReduceBool"]["via_own"] is True
    elif case == "closure":  # libAx is reached through the imported libThm and the own closureHelper alike
        assert found["libAx"] == {"name": "libAx", "module": f"Pairs.{LIB}", "via_own": True}
        assert found["libAx"] in leg["audit"]["decls"][0]["axioms_collector"]  # the collector's entry says so too


def test_import_only_axiom_reported_env(audited):
    """An off-allowlist axiom reached only through an imported constant is reported against the environment,
    accepted-env-axiom, not against the entry."""
    leg = audited["import_only", "pin"]
    assert (leg["outcome"], leg["table_row"]) == ("accepted-env-axiom", "any.audit.env")
    assert walked(leg)["libAx"] == {"name": "libAx", "module": f"Pairs.{LIB}", "via_own": False}


@pytest.mark.parametrize("env", ["pin", "legacy"])
def test_walk_memoised_bound(audited, env):
    """On a proof through the reals' ordered-field lemmas, whose closure is large, the audit's wall-clock and peak
    are in the leg result, and the memoised walk takes at most five times the collector's time on the same
    declaration."""
    leg = audited["large", env]
    decl = leg["audit"]["decls"][0]
    assert leg["audit"]["wall_s"] > 0 and leg["audit"]["peak_mem_kb"] > 0
    assert 0 < decl["collector_us"] and decl["walk_us"] <= 5 * decl["collector_us"], decl
