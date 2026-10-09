"""The recipe: the source, the published constants and each environment's identity, loaded and checked;
and the recipe identifier, the content hash that names an environment."""

import hashlib
import os
import re
from dataclasses import dataclass
from pathlib import Path

from ledger.types import Digest, Env, LedgerStop, load_toml

SOURCE = {
    "schema": str, "name": str, "repo": str, "revision": str, "file": str, "url": str, "bytes": int,
    "sha256": str, "record_unit": str, "card_split_counts": {"lean_workbook": int},
    "licence": {"spdx": str, "stated_at": str, "verbatim": str, "traced_on": str, "status": str},
    "declared": {"lean": str, "mathlib": str, "stated_at": str, "verbatim": str},
}
PUBLISHED = {
    "schema": str, "public_name": str, "publisher": str,
    "assembly": {"header": str, "max_heartbeats": int, "suffix_regex": str, "name_mangle": str},
    "sampling": {"seed": int, "sample_size": int, "max_pairs_per_entry": int, "prng": str, "python": str,
                 "cut_n": int},
    "limits": {"per_pair_wall_clock_s": int, "per_pair_limit_status": str, "per_pair_limit_rule": str,
               "run_ceiling_s": int, "replay_cap_s": int, "replay_cap_rule": str, "attempt_bound": int,
               "memory_floor_gib": int, "swap_floor_gib": int, "replay_memory_floor_mib": int,
               "leg_memory_max_mb": int, "agg_memory_max_mb": int},
    "budgets": {"durable_gb": int, "pin_env_gb": int, "legacy_env_gb": int, "rebuild_gb": int},
    "audit": {"allowlist": [str]},
    "classifier": {"version": str, "table": str, "table_sha256": str, "status": str},
    "status": {"legacy": str, "independent_check": str, "stop_loss": bool},
}
PIN = {
    "schema": str, "role": str, "lean": str, "mathlib_tag": str, "mathlib_commit": str, "arch": str,
    "python": str, "lake_flags": [str], "env": {"MATHLIB_NO_CACHE_ON_UPDATE": str}, "cache": str,
    "build_procedure": str,
}
ENVS = {"pin": PIN, "pin-seeded": PIN, "legacy": PIN | {"env": {}}}


@dataclass(frozen=True)
class Constants:
    repo: Path
    source: dict
    published: dict
    env: dict  # Env -> that environment's env.toml

    def tree(self, env: Env) -> str:
        """The tree `env`'s work runs in: for the pin, the stop-loss's while it is in force."""
        return "pin-seeded" if env == "pin" and self.published["status"]["stop_loss"] else env


def _load(repo: Path, rel: str, shape: dict, schema: str) -> dict:
    data = load_toml(repo / rel, shape, rel)
    if data["schema"] != schema:
        raise LedgerStop(f"{rel}: schema is not {schema}")
    return data


def load(repo: Path) -> Constants:
    """Load the recipe under `repo`, refusing unknown keys, wrong types, an unpinnable source and a pin or
    stop-loss recipe whose Lake calls do not start `lake --no-cache` (confine.run refuses them too)."""
    source = _load(repo, "recipe/source.toml", SOURCE, "source/1")
    if not re.fullmatch(r"[0-9a-f]{40}", source["revision"]):
        raise LedgerStop("recipe/source.toml: revision is not 40 hex characters")
    if f"/resolve/{source['revision']}/" not in source["url"]:
        raise LedgerStop("recipe/source.toml: url does not resolve at the pinned revision")
    published = _load(repo, "recipe/constants.toml", PUBLISHED, "constants/1")
    header = published["assembly"]["header"]
    if not header.endswith("\n") or header.endswith("\n\n"):
        raise LedgerStop("recipe/constants.toml: header does not end in exactly one newline")
    env = {e: _load(repo, f"recipe/{e}/env.toml", shape, "env/1") for e, shape in ENVS.items()}
    for e in ("pin", "pin-seeded"):
        if env[e]["lake_flags"][:1] != ["--no-cache"]:
            raise LedgerStop(f"recipe/{e}/env.toml: lake_flags does not start with --no-cache")
    return Constants(repo, source, published, env)


def recipe_id(repo: Path, env: Env) -> Digest:
    """sha256 over one line "<path>\\t<sha256 of the file's bytes>\\n" per file under recipe/<env>/ and
    lean/audit-<env>/ (the pin's, for pin-seeded), paths relative to the repository and sorted, Lake's .lake/
    output excluded."""
    if not (repo / "recipe" / env).is_dir():
        raise LedgerStop(f"recipe/{env}/ is missing")
    files = []
    for top in (repo / "recipe" / env, repo / "lean" / f"audit-{'pin' if env == 'pin-seeded' else env}"):
        for directory, subdirectories, names in os.walk(top):
            subdirectories[:] = [d for d in subdirectories if d != ".lake"]
            files += [Path(directory, name) for name in names]
    lines = sorted(f"{f.relative_to(repo).as_posix()}\t{hashlib.sha256(f.read_bytes()).hexdigest()}\n"
                   for f in files)
    return "sha256:" + hashlib.sha256("".join(lines).encode()).hexdigest()
