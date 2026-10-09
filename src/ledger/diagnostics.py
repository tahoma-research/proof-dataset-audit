"""Diagnostics: the output of every Lean, Lake and audit step, rewritten so that no host path is written."""

from pathlib import Path


def rewrite_paths(text: str, roots: list[Path]) -> tuple[str, bool]:
    """Replace every occurrence of each root, longest first, with `.`; and whether a path under a home or mount
    directory remains, in which case the text is withheld, so that none reaches a written file."""
    for root in sorted({str(r) for r in roots}, key=len, reverse=True):
        text = text.replace(root, ".")
    if "/home/" in text or "/mnt/" in text:  # path-sentinel
        return "withheld: a host path remains after rewriting", True
    return text, False
