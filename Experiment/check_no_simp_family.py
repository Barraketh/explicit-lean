#!/usr/bin/env python3
"""Lint: `explicit_rw` product code must not touch the simp family.

`explicit_rw` is product code: it will appear in translated Mathlib files. Per
the governing rule in AGENTS.md it must not call, import for use, or expand to
`Lean.Meta.Simp` or any simp-family tactic.

This check scans every file under `ExplicitLean/ExplicitRw*` for references to
simp-family identifiers and to the `Lean.Meta.Simp` namespace. It fails on the
first offending reference, naming the file, line and matched text.

Comments and docstrings are exempt on purpose: the modules *document* that they
avoid simp, and forbidding the word would make that impossible to say. Only
code is scanned. Run with `python3 -B Experiment/check_no_simp_family.py`.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Directories and files whose *code* must be free of the simp family.
TARGETS = [
    REPO / "ExplicitLean" / "ExplicitRw.lean",
    REPO / "ExplicitLean" / "ExplicitRw",
]

# Tactic names and namespaces from the governing rule in AGENTS.md.
FORBIDDEN_TACTICS = [
    "simp",
    "simp_all",
    "simp_arith",
    "simp_rw",
    "simpa",
    "dsimp",
    "field_simp",
    "norm_num",
    "push_cast",
    "norm_cast",
]

# A simp-family tactic used as a Lean identifier or tactic name. `\b` on both
# sides keeps `simp` from matching inside `simple` or `SimpleFoo`, while still
# catching `simp only`, `Simp.Config`, `evalSimp` is caught by the namespace
# pattern below.
TACTIC_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_.])(" + "|".join(re.escape(t) for t in FORBIDDEN_TACTICS) + r")(?![A-Za-z0-9_])"
)

# Anything in the simp implementation namespace, however it is spelled.
NAMESPACE_PATTERN = re.compile(r"(?<![A-Za-z0-9_])(Lean\.Meta\.Simp|Meta\.Simp|Simp\.[A-Z])")

# Identifiers that mention simp by name, e.g. `evalSimp`, `simpTarget`,
# `mkSimpContext`, `SimpTheorems`. Catches a call that the patterns above miss
# because it is a camel-case member rather than a bare tactic name.
CAMEL_PATTERN = re.compile(r"(?<![A-Za-z0-9_])[A-Za-z0-9_]*[Ss]imp(?:roc)?[A-Z][A-Za-z0-9_]*")


def strip_comments(text: str) -> list[tuple[int, str]]:
    """Return (line number, code-only text) pairs, with comments blanked out.

    Handles Lean's `--` line comments and nestable `/- -/` block comments,
    which also covers `/-- -/` docstrings and `/-! -/` module docs.
    """
    out: list[tuple[int, str]] = []
    depth = 0
    for lineno, line in enumerate(text.splitlines(), start=1):
        code_chars: list[str] = []
        i = 0
        while i < len(line):
            two = line[i : i + 2]
            if depth == 0 and two == "--":
                break  # rest of the line is a comment
            if two == "/-":
                depth += 1
                i += 2
                continue
            if two == "-/" and depth > 0:
                depth -= 1
                i += 2
                continue
            if depth == 0:
                code_chars.append(line[i])
            i += 1
        out.append((lineno, "".join(code_chars)))
    return out


def lean_files() -> list[Path]:
    files: list[Path] = []
    for target in TARGETS:
        if target.is_file():
            files.append(target)
        elif target.is_dir():
            files.extend(sorted(target.rglob("*.lean")))
    return files


def main() -> int:
    files = lean_files()
    if not files:
        print("check_no_simp_family: FAIL: no files found under ExplicitLean/ExplicitRw*")
        return 1

    violations: list[str] = []
    for path in files:
        text = path.read_text(encoding="utf-8")
        for lineno, code in strip_comments(text):
            if not code.strip():
                continue
            for pattern, what in (
                (TACTIC_PATTERN, "simp-family tactic"),
                (NAMESPACE_PATTERN, "simp implementation namespace"),
                (CAMEL_PATTERN, "simp-derived identifier"),
            ):
                for match in pattern.finditer(code):
                    rel = path.relative_to(REPO)
                    violations.append(
                        f"{rel}:{lineno}: {what} `{match.group(0)}` in code:\n"
                        f"    {code.strip()}"
                    )

    scanned = ", ".join(str(p.relative_to(REPO)) for p in files)
    if violations:
        print("check_no_simp_family: FAIL")
        print(f"scanned {len(files)} file(s): {scanned}")
        print()
        for v in violations:
            print(v)
        print()
        print(
            f"{len(violations)} violation(s). `explicit_rw` is product code and must not "
            "reference the simp family; see the governing rule in AGENTS.md."
        )
        return 1

    print(f"check_no_simp_family: PASS ({len(files)} file(s) scanned: {scanned})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
