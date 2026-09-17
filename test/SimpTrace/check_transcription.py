#!/usr/bin/env python3
"""Count simp-family tactic sites in a Mathlib source and its traced copy.

A traced measurement module is only honest if it converted *every* executable
`simp`/`simp only` in the source: a module that silently drops sites reports
partial coverage as though it were complete, and leaves live `simp` calls in a
file whose stated purpose is to demonstrate removing them (AGENTS.md's governing
rule). REVIEW-8 5 found two such sites, both `<tactic>; simp`, which the
generator's line rewrite missed.

Run from the repository root:

    python3 -B test/SimpTrace/check_transcription.py

Exit 0 when every traced copy accounts for its source's sites, 1 otherwise.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
MATHLIB = ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"

# (traced copy under test/SimpTrace/, source under Mathlib/)
MODULES = (
    ("IsEmptyBasicTraced.lean", "Logic/IsEmpty/Basic.lean"),
    ("NontrivialDefsTraced.lean", "Logic/Nontrivial/Defs.lean"),
    ("FunctionDefsTraced.lean", "Logic/Function/Defs.lean"),
    ("ExistsUniqueTraced.lean", "Logic/ExistsUnique.lean"),
    ("FunctionBasicTraced.lean", "Logic/Function/Basic.lean"),
    ("LogicBasicTraced.lean", "Logic/Basic.lean"),
)

# A simp-family tactic *invocation*, as opposed to `@[simp]`, a declaration
# name, a doc comment or the `Simp.simp` term-level API.
TACTIC = re.compile(r"(?<![\w?.])(simp only|simp|dsimp only|dsimp)(?![_?\w])")


def tactic_sites(text: str) -> int:
    """Count simp-family tactic invocations, excluding non-tactic mentions."""
    count = 0
    for line in text.split("\n"):
        stripped = line.lstrip()
        if "@[" in line or stripped.startswith("attribute"):
            continue
        if "Simp.simp" in line or stripped.startswith("--") or stripped.startswith("/-"):
            continue
        for match in TACTIC.finditer(line):
            before = line[: match.start()].rstrip()
            # `<| simp e` and `$ simp e` apply the simp *API* to a term; they
            # are not tactic invocations and the review excludes them.
            if before.endswith(("<|", "$")):
                continue
            # A tactic invocation starts a tactic, or follows `by`, `;`, `<;>`,
            # `·`, `|` or nothing at all.
            if (
                before == ""
                or before.endswith(("by", ";", "<;>", "·", "|", "=>", "(", "["))
            ):
                count += 1
    return count


def main() -> int:
    problems: list[str] = []
    for traced_name, source_rel in MODULES:
        traced_path = ROOT / "test" / "SimpTrace" / traced_name
        source_path = MATHLIB / source_rel
        if not traced_path.is_file():
            problems.append(f"{traced_name}: missing")
            continue
        if not source_path.is_file():
            problems.append(f"{source_rel}: missing (is Mathlib built?)")
            continue
        source_sites = tactic_sites(source_path.read_text(encoding="utf-8"))
        traced_text = traced_path.read_text(encoding="utf-8")
        converted = traced_text.count("simp_trace")
        # Any simp-family tactic left unconverted in the copy.
        remaining = tactic_sites(traced_text.replace("simp_trace", "SIMPTRACE"))
        print(
            f"{traced_name:28} source sites {source_sites:3}  "
            f"converted {converted:3}  still stock {remaining:3}"
        )
        if remaining:
            problems.append(
                f"{traced_name}: {remaining} simp-family tactic site(s) were not "
                f"converted; a traced copy must contain none"
            )
        if converted != source_sites:
            problems.append(
                f"{traced_name}: converted {converted} but the source has "
                f"{source_sites} tactic site(s)"
            )

    if problems:
        for problem in problems:
            print(f"FAIL {problem}", file=sys.stderr)
        return 1
    print("\nOK: every traced copy accounts for all of its source's simp sites")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
