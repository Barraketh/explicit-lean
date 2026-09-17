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
import json
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from trace_identity import find_sites, manifest  # noqa: E402

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
        source_text = source_path.read_text(encoding="utf-8")
        source_sites = find_sites(source_text)
        traced_text = traced_path.read_text(encoding="utf-8")
        traced_stem = traced_path.stem
        manifest_path = traced_path.with_suffix(".manifest.json")
        clause_re = re.compile(
            rf"=>trace \"test/SimpTrace/meas_out/{re.escape(traced_stem)}_([0-9]+)\.json\""
        )
        clause_sites = [int(m.group(1)) - 1 for m in clause_re.finditer(traced_text)]
        converted = len(clause_sites)
        remaining = len(find_sites(traced_text))
        print(
            f"{traced_name:28} source sites {len(source_sites):3}  "
            f"converted {converted:3}  still stock {remaining:3}"
        )
        if remaining:
            problems.append(
                f"{traced_name}: {remaining} simp-family tactic site(s) were not "
                f"converted; a traced copy must contain none"
            )
        if converted != len(source_sites):
            problems.append(
                f"{traced_name}: converted {converted} but the source has "
                f"{len(source_sites)} tactic site(s)"
            )
        if sorted(clause_sites) != list(range(len(source_sites))):
            problems.append(f"{traced_name}: generated site ordinals are not a bijection")
        if not manifest_path.is_file():
            problems.append(f"{traced_name}: manifest sidecar missing")
            continue
        try:
            value = json.loads(manifest_path.read_text(encoding="utf-8"))
            expected = manifest("Mathlib/" + source_rel, source_text, source_sites)
            if value != expected:
                problems.append(f"{traced_name}: manifest does not match source")
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            problems.append(f"{traced_name}: malformed manifest: {exc}")

    if problems:
        for problem in problems:
            print(f"FAIL {problem}", file=sys.stderr)
        return 1
    print("\nOK: every traced copy accounts for all of its source's simp sites")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
