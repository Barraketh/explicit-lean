#!/usr/bin/env python3
"""Check Package D selector syntax, rollback, and mutation diagnostics."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
PROBE = ROOT / "Experiment" / "SelectorProbe.lean"
OUTPUT = ROOT / ".lake" / "simp-explicit-selector-fixtures"


def run_probe(path: Path) -> tuple[int, str]:
    code, output, _ = coverage.run(["lake", "env", "lean", str(path)], timeout=180)
    return code, output


def main() -> None:
    source = PROBE.read_text(encoding="utf-8")
    required = [
        "match 2 => Nat.add_zero",
        "tick 11 => Nat.add_zero",
        "11 => Nat.add_zero",
        "match 2 => guardedAdd n using [Nat.zero_le n]",
    ]
    for needle in required:
        if needle not in source:
            raise RuntimeError(f"selector fixture is missing a `{needle}` case")

    code, output = run_probe(PROBE)
    if code != 0:
        raise RuntimeError(f"selector fixture failed: exit={code}\n{output}")

    mutations = [
        (
            "ordinal-too-large",
            "fail_if_success simp_explicit [match 2 => Nat.add_zero]",
            "simp_explicit [match 2 => Nat.add_zero]",
            "simp_explicit match ordinal 2 not reached; observed 1 successful sites",
        ),
        (
            "phase-mutation",
            "fail_if_success simp_explicit [tick 11 => ↓ Nat.add_zero]",
            "simp_explicit [tick 11 => ↓ Nat.add_zero]",
            "simp_explicit traversal phase changed at position 11",
        ),
        (
            "zero-ordinal",
            "fail_if_success simp_explicit [match 0 => Nat.add_zero]",
            "simp_explicit [match 0 => Nat.add_zero]",
            "simp_explicit match ordinals start at 1",
        ),
    ]
    OUTPUT.mkdir(parents=True, exist_ok=True)
    for name, guarded, mutated, diagnostic in mutations:
        if source.count(guarded) != 1:
            raise RuntimeError(f"mutation anchor is not unique: {name}")
        mutated_source = source.replace(guarded, mutated, 1)
        path = OUTPUT / f"Selector_{name}.lean"
        path.write_text(mutated_source, encoding="utf-8")
        code, output = run_probe(path)
        if code == 0 or diagnostic not in output:
            raise RuntimeError(
                f"{name} mutation did not preserve its diagnostic: "
                f"exit={code}, expected={diagnostic!r}\n{output}"
            )

    print("selector next/match/tick replay, premise rollback, and mutations passed")


if __name__ == "__main__":
    main()
