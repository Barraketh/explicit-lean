#!/usr/bin/env python3
"""Check the closed manual simp_explicit_context parser/replayer."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
PROBE = ROOT / "Experiment" / "ContextReplayProbe.lean"
OUTPUT = ROOT / ".lake" / "simp-explicit-context-fixtures"


def run_probe(path: Path) -> tuple[int, str]:
    code, output, _ = coverage.run(["lake", "env", "lean", str(path)], timeout=180)
    return code, output


def main() -> None:
    source = PROBE.read_text(encoding="utf-8")
    required = [
        "at h => [Nat.add_zero, eq_self]",
        "at hAdd => [Nat.add_zero, eq_self]",
        "at hMul => [Nat.mul_one, eq_self]",
        "at h_explicit_2 => [Nat.add_zero, eq_self]",
        "rename_i h_explicit_2",
        "closed, explicitly expanded form of `at *`",
        "at k => [eq_self]",
    ]
    for needle in required:
        if needle not in source:
            raise RuntimeError(f"context fixture is missing `{needle}`")

    code, output = run_probe(PROBE)
    if code != 0:
        raise RuntimeError(f"context fixture failed: exit={code}\n{output}")

    OUTPUT.mkdir(parents=True, exist_ok=True)
    mutations = [
        (
            "unknown-subject",
            "    at hAdd => [Nat.add_zero, eq_self],\n    at hMul",
            "    at missing_context_subject => [Nat.add_zero, eq_self],\n    at hMul",
            "unknown local subject `missing_context_subject`",
        ),
        (
            "duplicate-subject",
            "    at hAdd => [Nat.add_zero, eq_self],\n    at hMul => [Nat.mul_one, eq_self],",
            "    at hAdd => [Nat.add_zero, eq_self],\n    at hAdd => [Nat.mul_one, eq_self],",
            "duplicate local subject `hAdd`",
        ),
        (
            "target-not-last",
            "simp_explicit_context [at h => [Nat.add_zero, eq_self], at target => [Nat.add_zero, eq_self]]",
            "simp_explicit_context [at target => [Nat.add_zero, eq_self], at h => [Nat.add_zero, eq_self]]",
            "requires `target` to be the last group",
        ),
        (
            "subject-command-mismatch",
            "simp_explicit_context [at h => [Nat.add_zero, eq_self], at target => [Nat.add_zero, eq_self]]",
            "simp_explicit_context [at h => [Nat.mul_one], at target => [Nat.add_zero, eq_self]]",
            "simp_explicit_context at h did not consume",
        ),
    ]
    for name, anchor, replacement, diagnostic in mutations:
        if source.count(anchor) != 1:
            raise RuntimeError(f"mutation anchor is not unique: {name}")
        mutated = source.replace(anchor, replacement, 1)
        path = OUTPUT / f"Context_{name}.lean"
        path.write_text(mutated, encoding="utf-8")
        code, output = run_probe(path)
        if code == 0 or diagnostic not in output:
            raise RuntimeError(
                f"{name} mutation did not preserve its diagnostic: "
                f"exit={code}, expected={diagnostic!r}\n{output}"
            )

    print("closed simp_explicit_context replay, batch staging, and mutations passed")


if __name__ == "__main__":
    main()
