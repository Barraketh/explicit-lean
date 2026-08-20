#!/usr/bin/env python3
"""Compile the focused probe and assert its mixed-certificate suggestions."""

from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent

EXPECTED = (
    "Try this deterministic replay:\nnormalize_category",
    "Try this deterministic replay:\nnormalize_category\nsimp_explicit [\n  h\n]",
    "Try this deterministic replay:\nnormalize_category\nsimp_explicit [\n  h\n]\nnormalize_category",
    "Try this deterministic replay:\nsimp_explicit [\n  wrappedComp_eq\n]\nnormalize_category",
)


def main() -> None:
    result = subprocess.run(
        ["lake", "env", "lean", "Experiment/SimpExplicitProbe.lean"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    output = result.stdout + result.stderr
    sys.stdout.write(output)
    if result.returncode != 0:
        raise SystemExit(result.returncode)
    missing = [snippet for snippet in EXPECTED if snippet not in output]
    if missing:
        raise RuntimeError(f"missing mixed-certificate suggestions: {missing!r}")


if __name__ == "__main__":
    main()
