#!/usr/bin/env python3
"""Compile and run the end-to-end Int.reduceNeg guard/literal-fold probe."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PROBE = "Experiment/IntNegGuardFoldProbe.lean"
POSITIVE_MARKER = "INT_NEG_GUARD_FOLD custom,ordinary,dphase,changing,unsupported: ok"
MUTATION_MARKER = "INT_NEG_GUARD_FOLD_MUTATIONS rejected=131"


def main() -> None:
    build = subprocess.run(
        ["lake", "build", "ExplicitLean:shared"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=300,
    )
    if build.returncode:
        raise RuntimeError(build.stdout)
    query = subprocess.run(
        ["lake", "query", "ExplicitLean:shared", "--json"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
    )
    if query.returncode:
        raise RuntimeError(query.stdout + query.stderr)
    dylib = json.loads(query.stdout.strip())
    run = subprocess.run(
        ["lake", "env", "lean", f"--load-dynlib={dylib}", PROBE],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=300,
    )
    if run.returncode:
        raise RuntimeError(run.stdout)
    missing = [marker for marker in (POSITIVE_MARKER, MUTATION_MARKER) if marker not in run.stdout]
    if missing:
        raise RuntimeError("Int neg guard fold probe markers missing: " + ", ".join(missing) + "\n" + run.stdout)
    print("Int.reduceNeg guard/literal fold and mutation rejection: ok")


if __name__ == "__main__":
    main()
