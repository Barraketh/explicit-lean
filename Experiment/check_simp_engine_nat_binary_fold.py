#!/usr/bin/env python3
"""Compile and run the focused Nat binary semantic-fold replay probe."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PROBE = "Experiment/NatBinaryFoldProbe.lean"
POSITIVE_MARKER = "SIMP_ENGINE_NAT_BINARY_FOLD add,div,dadd,ddiv: ok"
MUTATION_MARKER = "SIMP_ENGINE_NAT_BINARY_FOLD_MUTATIONS rejected=34"


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
    missing = [
        marker for marker in (POSITIVE_MARKER, MUTATION_MARKER)
        if marker not in run.stdout
    ]
    if missing:
        raise RuntimeError(
            "Nat binary fold probe missed markers: "
            + ", ".join(missing)
            + "\n"
            + run.stdout
        )
    print("Nat binary semantic fold: add/div ordinary+dphase, 34 mutations: ok")


if __name__ == "__main__":
    main()
