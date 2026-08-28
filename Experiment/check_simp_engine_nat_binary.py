#!/usr/bin/env python3
"""Compile and run the focused Nat binary semantic interpreter probe."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PROBE = "Experiment/NatBinarySemanticProbe.lean"
MARKER = (
    "SIMP_ENGINE_NAT_BINARY_SEMANTIC "
    "add=raw,ofNat,metadata div=zero,numeratorZero,exact,inexact: ok"
)


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
    if MARKER not in run.stdout:
        raise RuntimeError("Nat binary semantic probe did not cover all cases\n" + run.stdout)
    print("Nat binary semantic interpreter: ok")


if __name__ == "__main__":
    main()
