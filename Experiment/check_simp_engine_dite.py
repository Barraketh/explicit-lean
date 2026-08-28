#!/usr/bin/env python3
"""Compile and run the focused reduceDIte semantic-fold replay probe."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PROBE = "Experiment/DIteSemanticFoldProbe.lean"
MARKER = "SIMP_ENGINE_DITE true=false,nested,nested-dite,headBeta,extra,singlePass,unsupported: ok mutations=86"


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
        raise RuntimeError("reduceDIte probe missed marker\n" + run.stdout)
    print("reduceDIte semantic fold: pre visit, nested condition, headBeta, extra args, parity and mutations: ok")


if __name__ == "__main__":
    main()
