#!/usr/bin/env python3
"""Compile and run the focused ExistsAndEq semantic-simproc gate."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PROBE = "Experiment/ExistsAndEqFoldProbe.lean"
POSITIVE_MARKER = (
    "SIMP_ENGINE_EXISTS_AND_EQ direct,nested,multiple,hygienic,loop,post,"
    "registry-post-deferred,unsupported: ok"
)
MUTATION_MARKER = "SIMP_ENGINE_EXISTS_AND_EQ_MUTATIONS rejected=59"


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
        marker
        for marker in (POSITIVE_MARKER, MUTATION_MARKER)
        if marker not in run.stdout
    ]
    if missing:
        raise RuntimeError(
            "ExistsAndEq gate markers missing: "
            + ", ".join(missing)
            + "\n"
            + run.stdout
        )
    print("ExistsAndEq semantic-simproc fold and mutation rejection: ok")


if __name__ == "__main__":
    main()
