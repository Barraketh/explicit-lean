#!/usr/bin/env python3
"""Compile and run the end-to-end Fin.mk canonical-fold probe."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PROBE = "Experiment/FinMkCanonicalFoldProbe.lean"
POSITIVE_MARKER = "FIN_MK_CANONICAL ordinary,dphase,trace,unsupported: ok"
MUTATION_MARKER = "FIN_MK_MUTATIONS rejected=77"


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
            "Fin.mk canonical-fold probe markers missing: "
            + ", ".join(missing)
            + "\n"
            + run.stdout
        )
    print("Fin.mk canonical fold and mutation rejection: ok")


if __name__ == "__main__":
    main()
