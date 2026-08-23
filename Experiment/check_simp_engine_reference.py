#!/usr/bin/env python3
"""Compile the pinned upstream/fork simplifier equivalence probes."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    build = subprocess.run(
        ["lake", "build", "ExplicitLean:shared"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=180,
    )
    if build.returncode != 0:
        raise SystemExit(build.stdout)
    query = subprocess.run(
        ["lake", "query", "ExplicitLean:shared", "--json"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
    )
    if query.returncode != 0:
        raise SystemExit(query.stdout + query.stderr)
    dynlib = json.loads(query.stdout.strip())
    completed = subprocess.run(
        [
            "lake",
            "env",
            "lean",
            f"--load-dynlib={dynlib}",
            "Experiment/SimpEngineReferenceProbe.lean",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=180,
    )
    if completed.returncode != 0:
        raise SystemExit(completed.stdout)
    print("pinned simp engine reference equivalence: ok")


if __name__ == "__main__":
    main()
