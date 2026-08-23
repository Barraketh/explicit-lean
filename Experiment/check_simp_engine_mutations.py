#!/usr/bin/env python3
"""Require schema-17 replay to reject focused single-field mutations."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    build = subprocess.run(
        ["lake", "build", "ExplicitLean:shared"], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300,
    )
    if build.returncode:
        raise RuntimeError(build.stdout)
    query = subprocess.run(
        ["lake", "query", "ExplicitLean:shared", "--json"], cwd=ROOT,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
    )
    if query.returncode:
        raise RuntimeError(query.stdout + query.stderr)
    dylib = json.loads(query.stdout.strip())
    run = subprocess.run(
        ["lake", "env", "lean", f"--load-dynlib={dylib}",
         "Experiment/SimpEngineMutationProbe.lean"],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=300,
    )
    if run.returncode:
        raise RuntimeError(run.stdout)
    if "SIMP_ENGINE_MUTATIONS core=9" not in run.stdout or \
            "SIMP_ENGINE_MUTATIONS structural=7" not in run.stdout or \
            "SIMP_ENGINE_MUTATIONS generated=1" not in run.stdout or \
            "SIMP_ENGINE_MUTATIONS equation=1" not in run.stdout or \
            "SIMP_ENGINE_MUTATIONS arithmetic=2" not in run.stdout:
        raise RuntimeError("mutation probe did not run all cases\n" + run.stdout)
    print("schema-17 replay mutations: 20 rejected: ok")


if __name__ == "__main__":
    main()
