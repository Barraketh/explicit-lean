#!/usr/bin/env python3
"""Compile the focused SimprocEntry invocation differential probe."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PROBE = "Experiment/SimprocInvocationProbe.lean"
MARKER = (
    "SIMP_ENGINE_SIMPROC_INVOCATION "
    "statuses=done,visit,continueSome,continueNone extraArgs=0,2: ok"
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
        raise RuntimeError("simproc invocation probe did not cover all cases\n" + run.stdout)
    print("simproc entry upstream/wrapper differential: ok")


if __name__ == "__main__":
    main()
