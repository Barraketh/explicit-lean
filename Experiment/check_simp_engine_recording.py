#!/usr/bin/env python3
"""Compile the schema-17 recorder probe and require key dynamic observers."""

from __future__ import annotations

import subprocess
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REQUIRED = {
    "rewrite.commit",
    "reduce.beta",
    "reduce.delta",
    "struct.cacheHit",
    "struct.congruence.generated",
    "struct.congruence.generic",
    "struct.congruence.user",
    "struct.contextualScope",
    "struct.forall.implicationContextual",
    "struct.forall.implicationPlain",
    "struct.forall.propositionDomainTransport",
    "struct.haveTelescope",
    "struct.lambdaTelescope",
    "struct.ground",
    "simproc.dsimp",
    "simproc.simp.continueNone",
    "boundary.customDischarger",
    "builtin.decideTrue",
    "builtin.arith.intEquality",
}


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
        ["lake", "env", "lean", f"--load-dynlib={dylib}",
         "Experiment/SimpEngineRecordingProbe.lean"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=300,
    )
    if run.returncode:
        raise RuntimeError(run.stdout)
    observed: set[str] = set()
    subject_counts: list[int] = []
    for line in run.stdout.splitlines():
        marker = "SIMP_ENGINE_RECORDING branches="
        if marker not in line:
            continue
        payload = line.split(marker, 1)[1].split(" events=", 1)[0]
        observed.update(filter(None, payload.split(",")))
        if " subjects=" in line:
            subject_counts.append(int(line.rsplit(" subjects=", 1)[1]))
    missing = sorted(REQUIRED - observed)
    if missing:
        raise RuntimeError("unobserved_transition: " + ", ".join(missing) + "\n" + run.stdout)
    if not subject_counts or max(subject_counts) < 2:
        raise RuntimeError("subject_transport_unobserved\n" + run.stdout)
    print(f"schema-17 recording probe: {len(observed)} dynamic branches: ok")


if __name__ == "__main__":
    main()
