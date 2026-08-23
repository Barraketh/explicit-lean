#!/usr/bin/env python3
"""Compile focused closed-replay examples."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PROBES = (
    "Experiment/SimpEngineReplayProbe.lean",
    "Experiment/SimpEngineReplayProductionProbe.lean",
)
REQUIRED = {
    "rewrite.commit",
    "reduce.beta",
    "reduce.delta",
    "struct.cacheHit",
    "struct.proofSkip",
    "struct.unassignedMVarStop",
    "struct.congruence.generated",
    "struct.congruence.generic",
    "struct.congruence.user",
    "struct.contextualScope",
    "struct.forall.implicationContextual",
    "struct.forall.implicationPlain",
    "struct.forall.propositionDomainTransport",
    "struct.haveTelescope",
    "struct.lambdaTelescope",
    "struct.dsimpTransform",
    "builtin.decideTrue",
    "builtin.arith.intEquality",
    "control.phase.pre.continueNone",
    "control.phase.post.visit",
    "control.phase.dpre.continueSome",
    "control.phase.dpost.done",
}


def main() -> None:
    build = subprocess.run(
        ["lake", "build", "ExplicitLean:shared"], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300,
    )
    if build.returncode:
        raise RuntimeError(build.stdout)
    query = subprocess.run(
        ["lake", "query", "ExplicitLean:shared", "--json"], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
    )
    if query.returncode:
        raise RuntimeError(query.stdout + query.stderr)
    dylib = json.loads(query.stdout.strip())
    observed: set[str] = set()
    outputs: list[str] = []
    for probe in PROBES:
        run = subprocess.run(
            ["lake", "env", "lean", f"--load-dynlib={dylib}", probe],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=300,
        )
        outputs.append(run.stdout)
        if run.returncode:
            raise RuntimeError(run.stdout)
        for line in run.stdout.splitlines():
            marker = "SIMP_ENGINE_REPLAY branches="
            if marker in line:
                observed.update(filter(None, line.split(marker, 1)[1].split(",")))
    missing = sorted(REQUIRED - observed)
    if missing:
        raise RuntimeError("unreplayed_transition: " + ", ".join(missing) + "\n" + "".join(outputs))
    print(f"schema-16 focused closed replay: {len(observed)} dynamic branches: ok")


if __name__ == "__main__":
    main()
