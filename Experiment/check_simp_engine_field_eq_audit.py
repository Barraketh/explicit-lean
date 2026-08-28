#!/usr/bin/env python3
"""Compile and run the focused schema-27 ``fieldEq`` audit probe."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PROBE = "Experiment/FieldEqAuditProbe.lean"
MARKER = "FIELD_EQ_AUDIT assumption,normNum,positivity,kept-denominator: ok"


def run(command: list[str], timeout: int = 300) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
    )
    if result.returncode:
        raise RuntimeError("command failed: " + " ".join(command) + "\n" + result.stdout)
    return result


def main() -> None:
    # The Mathlib-dependent audit is intentionally a source/library target,
    # not a dependency of the generic ExplicitLean shared object.  Loading
    # the generic object is sufficient for the probe; the imported audit
    # module's meta code is elaborated from its .olean.
    for target in (
        "ExplicitLean:shared",
        "ExplicitLean.SimpEngine.Recording",
        "ExplicitLean.SimpEngine.Reference",
        "ExplicitLeanMathlibAudit.FieldEq",
    ):
        run(["lake", "build", target])

    query = run(["lake", "query", "ExplicitLean:shared", "--json"], timeout=30)
    dylib = json.loads(query.stdout.strip())
    probe = run(
        ["lake", "env", "lean", f"--load-dynlib={dylib}", PROBE]
    )
    if MARKER not in probe.stdout:
        raise RuntimeError("fieldEq audit probe marker missing\n" + probe.stdout)
    print("schema-27 fieldEq audit probe: ok")


if __name__ == "__main__":
    main()
