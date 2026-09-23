#!/usr/bin/env python3
"""Compile the focused operational recorder probe and check exact positions."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

from render_simp_operations import render_trace


ROOT = Path(__file__).resolve().parents[1]
PROBE = "test/SimpTrace/T79OperationalRecording.lean"


def run(*command: str) -> str:
    result = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=300,
    )
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def main() -> None:
    run("lake", "build", "ExplicitLean:shared")
    query = run("lake", "query", "ExplicitLean:shared", "--json")
    dylib = json.loads([line for line in query.splitlines() if line.strip()][-1])
    output = run("lake", "env", "lean", f"--load-dynlib={dylib}", PROBE)
    traces = [
        json.loads(line.split("SIMP_OPERATIONS ", 1)[1])
        for line in output.splitlines()
        if "SIMP_OPERATIONS " in line
    ]
    if len(traces) != 5:
        raise RuntimeError(f"expected five traces, got {len(traces)}\n{output}")
    tagged = [line.split("SIMP_OPERATIONS_SITE ", 1)[1]
              for line in output.splitlines() if "SIMP_OPERATIONS_SITE " in line]
    if len(tagged) != 1 or not tagged[0].startswith("17 {"):
        raise RuntimeError(f"expected one source-labelled trace for site 17: {tagged!r}\n{output}")
    tagged_trace = json.loads(tagged[0].split(" ", 1)[1])
    if tagged_trace != traces[0]:
        raise RuntimeError("source-site log label changed the operation trace payload")
    first_positions = [event["position"] for event in traces[0]["events"]]
    second_positions = [event["position"] for event in traces[1]["events"]]
    if first_positions != [[0, 1], []]:
        raise RuntimeError(f"unexpected root trace positions: {first_positions}")
    if second_positions[0] != [0, 1, 0, 1]:
        raise RuntimeError(f"unexpected nested rewrite position: {second_positions[0]}")
    third = traces[2]["events"]
    if third[0]["position"] != [0, 1] or "reduce" not in third[0]["action"]:
        raise RuntimeError(f"unexpected beta operation: {third[0]}")
    local_json = json.dumps(traces[3], sort_keys=True)
    if "contextIndex" not in local_json:
        raise RuntimeError(f"local operation lost its context identity: {local_json}")
    for forbidden in ("typeFingerprint", "valueFingerprint", "fingerprint"):
        if forbidden in local_json:
            raise RuntimeError(f"local operation leaked {forbidden}: {local_json}")
    if "local local_ref 2" not in render_trace(traces[3]):
        raise RuntimeError(f"local operation did not render by context identity: {traces[3]}")
    metadata_positions = [event["position"] for event in traces[4]["events"]]
    if metadata_positions != [[0, 0, 1], [0]]:
        raise RuntimeError(f"unexpected metadata trace positions: {metadata_positions}")
    expected = (
        "explicit_rw_v2 [rule Nat.add_zero variant 0 phase post fwd extra 0 "
        "at [0, 1] with [], rule eq_self variant 0 phase post fwd extra 0 "
        "at [] with []] then true_intro"
    )
    if render_trace(traces[0]) != expected:
        raise RuntimeError(f"unexpected rendered source: {render_trace(traces[0])}")
    print("operational recorder: exact rule identities and raw positions: ok")


if __name__ == "__main__":
    main()
