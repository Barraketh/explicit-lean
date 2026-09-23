#!/usr/bin/env python3
"""Regression for trace snapshots crossing temporary Meta contexts."""

from __future__ import annotations

import json
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "test" / "SimpTrace" / "EventMVarSnapshot.lean"


def run_lean(path: pathlib.Path) -> None:
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT,
        capture_output=True, text=True, timeout=1800,
    )
    if proc.returncode:
        raise AssertionError(f"Lean failed for {path}:\n{proc.stdout}{proc.stderr}")


def main() -> None:
    private = ROOT / ".lake" / "private"
    private.mkdir(parents=True, exist_ok=True)
    run_dir = pathlib.Path(tempfile.mkdtemp(prefix="event-mvar-snapshot-", dir=private))
    trace_path = run_dir / "nested-ne-eq.json"
    source = FIXTURE.read_text(encoding="utf-8")
    recorded = run_dir / "EventMVarSnapshotRecorded.lean"
    recorded.write_text(
        source.replace("NESTED_NE_EQ_TRACE_PATH", trace_path.as_posix()),
        encoding="utf-8",
    )
    run_lean(recorded)

    raw = json.loads(trace_path.read_text(encoding="utf-8"))
    locations = raw["locations"]
    if len(locations) != 1:
        raise AssertionError(f"expected one trace location, got {len(locations)}")
    side_steps = [
        nested
        for step in locations[0]["steps"]
        for side in step.get("side", [])
        for nested in side.get("steps", [])
    ]
    ne_eq = [step for step in side_steps if step.get("name") == "ne_eq"]
    if not ne_eq:
        raise AssertionError("recorded trace did not contain nested ne_eq")
    if any(step.get("unresolved", "").startswith("unreplayable_rw") for step in ne_eq):
        raise AssertionError(f"nested ne_eq remained unreplayable: {ne_eq}")

    print("temporary metavariable snapshot and nested ne_eq validation: passed")


if __name__ == "__main__":
    main()
