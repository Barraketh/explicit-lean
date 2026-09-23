#!/usr/bin/env python3
"""Regression for source-applied simp arguments behind reducible Π wrappers."""

from __future__ import annotations

import json
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "test" / "SimpTrace" / "MissingSourceApplication.lean"
TRACE_MARKERS = {
    "applied-local.json": "T77_MISSING_APPLIED_LOCAL",
    "forall-local.json": "T77_MISSING_FORALL_LOCAL",
    "membership-local.json": "T77_MISSING_MEMBERSHIP_LOCAL",
    "choose-spec.json": "T77_MISSING_CHOOSE_SPEC",
    "subtype-property.json": "T77_MISSING_SUBTYPE_PROPERTY",
    "show-from.json": "T77_MISSING_SHOW_FROM",
    "multiple-theorems.json": "T77_MISSING_MULTIPLE_THEOREMS",
}


def run_lean(path: pathlib.Path, *, success: bool) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT,
        capture_output=True, text=True, timeout=1800,
    )
    if (proc.returncode == 0) != success:
        raise AssertionError(
            f"Lean returned {proc.returncode} for {path}:\n{proc.stdout}{proc.stderr}"
        )
    return proc


def main() -> None:
    run_dir = pathlib.Path(tempfile.mkdtemp(
        prefix="t77-missing-source-application-", dir=ROOT / ".lake" / "private"
    ))
    source = FIXTURE.read_text(encoding="utf-8")
    recorded_source = source
    for filename, marker in TRACE_MARKERS.items():
        recorded_source = recorded_source.replace(marker, (run_dir / filename).as_posix())
    recorded = run_dir / "MissingSourceApplicationRecorded.lean"
    recorded.write_text(recorded_source, encoding="utf-8")

    positive = run_lean(recorded, success=True)
    if positive.stdout or positive.stderr:
        raise AssertionError(f"positive source-application fixture emitted diagnostics: {positive}")

    outputs = {
        "applied-local.json": (1, {"f g"}),
        "forall-local.json": (1, {"f g"}),
        "membership-local.json": (1, {"P 0 3"}),
        "choose-spec.json": (1, {"⋯.choose"}),
        "subtype-property.json": (1, {"p ↑x"}),
        "show-from.json": (1, {"f n"}),
        "multiple-theorems.json": (2, {"p", "q"}),
    }
    for filename, (expected_count, expected_before) in outputs.items():
        value = json.loads((run_dir / filename).read_text(encoding="utf-8"))
        steps = [step for step in value["locations"][0]["steps"]
                 if step.get("derivation", {}).get("source") == "simp-argument"]
        if len(steps) != expected_count:
            raise AssertionError(f"{filename}: expected {expected_count} source rewrites, got {steps!r}")
        if {step["before"] for step in steps} != expected_before:
            raise AssertionError(f"{filename}: unexpected source rewrite redexes: {steps!r}")
        if any(step.get("unresolved") for step in steps):
            raise AssertionError(f"{filename}: source argument remained unresolved: {steps!r}")
        if any("sourceValue" in step for step in steps):
            raise AssertionError("validator-only source values leaked into trace JSON")
        if any(step["derivation"].get("argId") != 0 for step in steps):
            raise AssertionError(f"{filename}: source range/argument identity was lost: {steps!r}")

    print("source-applied application validation: positive, range identity, and multi-theorem controls passed")


if __name__ == "__main__":
    main()
