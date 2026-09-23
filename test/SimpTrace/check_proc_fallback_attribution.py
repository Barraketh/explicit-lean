#!/usr/bin/env python3
"""Regression for exact attribution of opaque simproc fallback changes."""

from __future__ import annotations

import json
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "test" / "SimpTrace" / "ProcFallbackAttribution.lean"


def run_lean(path: pathlib.Path, *, expect_unresolved: bool = False) -> None:
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT,
        capture_output=True, text=True, timeout=1800,
    )
    output = proc.stdout + proc.stderr
    if expect_unresolved:
        if proc.returncode == 0 or "simp_trace unresolved: proc_fallback_nested_simp_evidence_unreplayable" not in output:
            raise AssertionError(f"Lean did not fail with the expected classified blocker for {path}:\n{output}")
    elif proc.returncode:
        raise AssertionError(f"Lean failed for {path}:\n{proc.stdout}{proc.stderr}")


def nested_steps(step: dict):
    yield step
    for field in ("steps", "domain", "body"):
        for child in step.get(field, []):
            yield from nested_steps(child)
    for side in step.get("side", []):
        for child in side.get("steps", []):
            yield from nested_steps(child)


def main() -> None:
    private = ROOT / ".lake" / "private"
    private.mkdir(parents=True, exist_ok=True)
    run_dir = pathlib.Path(tempfile.mkdtemp(prefix="proc-fallback-attribution-", dir=private))
    trace_path = run_dir / "cmpLE-swap.json"
    source = FIXTURE.read_text(encoding="utf-8").replace(
        "PROC_FALLBACK_TRACE_PATH", trace_path.as_posix()
    )
    recorded = run_dir / "ProcFallbackAttributionRecorded.lean"
    recorded.write_text(source, encoding="utf-8")
    run_lean(recorded, expect_unresolved=True)

    raw = json.loads(trace_path.read_text(encoding="utf-8"))
    if len(raw.get("locations", [])) != 1:
        raise AssertionError(f"expected one traced location: {raw.get('locations')!r}")
    steps = raw["locations"][0]["steps"]
    wrappers = [
        step for step in steps
        if step.get("kind") == "eq"
        and "cmpLE x y" in (step.get("lhs") or "")
        and "Ordering.eq" in (step.get("rhs") or "")
    ]
    if len(wrappers) != 1:
        raise AssertionError(
            "expected the enclosing cmpLE/match change to be an unattributed eq; "
            f"found {wrappers!r} among {steps!r}"
        )
    wrapper = wrappers[0]
    if not (wrapper.get("by") or "").startswith("unresolved:simproc:"):
        raise AssertionError(f"opaque wrapper was not left as a genuine blocker: {wrapper!r}")
    local_yx = [
        nested for step in steps for nested in nested_steps(step)
        if nested.get("kind") == "rw"
        and nested.get("name") == "yx"
        and (nested.get("local") or {}).get("userName") == "yx"
    ]
    if not local_yx:
        raise AssertionError(
            "the genuine nested local-evidence rewrite by yx was lost from the "
            f"overall trace: {steps!r}"
        )
    falsely_attributed = [
        step for step in steps
        if step.get("kind") == "rw"
        and step.get("name") == "yx"
        and "cmpLE x y" in (step.get("before") or "")
        and "Ordering.eq" in (step.get("after") or "")
    ]
    if falsely_attributed:
        raise AssertionError(f"wrapper was falsely attributed to yx: {falsely_attributed!r}")

    print("proc fallback attribution and nested local evidence: passed")


if __name__ == "__main__":
    main()
