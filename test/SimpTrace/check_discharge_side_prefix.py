#!/usr/bin/env python3
"""Regression for preserving queued side traces across nested dischargers."""

from __future__ import annotations

import json
import pathlib
import subprocess
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "test" / "SimpTrace" / "DischargeSidePrefix.lean"
PLACEHOLDER = "DISCHARGE_SIDE_PREFIX_TRACE_PATH"


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
    run_dir = pathlib.Path(
        tempfile.mkdtemp(prefix="discharge-side-prefix-", dir=private)
    )
    trace_path = run_dir / "two-premise-sides.json"
    recorded = run_dir / "DischargeSidePrefixRecorded.lean"
    source = FIXTURE.read_text(encoding="utf-8")
    if source.count(PLACEHOLDER) != 1:
        raise AssertionError("fixture must have exactly one trace-path placeholder")
    recorded.write_text(
        source.replace(PLACEHOLDER, trace_path.as_posix()), encoding="utf-8"
    )
    run_lean(recorded)

    raw = json.loads(trace_path.read_text(encoding="utf-8"))
    if len(raw.get("locations", [])) != 1:
        raise AssertionError("expected the fixture to produce one trace location")
    steps = raw["locations"][0]["steps"]
    candidates = [step for step in steps
                  if step.get("name") == "Finsupp.sum_sum_index"]
    if not candidates:
        raise AssertionError("trace did not contain Finsupp.sum_sum_index")

    for step in candidates:
        binders = step.get("derivation", {}).get("binders", [])
        discharged = [b for b in binders if b.get("classification") == "discharge"]
        sides = step.get("side", [])
        if len(discharged) != 2 or len(sides) != len(discharged):
            raise AssertionError(
                "sum_sum_index must retain exactly one side for each of its two "
                f"discharged premises; binders={discharged!r}, sides={sides!r}"
            )

        zero_goal = sides[0].get("goal", "")
        add_goal = sides[1].get("goal", "")
        zero_shape = "0 *" in zero_goal or "* 0" in zero_goal
        if not zero_shape or "b₁ + b₂" not in add_goal:
            raise AssertionError(
                "side traces must stay in h_zero, h_add binder order; "
                f"got goals {zero_goal!r} and {add_goal!r}"
            )
        zero_steps = {nested.get("name", "").split(".")[-1]
                      for nested in sides[0].get("steps", [])}
        add_steps = {nested.get("name", "").split(".")[-1]
                     for nested in sides[1].get("steps", [])}
        if not ({"zero_mul", "mul_zero"} & zero_steps) or not {
            "single_add"
        } <= add_steps or not ({"add_mul", "mul_add"} & add_steps):
            raise AssertionError(
                "nested simp evidence was not retained with its own premise: "
                f"h_zero steps={zero_steps!r}, h_add steps={add_steps!r}"
            )

    print(f"two-premise nested side preservation: passed ({len(candidates)} rewrite(s))")


if __name__ == "__main__":
    main()
