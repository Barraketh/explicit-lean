#!/usr/bin/env python3
"""Record, render, replay, and check fail-closed controls for prop source values."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "Experiment" / "pipeline"))
import render as R  # noqa: E402

FIXTURE = ROOT / "test" / "SimpTrace" / "T77NeZeroSourceEvidence.lean"
CALLS = {
    "NEZERO": 'simp_trace [NeZero.ne _] =>trace "T77_NEZERO_SOURCE_TRACE_PATH"',
    "TRUE": 'simp_trace only [Nat.zero_le _] =>trace "T77_PROP_TRUE_SOURCE_TRACE_PATH"',
}
MARKERS = {
    "NEZERO": "T77_NEZERO_SOURCE_TRACE_PATH",
    "TRUE": "T77_PROP_TRUE_SOURCE_TRACE_PATH",
}


def run_lean(path: pathlib.Path) -> None:
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT,
        capture_output=True, text=True, timeout=1800,
    )
    if proc.returncode:
        raise AssertionError(f"Lean failed for {path}:\n{proc.stdout}{proc.stderr}")


def main() -> None:
    run_dir = pathlib.Path(tempfile.mkdtemp(
        prefix="t77-nezero-source-", dir=ROOT / ".lake" / "private"
    ))
    traces = {name: run_dir / f"{name.lower()}.json" for name in CALLS}
    source = FIXTURE.read_text(encoding="utf-8")
    recorded_source = source
    for name, marker in MARKERS.items():
        recorded_source = recorded_source.replace(marker, traces[name].as_posix())
    recorded = run_dir / "T77NeZeroSourceEvidenceRecorded.lean"
    recorded.write_text(recorded_source, encoding="utf-8")
    run_lean(recorded)

    rendered: dict[str, str] = {}
    expected = {
        "NEZERO": ("NeZero.ne", "false", "n = 0", "False"),
        "TRUE": ("Nat.zero_le", "true", "0 ≤ n", "True"),
    }
    for name, path in traces.items():
        raw = json.loads(path.read_text(encoding="utf-8"))
        steps = raw["locations"][0]["steps"]
        matches = [step for step in steps if step.get("name") == expected[name][0]]
        if len(matches) != 1:
            raise AssertionError(f"{name}: expected one source-backed proposition step, got {steps!r}")
        step = matches[0]
        if step.get("prop") != expected[name][1]:
            raise AssertionError(f"{name}: wrong proposition polarity: {step!r}")
        if (step.get("before"), step.get("after")) != expected[name][2:]:
            raise AssertionError(f"{name}: wrong rewrite pair: {step!r}")
        if "unresolved" in step or "sourceValue" in step:
            raise AssertionError(f"{name}: unresolved status or internal evidence leaked: {step!r}")
        derivation = step.get("derivation", {})
        if derivation.get("source") != "simp-argument" or derivation.get("argId") != 0:
            raise AssertionError(f"{name}: missing authenticated source identity: {step!r}")
        output, _ = R.render_trace(
            {"schema": "simp-trace-v2", "site": {"sourceArgs": raw["sourceArgs"]},
             "locations": raw["locations"]},
            source_text=recorded_source,
        )
        if len(output) != 1:
            raise AssertionError(f"{name}: expected one rendered location, got {output!r}")
        rendered[name] = output[0]

    replay_source = recorded_source
    for name, template in CALLS.items():
        call = template.replace(MARKERS[name], traces[name].as_posix())
        if call not in replay_source:
            raise AssertionError(f"fixture lost the {name} source call")
        replay_source = replay_source.replace(call, rendered[name])
    replay = run_dir / "T77NeZeroSourceEvidenceReplayed.lean"
    replay.write_text(replay_source, encoding="utf-8")
    run_lean(replay)

    print("authenticated proposition source-value record/render/replay: passed")
    for name, replacement in rendered.items():
        print(f"  {name}: {replacement}")


if __name__ == "__main__":
    main()
