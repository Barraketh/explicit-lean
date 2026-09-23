#!/usr/bin/env python3
"""Record, render and replay ordinary-Lean `change.to` printer fixtures."""

from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
PIPELINE = ROOT / "Experiment" / "pipeline"
sys.path.insert(0, str(PIPELINE))

import render as R  # noqa: E402

FIXTURE = ROOT / "test" / "SimpTrace" / "ChangeSurfaceFixture.lean"
RECORDER_CALLS = {
    "CHANGE_SURFACE_NAT_TRACE": (
        'simp_trace =>trace ".lake/private/change-surface-fixture-nat.json"'
    ),
    "CHANGE_SURFACE_INSTANCE_TRACE": (
        'simp_trace [-Nat.add_zero] '
        '=>trace ".lake/private/change-surface-fixture-instance.json"'
    ),
    "CHANGE_SURFACE_STRING_TRACE": (
        'simp_trace at h '
        '=>trace ".lake/private/change-surface-fixture-string.json"'
    ),
}
FIXTURE_TRACE_PATHS = {
    "CHANGE_SURFACE_NAT_TRACE": ".lake/private/change-surface-fixture-nat.json",
    "CHANGE_SURFACE_INSTANCE_TRACE": ".lake/private/change-surface-fixture-instance.json",
    "CHANGE_SURFACE_STRING_TRACE": ".lake/private/change-surface-fixture-string.json",
}
FORBIDDEN = re.compile(
    r"(?:\bnat_lit\b|\binst[A-Z]\w*|@\w+|✝|⋯|\.\{[^}]*\})"
)


def run_lean(path: pathlib.Path) -> None:
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT,
        capture_output=True, text=True, timeout=1800,
    )
    if proc.returncode:
        raise RuntimeError(
            f"Lean failed for {path}:\n{proc.stdout}{proc.stderr}"
        )


def collect_change_terms(trace_path: pathlib.Path, label: str) -> list[str]:
    raw = json.loads(trace_path.read_text(encoding="utf-8"))
    locations = raw.get("locations")
    if not isinstance(locations, list) or not locations:
        raise AssertionError(f"{label}: recorder emitted no locations")

    terms: list[str] = []

    def visit(value: object) -> None:
        if isinstance(value, list):
            for item in value:
                visit(item)
        elif isinstance(value, dict):
            if value.get("kind") == "change":
                term = value.get("to")
                if not isinstance(term, str) or not term.strip():
                    raise AssertionError(f"{label}: change has no nonempty `to`")
                if any(ch in term for ch in "\r\n\t"):
                    raise AssertionError(f"{label}: `change.to` is not one line: {term!r}")
                bad = FORBIDDEN.search(term)
                if bad:
                    raise AssertionError(
                        f"{label}: `change.to` exposes pp.all syntax {bad.group(0)!r}: {term!r}"
                    )
                terms.append(term)
            for nested in value.values():
                visit(nested)

    for location in locations:
        if not isinstance(location, dict):
            raise AssertionError(f"{label}: malformed location")
        visit(location.get("steps"))
    if not terms and label != "CHANGE_SURFACE_STRING_TRACE":
        raise AssertionError(f"{label}: recorder emitted no change step")
    if label == "CHANGE_SURFACE_NAT_TRACE":
        has_surface_value = any(re.search(r"\b3\b", term) for term in terms)
    elif label == "CHANGE_SURFACE_INSTANCE_TRACE":
        has_surface_value = any("+" in term for term in terms)
    elif label == "CHANGE_SURFACE_STRING_TRACE":
        has_surface_value = True
    else:
        raise AssertionError(f"unexpected recorder fixture {label}")
    if not has_surface_value:
        raise AssertionError(
            f"{label}: expected ordinary numeral/instance-bearing surface syntax, got {terms!r}"
        )
    return terms


def contains_value(value: object, target: str) -> bool:
    if value == target:
        return True
    if isinstance(value, dict):
        return any(contains_value(nested, target) for nested in value.values())
    if isinstance(value, list):
        return any(contains_value(nested, target) for nested in value)
    return False


def record_and_replay() -> None:
    private = ROOT / ".lake" / "private"
    private.mkdir(parents=True, exist_ok=True)
    run_dir = pathlib.Path(tempfile.mkdtemp(prefix="change-surface-", dir=private))
    source = FIXTURE.read_text(encoding="utf-8")
    recorded_source = source
    trace_paths: dict[str, pathlib.Path] = {}
    for token in RECORDER_CALLS:
        trace_path = run_dir / f"{token.lower()}.json"
        trace_paths[token] = trace_path
        recorded_source = recorded_source.replace(
            FIXTURE_TRACE_PATHS[token], trace_path.as_posix()
        )
    recorded = run_dir / "ChangeSurfaceRecorder.lean"
    recorded.write_text(recorded_source, encoding="utf-8")
    run_lean(recorded)

    replay_source = source
    for token, call in RECORDER_CALLS.items():
        terms = collect_change_terms(trace_paths[token], token)
        raw = json.loads(trace_paths[token].read_text(encoding="utf-8"))
        if token == "CHANGE_SURFACE_STRING_TRACE":
            string_term = '"literal.{abc}"'
            if not contains_value(raw, string_term):
                raise AssertionError(f"{token}: recorder lost the string literal")
            if R.check_term(string_term, "fixture string literal") != string_term:
                raise AssertionError("renderer changed the universe-like string literal")
        trace = {"schema": "simp-trace-v1", "locations": raw["locations"]}
        rendered, _ = R.render_trace(trace)
        if len(rendered) != 1:
            raise AssertionError(f"{token}: expected one rendered location, got {rendered!r}")
        if token != "CHANGE_SURFACE_STRING_TRACE" and "change " not in rendered[0]:
            raise AssertionError(f"{token}: rendered replay lost its `change` step")
        if terms and not any(term in rendered[0] for term in terms):
            raise AssertionError(f"{token}: rendered replay lost recorded change target")
        if replay_source.count(call) != 1:
            raise AssertionError(f"{token}: fixture recorder call is not unique")
        indent = " " * 2
        replay_call = ("\n" + indent).join(rendered)
        replay_source = replay_source.replace(call, replay_call, 1)

    replayed = run_dir / "ChangeSurfaceReplay.lean"
    replayed.write_text(replay_source, encoding="utf-8")
    run_lean(replayed)
    print("change surface recorder/render/replay: passed")
    for token, path in trace_paths.items():
        terms = collect_change_terms(path, token)
        print(f"  {token}: {len(terms)} change target(s): {terms}")
    print(f"  replay module: {replayed}")


if __name__ == "__main__":
    record_and_replay()
