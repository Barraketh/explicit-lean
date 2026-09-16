#!/usr/bin/env python3
"""Focused stock/context/encoding regression for the boundary recorder."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import check_simp_engine_boundary_source as source_checker


ROOT = Path(__file__).resolve().parents[1]
LAKE = ROOT / ".lake"
RESERVE = 12 * 1024**3

FIXTURE = r'''import ExplicitLean.SimpEngine.Boundary

set_option autoImplicit false

class ReviewC : Prop where
  h : True

def ReviewHiddenC : Prop := ReviewC

inductive ReviewBox : Prop where
  | intro

theorem review_box [ReviewC] : ReviewBox ↔ True :=
  ⟨fun _ => .intro, fun _ => .intro⟩

def reviewAlias (n : Nat) : Nat := n

def ReviewTypeAlias : Type := Nat

-- Stock and boundary capture must agree when a proof-free local exposes a
-- class instance.  This is the exact original context regression: unfold the
-- definition in `h` and `k` while retaining the proof-bearing local.
example (h : ReviewHiddenC) (k : ReviewBox) : ReviewBox := by
  simp only [ReviewHiddenC, review_box] at h k
  exact k

example (h : ReviewHiddenC) (k : ReviewBox) : ReviewBox := by
  simp_engine_boundary_probe only [ReviewHiddenC, review_box] at h k
  exact k

-- Target processing uses the updated context, so the newly exposed class
-- instance enables the conditional rewrite and closes the target.
example (h : ReviewHiddenC) (k : ReviewBox) : ReviewBox := by
  simp only [ReviewHiddenC, review_box] at h ⊢

example (h : ReviewHiddenC) (k : ReviewBox) : ReviewBox := by
  simp_engine_boundary_probe only [ReviewHiddenC, review_box] at h ⊢

-- Proof-bearing hypothesis transport remains usable.
example (P : Nat → Prop) (n : Nat) (h : P (0 + n)) : P n := by
  simp only [Nat.zero_add] at h
  exact h

example (P : Nat → Prop) (n : Nat) (h : P (0 + n)) : P n := by
  simp_engine_boundary_probe only [Nat.zero_add] at h
  exact h

-- Proof-free local replacement plus target simplification.
example (P : Nat → Prop) (n : Nat) (h : P (reviewAlias n)) : P n := by
  simp only [reviewAlias] at h ⊢
  exact h

example (P : Nat → Prop) (n : Nat) (h : P (reviewAlias n)) : P n := by
  simp_engine_boundary_probe only [reviewAlias] at h ⊢
  exact h

-- The later local depends on the earlier proof-free replacement.
example (h : ReviewTypeAlias) (k : h = h) : True := by
  simp only [ReviewTypeAlias] at h k
  exact k

example (h : ReviewTypeAlias) (k : h = h) : True := by
  simp_engine_boundary_probe only [ReviewTypeAlias] at h k
  exact k

-- Conditional rewrite remains unavailable without the exposing local.
example (h : ReviewBox) : ReviewBox := by
  simp_engine_boundary_probe (failIfUnchanged := false) only [review_box] at h
  exact h
'''


ROUNDTRIP_ORIGINAL = "simp only [ReviewHiddenC, review_box] at h k"
ROUNDTRIP_DEFS = '''module
public section
public class ReviewC : Prop where
  h : True

@[expose] public def ReviewHiddenC : Prop := ReviewC

public inductive ReviewBox : Prop where
  | intro

public theorem review_box [ReviewC] : ReviewBox ↔ True :=
  ⟨fun _ => .intro, fun _ => .intro⟩
end
'''
ROUNDTRIP_FIXTURE = f'''module
import Experiment.ContextDefs
import ExplicitLean.SimpEngine.Boundary

public theorem reviewHiddenC_warmup : ReviewHiddenC = ReviewC :=
  ReviewHiddenC.eq_1

example (h : ReviewHiddenC) (k : ReviewBox) : ReviewBox := by
  {ROUNDTRIP_ORIGINAL}
  exact k
'''


def available_memory() -> int | None:
    if sys.platform.startswith("linux"):
        try:
            for line in Path("/proc/meminfo").read_text().splitlines():
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) * 1024
        except (OSError, ValueError):
            return None
    if sys.platform == "darwin":
        try:
            page = int(subprocess.check_output(["sysctl", "-n", "hw.pagesize"], text=True))
            values: dict[str, int] = {}
            for line in subprocess.check_output(["vm_stat"], text=True).splitlines():
                match = re.match(r"^(Pages [^:]+):\s+(\d+)", line)
                if match:
                    values[match.group(1)] = int(match.group(2))
            return page * sum(values.get(name, 0) for name in (
                "Pages free", "Pages inactive", "Pages speculative", "Pages purgeable"
            ))
        except (OSError, ValueError, subprocess.SubprocessError):
            return None
    return None


def require_resources(label: str) -> dict[str, int]:
    memory = available_memory()
    disk = shutil.disk_usage(ROOT).free
    if memory is None or memory < RESERVE or disk < RESERVE:
        raise RuntimeError(
            f"{label} denied: available memory={memory!r}, free disk={disk}; "
            f"reserve={RESERVE}"
        )
    return {"availableMemoryBytes": memory, "freeDiskBytes": disk}


def run(command: list[str], timeout: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=timeout, check=False,
    )


def main() -> None:
    work = Path(tempfile.mkdtemp(prefix="replay-context-", dir=LAKE))
    results: list[dict[str, object]] = []
    admission = require_resources("build")
    build = run(["lake", "build", "ExplicitLean:shared"], 600)
    (work / "build.log").write_text(build.stdout, encoding="utf-8")
    if build.returncode:
        raise RuntimeError(f"shared boundary build failed; see {work / 'build.log'}")
    dylibs = [
        ROOT / ".lake" / "build" / "lib" / "libexplicitLean_ExplicitLean.dylib",
        ROOT / ".lake" / "build" / "lib" / "libexplicitLean_ExplicitLean.so",
    ]
    dylibs = [path for path in dylibs if path.is_file()]
    if len(dylibs) != 1:
        raise RuntimeError(f"expected one shared boundary library, found {dylibs!r}")
    dylib = str(dylibs[0])

    context = work / "LocalContext.lean"
    context.write_text(FIXTURE, encoding="utf-8")
    nonce = work.name
    env = dict(
        os.environ,
        SIMP_ENGINE_BOUNDARY_RUN_NONCE=nonce,
    )
    roundtrip_root = work / "roundtrip"
    module_suffix = re.sub(r"[^A-Za-z0-9_]", "_", work.name)
    context_defs_module = f"Experiment.ContextDefs_{module_suffix}"
    context_defs_import = f"public import {context_defs_module}"
    roundtrip_fixture = ROUNDTRIP_FIXTURE.replace(
        "import Experiment.ContextDefs", context_defs_import, 1)
    defs_relative = Path(*context_defs_module.split("."))
    defs_path = roundtrip_root / (defs_relative.with_suffix(".lean"))
    defs_path.parent.mkdir(parents=True, exist_ok=True)
    defs_path.write_text(ROUNDTRIP_DEFS, encoding="utf-8")
    defs_olean = defs_path.with_suffix(".olean")
    defs_build = run([
        "lake", "env", "lean", f"--load-dynlib={dylib}",
        "-R", str(roundtrip_root), "-o", str(defs_olean), str(defs_path),
    ], 180)
    defs_output = defs_build.stdout
    (work / "roundtrip-defs.log").write_text(defs_output, encoding="utf-8")
    if defs_build.returncode or not defs_olean.is_file():
        raise RuntimeError("roundtrip helper compile produced no olean")
    defs_import_dir = LAKE / "build" / "lib" / "lean" / Path(*context_defs_module.split(".")).parent
    defs_import_dir.mkdir(parents=True, exist_ok=True)
    emitted = [path for path in defs_path.parent.glob(defs_path.stem + ".*") if path.is_file()]
    if defs_olean not in emitted:
        raise RuntimeError("roundtrip helper compile omitted its olean artifact")
    for artifact in emitted:
        shutil.copy2(artifact, defs_import_dir / artifact.name)
    roundtrip_original = roundtrip_root / "Experiment" / "ContextRoundtrip.lean"
    roundtrip_original.parent.mkdir(parents=True, exist_ok=True)
    roundtrip_original.write_text(roundtrip_fixture, encoding="utf-8")
    if roundtrip_fixture.count(ROUNDTRIP_ORIGINAL) != 1:
        raise RuntimeError("roundtrip fixture must contain exactly one original tactic")
    prefix, separator, _suffix = roundtrip_fixture.partition(ROUNDTRIP_ORIGINAL)
    if not separator:
        raise RuntimeError("roundtrip fixture lost original tactic")
    start = len(prefix.encode("utf-8"))
    entry = {
        "id": "context-roundtrip",
        "kind": "simp",
        "source": ROUNDTRIP_ORIGINAL,
        "startByte": start,
        "endByte": start + len(ROUNDTRIP_ORIGINAL.encode("utf-8")),
    }
    instrumented = source_checker.replace_occurrence(
        roundtrip_fixture.encode("utf-8"),
        entry["startByte"],
        entry["endByte"],
        'simp_engine_boundary_record "context-roundtrip" only [ReviewHiddenC, review_box] at h k',
    )
    instrumented = source_checker.inject_import(instrumented, "ExplicitLean.SimpEngine.Boundary")
    if instrumented.count(b'simp_engine_boundary_record "context-roundtrip"') != 1:
        raise RuntimeError("roundtrip instrumentation did not replace exactly one tactic")
    roundtrip_recording = roundtrip_root / "recording" / "Experiment" / "ContextRoundtrip.lean"
    roundtrip_recording.parent.mkdir(parents=True, exist_ok=True)
    roundtrip_recording.write_bytes(instrumented)
    output, roundtrip_nonce = source_checker.compile_recording_source(dylib, roundtrip_recording)
    (work / "encoded-roundtrip-recording.log").write_text(output, encoding="utf-8")
    protocol.check_recording_abort_markers(
        output, expected_nonce=roundtrip_nonce, expected_module="Experiment.ContextRoundtrip"
    )
    reports = protocol.parse_framed_json_lines(
        output, marker=materializer.ARTIFACT_MARKER,
        expected_nonce=roundtrip_nonce, label="context roundtrip artifact",
    )
    grouped = protocol.group_report_variants(
        reports, ["context-roundtrip"], expected_module="Experiment.ContextRoundtrip"
    )
    applied_bytes = source_checker.replace_all_occurrences(
        roundtrip_fixture.encode("utf-8"), [entry], grouped
    )
    applied_root = roundtrip_root / "applied"
    applied = materializer._copy_at_module_root(
        applied_root, "Experiment/ContextRoundtrip.lean",
        source_checker.inject_import(applied_bytes, "ExplicitLean.SimpEngine.Boundary.Tactic"),
    )
    replay_output = source_checker.compile_replay_source(
        dylib, applied, "Experiment.ContextRoundtrip"
    )
    (work / "encoded-roundtrip-replay.log").write_text(replay_output, encoding="utf-8")
    results.append({
        "name": "encoded-roundtrip",
        "exitCode": 0,
        "recordingLogSha256": hashlib.sha256(output.encode()).hexdigest(),
        "replayLogSha256": hashlib.sha256(replay_output.encode()).hexdigest(),
        "resourceAdmission": admission,
    })
    for name, source in (("local-context", context),):
        admission = require_resources(name)
        result = subprocess.run(
            ["lake", "env", "lean", "-j1", f"--load-dynlib={dylib}", "-R", str(work), str(source)],
            cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=180, check=False,
        )
        output_path = work / f"{name}.log"
        output_path.write_text(result.stdout, encoding="utf-8")
        results.append({
            "name": name,
            "exitCode": result.returncode,
            "logSha256": hashlib.sha256(result.stdout.encode()).hexdigest(),
            "resourceAdmission": admission,
        })
        if result.returncode:
            raise RuntimeError(f"{name} failed; see {output_path}")

    summary = {
        "schema": 1,
        "kind": "simp_engine_local_context_regression",
        "boundarySha256": hashlib.sha256((ROOT / "ExplicitLean/SimpEngine/Boundary.lean").read_bytes()).hexdigest(),
        "fixtureSha256": hashlib.sha256(FIXTURE.encode()).hexdigest(),
        "results": results,
        "work": str(work),
    }
    target = LAKE / "replay-fixes" / "context-fixture-summary.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"summary": str(target), "results": results}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
        print(f"local-context-check: {error}", file=sys.stderr)
        raise SystemExit(2)
