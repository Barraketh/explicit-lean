#!/usr/bin/env python3
"""Validate a captured sparse-aware matcher bundle and wire negatives.

This standalone driver deliberately uses the archived JSON evidence and the
Python structural validator. It does not load the stale shared Boundary
library; checked definitions, declaration bodies, and typed extension/cache
transitions remain obligations of the Lean codec and its separate controls.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
import shutil
import tempfile
DEFAULT_ROOT = Path(__file__).resolve().parents[1]
ROOT = Path(os.environ.get("EXPLICIT_LEAN_PROJECT_ROOT", str(DEFAULT_ROOT))).resolve()
sys.path.insert(0, str(ROOT / "Experiment"))
from boundary_expr_codec import validate_matcher_payload
DRIVER = Path(__file__).resolve()
def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()
def extract_payload(path: Path) -> str:
    for line in path.read_text().splitlines():
        if line.startswith("PAYLOAD "):
            return line.removeprefix("PAYLOAD ")
    raise RuntimeError(f"no matcher payload in {path}")
def archive_inputs(paths: list[Path], archive: Path) -> list[dict[str, str]]:
    result = []
    for path in paths:
        target = archive / path.name
        if target.exists() and digest(target) != digest(path):
            target = archive / (digest(path)[:12] + "-" + path.name)
        shutil.copy2(path, target)
        result.append({"path": str(path), "sha256": digest(path), "archivedPath": str(target)})
    return result
def input_snapshot(manifest_path: Path | None, payload_log: Path) -> dict[str, str]:
    result = {}
    if manifest_path is not None:
        manifest = json.loads(manifest_path.read_text())
        result[str(manifest_path)] = digest(manifest_path)
        for entry in manifest.get("entries", []):
            path = Path(entry["path"])
            if not path.is_file() or digest(path) != entry["sha256"]:
                raise RuntimeError(f"archived evidence changed or is missing: {path}")
            result[str(path)] = entry["sha256"]
    for path in [
        ROOT / "Experiment/boundary_expr_codec.py",
        ROOT / "Experiment/boundary_protocol.py",
        ROOT / "ExplicitLean/SimpEngine/Boundary/MatcherCodec.lean",
        ROOT / "ExplicitLean/SimpEngine/Boundary/SparseCasesCodec.lean",
        ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/MatcherCodec.olean",
        ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/MatcherCodec.ir",
        payload_log,
        DRIVER,
    ]:
        if not path.is_file():
            raise RuntimeError(f"required input is missing: {path}")
        result[str(path)] = digest(path)
    return result
def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--payload-log", type=Path, required=True)
    parser.add_argument("--evidence-manifest", type=Path)
    args = parser.parse_args()
    manifest_path = args.evidence_manifest.resolve() if args.evidence_manifest else None
    payload_log = args.payload_log.resolve()
    evidence_dir = ROOT / ".lake/sparse-probe"
    evidence_dir.mkdir(parents=True, exist_ok=True)
    before = input_snapshot(manifest_path, payload_log)
    work = Path(tempfile.mkdtemp(prefix="matcher-", dir=evidence_dir))
    archive = work / "inputs"
    archive.mkdir()
    archive_paths = [payload_log,
                 ROOT / "Experiment/boundary_expr_codec.py",
                 ROOT / "Experiment/boundary_protocol.py",
                 ROOT / "ExplicitLean/SimpEngine/Boundary/MatcherCodec.lean",
                 DRIVER]
    if manifest_path is not None:
        archive_paths.insert(0, manifest_path)
    archived_inputs = archive_inputs(archive_paths, archive)
    raw = extract_payload(payload_log)
    payload = json.loads(raw)
    validate_matcher_payload(raw, payload[1])
    cases: list[dict[str, object]] = [{"case": "captured-payload", "result": "accepted"}]
    controls = []
    value = json.loads(raw); value[0] = "boundary_matcher_bundle_v1"
    controls.append(("header-version", value, "invalid matcher bundle header"))
    value = json.loads(raw); value[1] = [["s", "OtherAnchor"]]
    controls.append(("foreign-anchor", value, "invalid matcher bundle v2 header"))
    value = json.loads(raw)[:-1]
    controls.append(("field-count", value, "invalid matcher bundle v2 header"))
    value = json.loads(raw); value[7][0][0] = value[7][1][0]
    controls.append(("equation-order", value, "invalid captured equation metadata"))
    value = json.loads(raw); theorem = json.loads(value[7][0][1]); theorem[2] = []
    value[7][0][1] = json.dumps(theorem, separators=(",", ":"))
    controls.append(("theorem-group", value, "theorem declaration group must be singleton"))
    value = json.loads(raw); value[15][0][0] = [["s", "other"]]
    controls.append(("helper-name", value, "sparse helper is outside splitter namespace"))
    value = json.loads(raw); sparse = json.loads(value[15][0][1]); definition = json.loads(sparse[2])
    definition[4] = ["opaque"]; sparse[2] = json.dumps(definition, separators=(",", ":"))
    value[15][0][1] = json.dumps(sparse, separators=(",", ":"))
    controls.append(("helper-definition", value, "safe abbreviation"))
    value = json.loads(raw); value[9][1].append([["s", "bogus"]])
    controls.append(("matcher-state-transition", value, "invalid matcher snapshot transition"))
    value = json.loads(raw); value[17] = []
    controls.append(("async-cache-transition", value, "async sparse cache lacks a captured helper"))
    value = json.loads(raw); value[16] = value[17]
    controls.append(("async-before-transition", value, "invalid async sparse cache transition"))
    value = json.loads(raw); value[18].append([[], [["s", "bogus"]]])
    controls.append(("caller-cache-invalid", value, "invalid sparse cache key"))
    value = json.loads(raw); value[2][0] += 1
    controls.append(("splitter-metadata", value, "unrelated splitter metadata"))
    for name, value, expected in controls:
        try:
            validate_matcher_payload(json.dumps(value, separators=(",", ":")), payload[1])
        except RuntimeError as error:
            if expected not in str(error):
                raise RuntimeError(f"{name}: wrong rejection: {error}") from error
        else:
            raise RuntimeError(f"{name}: malformed payload was accepted")
        cases.append({"case": name, "result": "rejected", "expected": expected})
    after = input_snapshot(manifest_path, payload_log)
    if before != after:
        raise RuntimeError("matcher codec inputs changed during controls")
    report = {
        "status": "passed", "acceptedCampaignCoverage": False,
        "validatorScope": "wire structure only; Lean validates checked bodies and typed extension/cache state",
        "cases": cases, "inputSha256Before": before, "inputSha256After": after,
        "archivedInputs": archived_inputs,
        "archivedInputDirectory": str(archive),
    }
    report_path = work / "report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"matcher bundle wire validator: {len(cases)} cases passed")
    print(f"report={report_path}")
if __name__ == "__main__":
    main()
