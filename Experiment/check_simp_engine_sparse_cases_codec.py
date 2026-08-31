#!/usr/bin/env python3
"""Validate the captured sparse-helper wire form without loading Lean.

This is regression evidence only.  It validates an archived payload and
malformed transitions; kernel and typed cache checks remain in the Lean
codec.  Every input is hashed before and after the controls.
"""

from __future__ import annotations

import hashlib
import argparse
import json
import os
import sys
from pathlib import Path
import shutil
import tempfile

DEFAULT_ROOT = Path(__file__).resolve().parents[1]
ROOT = Path(os.environ.get("EXPLICIT_LEAN_PROJECT_ROOT", str(DEFAULT_ROOT))).resolve()
sys.path.insert(0, str(ROOT / "Experiment"))
from boundary_expr_codec import validate_sparse_payload
DRIVER = Path(__file__).resolve()


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def extract_payload(path: Path) -> str:
    for line in path.read_text().splitlines():
        if line.startswith("PAYLOAD "):
            return line.removeprefix("PAYLOAD ")
    raise RuntimeError(f"no sparse payload in {path}")

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
        ROOT / "ExplicitLean/SimpEngine/Boundary/SparseCasesCodec.lean",
        ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/SparseCasesCodec.olean",
        ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/SparseCasesCodec.ir",
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
    work = Path(tempfile.mkdtemp(prefix="sparse-cases-", dir=evidence_dir))
    archive = work / "inputs"
    archive.mkdir()
    archive_paths = [payload_log,
                 ROOT / "Experiment/boundary_expr_codec.py",
                 ROOT / "ExplicitLean/SimpEngine/Boundary/SparseCasesCodec.lean",
                 DRIVER]
    if manifest_path is not None:
        archive_paths.insert(0, manifest_path)
    archived_inputs = archive_inputs(archive_paths, archive)
    raw = extract_payload(payload_log)
    payload = json.loads(raw)
    validate_sparse_payload(raw, payload[1])
    cases: list[dict[str, object]] = [{"case": "captured-payload", "result": "accepted"}]

    controls = []
    value = json.loads(raw); value[0] = "boundary_sparse_cases_v2"
    controls.append(("header-version", value, "invalid sparse cases header"))
    value = json.loads(raw); value[1] = [["s", "publicHelper"]]
    controls.append(("public-helper-name", value, "mismatched helper name"))
    value = json.loads(raw); value[3][2] = False
    controls.append(("public-cache-key", value, "cache key is not private"))
    value = json.loads(raw); value[3][1] = value[3][1] * 2
    controls.append(("duplicate-constructor", value, "duplicate sparse constructors"))
    value = json.loads(raw); value[4][2] += 1
    controls.append(("metadata-arity", value, "metadata arity is inconsistent"))
    value = json.loads(raw); definition = json.loads(value[2]); definition[4] = ["opaque"]
    value[2] = json.dumps(definition, separators=(",", ":"))
    controls.append(("non-abbreviation", value, "safe abbreviation"))
    value = json.loads(raw); value[2] = "[]"
    controls.append(("malformed-definition", value, "invalid safe singleton definition header"))
    for name, value, expected in controls:
        try:
            validate_sparse_payload(json.dumps(value, separators=(",", ":")), payload[1])
        except RuntimeError as error:
            if expected not in str(error):
                raise RuntimeError(f"{name}: wrong rejection: {error}") from error
        else:
            raise RuntimeError(f"{name}: malformed payload was accepted")
        cases.append({"case": name, "result": "rejected", "expected": expected})
    after = input_snapshot(manifest_path, payload_log)
    if before != after:
        raise RuntimeError("sparse codec inputs changed during controls")
    report = {
        "status": "passed",
        "acceptedCampaignCoverage": False,
        "validatorScope": "wire structure only; Lean validates definitions and typed cache state",
        "cases": cases,
        "inputSha256Before": before,
        "inputSha256After": after,
        "archivedInputs": archived_inputs,
        "archivedInputDirectory": str(archive),
    }
    report_path = work / "report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"sparse cases wire validator: {len(cases)} cases passed")
    print(f"report={report_path}")


if __name__ == "__main__":
    main()
