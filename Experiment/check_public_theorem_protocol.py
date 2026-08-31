#!/usr/bin/env python3
"""Exercise the public-theorem wire validator against captured codec payloads.

This is a protocol-shape check.  It does not authenticate a capture, resolve
declarations, or establish kernel validity of expressions or metadata tags.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Callable

from boundary_public_theorem_codec import validate_public_theorem_payload


ROOT = Path(__file__).resolve().parents[1]


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _latest_report() -> Path:
    reports = list((ROOT / ".lake" / "public-theorem-codec").glob(
        "fixture-*/report.json"))
    if not reports:
        raise RuntimeError("no public-theorem codec fixture report found")
    return max(reports, key=lambda path: (path.stat().st_mtime_ns, str(path)))


def _load_payload(path: Path) -> tuple[list[Any], object]:
    payload = json.loads(path.read_text())
    if not isinstance(payload, list) or len(payload) < 2:
        raise RuntimeError(f"{path} does not contain a public theorem payload")
    theorem = json.loads(payload[1])
    if not isinstance(theorem, list) or len(theorem) < 2:
        raise RuntimeError(f"{path} does not contain a theorem payload")
    return payload, theorem[1]


def _report_path(value: object, report_path: Path, label: str) -> Path:
    if not isinstance(value, str):
        raise RuntimeError(f"{label} must be a path string")
    path = Path(value)
    return (report_path.parent / path).resolve() if not path.is_absolute() else path.resolve()


def _mutate_inner(payload: list[Any], mutate: Callable[[list[Any]], None]) -> str:
    mutated = list(payload)
    theorem = json.loads(mutated[1])
    mutate(theorem)
    mutated[1] = json.dumps(theorem, separators=(",", ":"), ensure_ascii=False)
    return json.dumps(mutated, separators=(",", ":"), ensure_ascii=False)


def _must_reject(source: str, expected_name: object, label: str) -> dict[str, object]:
    try:
        validate_public_theorem_payload(source, expected_name, label)
    except RuntimeError:
        return {"case": label, "rejected": True}
    raise RuntimeError(f"mutation {label} was accepted")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--report", type=Path, default=None,
        help="codec fixture report.json (defaults to the newest fixture)")
    parser.add_argument(
        "--evidence", type=Path,
        default=ROOT / ".lake" / "public-theorem-codec" / "wire-validator-report.json")
    args = parser.parse_args()

    report_path = (args.report or _latest_report()).resolve()
    report = json.loads(report_path.read_text())
    if not isinstance(report, dict) or report.get("status") != "passed":
        raise RuntimeError(f"codec report is not a passed report: {report_path}")

    payload_paths = [_report_path(report.get("payload"), report_path, "payload")]
    additional = report.get("additionalPayloads", [])
    if not isinstance(additional, list):
        raise RuntimeError("additionalPayloads must be an array")
    for index, item in enumerate(additional):
        if not isinstance(item, dict):
            raise RuntimeError(f"additionalPayloads[{index}] must be an object")
        payload_paths.append(_report_path(item.get("path"), report_path,
                                          f"additionalPayloads[{index}].path"))
    payloads: list[tuple[Path, list[Any], object]] = []
    for path in payload_paths:
        payload, expected_name = _load_payload(path)
        validate_public_theorem_payload(
            json.dumps(payload, separators=(",", ":"), ensure_ascii=False),
            expected_name,
            f"captured payload {path.name}")
        payloads.append((path, payload, expected_name))

    base_path, base, expected_name = payloads[0]
    mutations = [
        ("wrong-tag-type", "outer", lambda value: value.__setitem__(2, 1)),
        ("wrong-cache-shape", "outer", lambda value: value.__setitem__(4, [])),
        ("wrong-cache-expression", "outer",
         lambda value: value.__setitem__(4, ["not-an-expression-dag", False, False, None])),
        ("wrong-group", "inner",
         lambda theorem: theorem.__setitem__(2, [theorem[1], [["s", "foreign"]]])),
        ("wrong-name", "inner", lambda theorem: theorem.__setitem__(1, [["s", "foreign"]])),
        ("wrong-value", "inner",
         lambda theorem: theorem.__setitem__(5, "not-an-expression-dag")),
    ]
    mutation_results: list[dict[str, object]] = []
    for name, location, mutate in mutations:
        if location == "inner":
            source = _mutate_inner(base, mutate)
        else:
            mutated = list(base)
            mutate(mutated)
            source = json.dumps(mutated, separators=(",", ":"), ensure_ascii=False)
        mutation_results.append(_must_reject(source, expected_name, name))

    evidence = {
        "kind": "public_theorem_codec_wire_validator",
        "status": "passed",
        "sourceReport": str(report_path),
        "sourceReportSha256": _sha256(report_path),
        "positivePayloads": [
            {"path": str(path), "sha256": _sha256(path), "expectedName": name}
            for path, _, name in payloads
        ],
        "baseMutationPayload": str(base_path),
        "mutations": mutation_results,
        "validator": {
            "path": str(Path(__file__).with_name("boundary_public_theorem_codec.py")),
            "sha256": _sha256(Path(__file__).with_name("boundary_public_theorem_codec.py")),
        },
        "limitation": (
            "Structural wire validation does not authenticate capture or prove "
            "kernel validity of expressions, declarations, or metadata tags."
        ),
    }
    args.evidence.parent.mkdir(parents=True, exist_ok=True)
    args.evidence.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(json.dumps(evidence, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
