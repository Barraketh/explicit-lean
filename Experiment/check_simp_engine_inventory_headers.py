#!/usr/bin/env python3
"""Remaining-call scans must parse the replay syntax imported by the source."""
from pathlib import Path
import hashlib
import json
import shutil
import sys
import tempfile

import simp_engine_inventory as inventory

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "Experiment/SimpEngineInventoryHeaderFixture.lean"
CALL = "simp only [go_append tl _, Array.toListAppend_eq, append_assoc, Array.toList_push]"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parent = ROOT / ".lake/inventory-header-controls"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="controls-", dir=parent))
    source = FIXTURE.read_text()
    assert source.count(CALL) == 1
    inputs = [Path(__file__).resolve(), FIXTURE, ROOT / "lean-toolchain",
              ROOT / "Experiment/SimpEngineInventory.lean",
              ROOT / "Experiment/simp_engine_inventory.py",
              ROOT / "Experiment/boundary_materialize_shard.py",
              ROOT / "ExplicitLean/SimpEngine/Inventory.lean",
              ROOT / "ExplicitLean/SimpEngine/Boundary/Tactic.lean",
              ROOT / ".lake/build/bin/simpEngineInventory"]
    before = {str(path): sha(path) for path in inputs}
    archived = []
    for index, path in enumerate(inputs):
        destination = work / "inputs" / f"{index}-{path.name}"
        destination.parent.mkdir(exist_ok=True)
        shutil.copy2(path, destination)
        archived.append({"path": str(path), "archivedPath": str(destination), "sha256": sha(path)})
    records = []
    # Aggregate parsing historically returns zero here, but that is diagnostic:
    # an improvement to it must not break the actual-header correctness checks.
    for label, text, header, expected in [
        ("aggregate-diagnostic", source, False, None),
        ("actual-header-one-call", source, True, 1),
        ("actual-header-no-calls", source.replace(CALL, "skip"), True, 0),
    ]:
        path = work / f"{label}.lean"
        path.write_text(text)
        command = [sys.executable, str(ROOT / "Experiment/lean_toolchain_cache.py"), "inventory"]
        if header:
            command.append("--header-imports")
        code, output, _ = inventory.run(command + [str(path)], timeout=120)
        log = path.with_suffix(".log")
        log.write_text(output)
        if code or "FULL_FALLBACK" in output or "ELABORATION_ERRORS_ALLOWED" in output:
            raise RuntimeError(f"{label}: expected a clean syntax parse; see {log}")
        entries = [json.loads(line) for line in output.splitlines() if line.startswith("{")]
        if expected is not None and len(entries) != expected:
            raise RuntimeError(f"{label}: expected {expected} calls, got {len(entries)}")
        if expected == 1:
            entry = entries[0]
            assert text.encode()[entry["startByte"]:entry["endByte"]].decode() == CALL
        records.append({"case": label, "expectedCount": expected, "actualCount": len(entries),
                        "source": str(path), "sourceSha256": sha(path),
                        "log": str(log), "logSha256": sha(log)})
    if {str(path): sha(path) for path in inputs} != before:
        raise RuntimeError("inventory inputs changed during validation")
    for item in archived:
        assert sha(Path(item["archivedPath"])) == item["sha256"]
    report = {"status": "passed", "acceptedCampaignCoverage": False,
              "records": records, "inputs": archived}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(work / "report.json")


if __name__ == "__main__":
    main()
