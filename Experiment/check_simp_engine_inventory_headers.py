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
LOCAL_SYNTAX_SOURCE = """\
import Mathlib.Data.Nat.Basic

namespace LocalInventorySyntax
scoped syntax "localInventoryTerm" : term
scoped macro_rules | `(localInventoryTerm) => `(0)
end LocalInventorySyntax

open scoped LocalInventorySyntax

example : True := by
  have : Nat := localInventoryTerm
  simp
"""


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
    # Aggregate parsing lacks the replay syntax imported by this source. It must
    # now detect that recovery, use the full parser, and retain the occurrence.
    for label, text, header, allow_errors, expected_source, expect_fallback in [
        ("aggregate-diagnostic", source, False, True, CALL, True),
        ("actual-header-one-call", source, True, False, CALL, False),
        ("actual-header-no-calls", source.replace(CALL, "skip"), True, False, None, False),
        ("actual-header-local-syntax", LOCAL_SYNTAX_SOURCE, True, False, "simp", False),
    ]:
        path = work / f"{label}.lean"
        path.write_text(text)
        command = [sys.executable, str(ROOT / "Experiment/lean_toolchain_cache.py"), "inventory"]
        if allow_errors:
            command.append("--allow-elaboration-errors")
        if header:
            command.append("--header-imports")
        code, output, _ = inventory.run(command + [str(path)], timeout=120)
        log = path.with_suffix(".log")
        log.write_text(output)
        fallback = "FULL_FALLBACK" in output
        if code or fallback != expect_fallback:
            raise RuntimeError(f"{label}: expected a clean syntax parse; see {log}")
        entries = [json.loads(line) for line in output.splitlines() if line.startswith("{")]
        expected_count = int(expected_source is not None)
        if len(entries) != expected_count:
            raise RuntimeError(f"{label}: expected {expected_count} calls, got {len(entries)}")
        if expected_source is not None:
            entry = entries[0]
            actual_source = text.encode()[entry["startByte"]:entry["endByte"]].decode()
            if actual_source != expected_source:
                raise RuntimeError(
                    f"{label}: expected source {expected_source!r}, got {actual_source!r}"
                )
        records.append({"case": label, "expectedCount": expected_count,
                        "actualCount": len(entries),
                        "expectedFallback": expect_fallback, "actualFallback": fallback,
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
