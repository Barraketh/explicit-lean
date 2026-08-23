#!/usr/bin/env python3
"""Exercise record mode over the bounded production modules."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import simp_engine_inventory as coverage


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / ".lake" / "simp-engine-recording"
MODULES = (
    "Mathlib/Data/List/DropRight.lean",
    "Mathlib/CategoryTheory/EqToHom.lean",
)


def dynamic_library() -> str:
    build = subprocess.run(
        ["lake", "build", "ExplicitLean:shared"], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300,
    )
    if build.returncode:
        raise RuntimeError(build.stdout)
    query = subprocess.run(
        ["lake", "query", "ExplicitLean:shared", "--json"], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
    )
    if query.returncode:
        raise RuntimeError(query.stdout + query.stderr)
    return json.loads(query.stdout.strip())


def instrument(module: str) -> tuple[Path, int]:
    source_path = coverage.MATHLIB / module
    source = source_path.read_bytes()
    entries = [entry for entry in coverage.syntax_inventory_file(source_path, module, 180)
               if entry["kind"] in coverage.SUPPORTED_KINDS]
    for entry in sorted(entries, key=lambda item: item["startByte"], reverse=True):
        original = entry["source"]
        replacement = "simp_engine_recording" + original[len("simp") :]
        source = coverage.replace_bytes(source, entry, replacement)
    source = coverage.inject_import(source, "ExplicitLean.SimpEngine.Recording")
    destination = OUTPUT / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination, len(entries)


def main() -> None:
    dynlib = dynamic_library()
    total = 0
    for module in MODULES:
        destination, count = instrument(module)
        if not count:
            raise RuntimeError(f"bounded production module has no supported simp calls: {module}")
        command = coverage.lean_command(destination)
        command.insert(3, f"--load-dynlib={dynlib}")
        code, output, _ = coverage.run(command, timeout=600)
        log = OUTPUT / f"{coverage.occurrence_id(module, 0, 0)}.log"
        log.write_text(output, encoding="utf-8")
        if code:
            raise RuntimeError(f"record mode mismatch in {module}; see {log}")
        if output.count("SIMP_ENGINE_RECORDING") < count:
            raise RuntimeError(
                f"too few recording executions in {module}: "
                f"{output.count('SIMP_ENGINE_RECORDING')} < {count}"
            )
        total += count
    print(f"schema-16 production recording: {len(MODULES)} modules, {total} simp calls: ok")


if __name__ == "__main__":
    main()
