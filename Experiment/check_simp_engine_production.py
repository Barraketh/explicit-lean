#!/usr/bin/env python3
"""Compare the pinned fork with upstream simp inside bounded Mathlib modules."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import simp_engine_inventory as coverage


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / ".lake" / "simp-engine-reference"
MODULES = (
    "Mathlib/Data/List/DropRight.lean",
    "Mathlib/CategoryTheory/EqToHom.lean",
)


def dynamic_library() -> str:
    build = subprocess.run(
        ["lake", "build", "ExplicitLean:shared"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=180,
    )
    if build.returncode != 0:
        raise RuntimeError(build.stdout)
    query = subprocess.run(
        ["lake", "query", "ExplicitLean:shared", "--json"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
    )
    if query.returncode != 0:
        raise RuntimeError(query.stdout + query.stderr)
    return json.loads(query.stdout.strip())


def instrument(module: str) -> tuple[Path, int]:
    source_path = coverage.MATHLIB / module
    source = source_path.read_bytes()
    entries = [
        entry
        for entry in coverage.syntax_inventory_file(source_path, module, 180)
        if entry["kind"] in coverage.SUPPORTED_KINDS
    ]
    source = coverage.rewrite_simp_heads(
        source, entries, lambda _entry: "simp_engine_reference"
    )
    source = coverage.inject_import(source, "ExplicitLean.SimpEngine.Reference")
    destination = OUTPUT / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination, len(entries)


def main() -> None:
    dynlib = dynamic_library()
    total = 0
    for module in MODULES:
        destination, count = instrument(module)
        if count == 0:
            raise RuntimeError(f"bounded production module has no supported simp calls: {module}")
        command = coverage.lean_command(destination)
        command.insert(3, f"--load-dynlib={dynlib}")
        code, output, _ = coverage.run(command, timeout=300)
        log = OUTPUT / f"{coverage.occurrence_id(module, 0, 0)}.log"
        log.write_text(output, encoding="utf-8")
        if code != 0:
            raise RuntimeError(f"pinned engine mismatch in {module}; see {log}")
        total += count
    print(
        "pinned simp engine production equivalence: "
        f"{len(MODULES)} modules, {total} simp calls: ok"
    )


if __name__ == "__main__":
    main()
