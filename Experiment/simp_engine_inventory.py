#!/usr/bin/env python3
"""Small syntax-aware instrumentation helpers for the schema-16 engine tests."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import time
from typing import Any, Callable


ROOT = Path(__file__).resolve().parent.parent
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"
SUPPORTED_KINDS = {"simp", "simp_only"}


def run(command: list[str], *, timeout: int | None = None) -> tuple[int, str, float]:
    started = time.monotonic()
    try:
        result = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
        return result.returncode, result.stdout, time.monotonic() - started
    except subprocess.TimeoutExpired as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return 124, output + "\nexplicit-lean: compilation timed out\n", time.monotonic() - started


def occurrence_id(module: str, start: int, end: int) -> str:
    identity = f"{module}:{start}:{end}".encode()
    return hashlib.sha256(identity).hexdigest()[:16]


def syntax_inventory_file(path: Path, module: str, timeout: int) -> list[dict[str, Any]]:
    command = [
        "lake",
        "env",
        "lean",
        "--run",
        "Experiment/SimpEngineInventory.lean",
        str(path.resolve()),
    ]
    code, output, _ = run(command, timeout=timeout)
    if code != 0:
        raise RuntimeError(f"syntax inventory failed for {path}:\n{output}")
    result: list[dict[str, Any]] = []
    for line in output.splitlines():
        if not line.startswith("{"):
            continue
        entry = json.loads(line)
        entry.pop("file", None)
        entry["module"] = module
        entry["id"] = occurrence_id(module, entry["startByte"], entry["endByte"])
        result.append(entry)
    return result


def validate_occurrence(source: bytes, entry: dict[str, Any]) -> None:
    start, end = int(entry["startByte"]), int(entry["endByte"])
    if not 0 <= start < end <= len(source):
        raise RuntimeError(
            f"invalid inventory range for {entry['module']}:{entry['line']}: "
            f"{start}:{end} in {len(source)} bytes"
        )
    try:
        actual = source[start:end].decode("utf-8")
    except UnicodeDecodeError as error:
        raise RuntimeError(
            f"inventory range splits UTF-8 for {entry['module']}:{entry['line']}"
        ) from error
    if actual != entry["source"]:
        raise RuntimeError(
            f"stale inventory for {entry['module']}:{entry['line']}: "
            f"expected {entry['source']!r}, found {actual!r}"
        )
    if source[start : start + 4] != b"simp":
        raise RuntimeError(
            f"supported occurrence does not start with `simp`: "
            f"{entry['module']}:{entry['line']}"
        )


def rewrite_simp_heads(
    source: bytes,
    entries: list[dict[str, Any]],
    replacement: Callable[[dict[str, Any]], str],
) -> bytes:
    """Replace only each `simp` token so nested occurrences compose exactly."""
    starts: set[int] = set()
    for entry in entries:
        validate_occurrence(source, entry)
        start = int(entry["startByte"])
        if start in starts:
            raise RuntimeError(
                f"duplicate instrumentation start for {entry['module']}:{entry['line']}"
            )
        starts.add(start)
    for entry in sorted(entries, key=lambda item: int(item["startByte"]), reverse=True):
        start = int(entry["startByte"])
        source = source[:start] + replacement(entry).encode("utf-8") + source[start + 4 :]
    return source


def inject_import(source: bytes, imported: str) -> bytes:
    marker = b"module\n"
    position = source.find(marker)
    if position < 0:
        raise RuntimeError("Lean source has no `module` header")
    insertion = position + len(marker)
    return source[:insertion] + f"\nimport {imported}\n".encode() + source[insertion:]


def lean_command(path: Path) -> list[str]:
    command = [
        "lake",
        "env",
        "lean",
        "-Dlinter.unusedVariables=false",
        "-Dlinter.unusedSimpArgs=false",
        "-Dlinter.unreachableTactic=false",
        "-DmaxHeartbeats=0",
    ]
    try:
        mathlib_index = path.parts.index("Mathlib")
    except ValueError:
        pass
    else:
        # Preserve anonymous declaration names from the source module.
        command.extend(["-R", str(Path(*path.parts[:mathlib_index]))])
    command.append(str(path))
    return command
