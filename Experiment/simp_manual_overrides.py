#!/usr/bin/env python3
"""Pinned, reviewable source replacements for exceptional ``simp`` calls.

The boundary recorder handles the common case.  This table is the deliberately
small escape hatch for calls whose elaboration creates search-only local state:
each entry is bound to exact Mathlib bytes and an occurrence identity, retains
the original call as comments, and is still checked by compilation and the
declaration oracle.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from pathlib import PurePosixPath
import re
from typing import Any

import simp_engine_inventory as inventory


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PATH = ROOT / "Experiment" / "simp_manual_overrides.json"
KIND = "simp_manual_overrides"
SCHEMA = 1
TOP_LEVEL_FIELDS = frozenset(
    {"kind", "schema", "mathlibCommit", "lean", "overrides"}
)
LEAN_FIELDS = frozenset({"version", "commit"})
OVERRIDE_FIELDS = frozenset(
    {
        "module",
        "moduleSourceSha256",
        "occurrence",
        "startByte",
        "endByte",
        "source",
        "replacement",
    }
)
BANNED_SEARCH_TOKENS = frozenset(
    {
        "aesop",
        "aesop?",
        "all_goals",
        "any_goals",
        "apply?",
        "assumption?",
        "by?",
        "decide?",
        "exact?",
        "field_simp",
        "first",
        "focus",
        "grind",
        "library_search",
        "linarith",
        "native_decide",
        "nlinarith",
        "norm_num",
        "omega",
        "positivity",
        "repeat",
        "repeat'",
        "ring",
        "ring_nf",
        "rw?",
        "run_tac",
        "simpa",
        "simp",
        "simp?",
        "simp_all",
        "simp_all?",
        "simp_arith",
        "simp_rw",
        "solve_by_elim",
        "solve",
        "try",
        "try?",
    }
)
BANNED_SEARCH_PATTERN = re.compile(
    r"(?<![\w'])(?:"
    + "|".join(re.escape(token) for token in sorted(BANNED_SEARCH_TOKENS, key=len, reverse=True))
    + r")(?![\w'])"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise RuntimeError(f"{label} must be a nonempty string")
    return value


def _offset(value: object, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise RuntimeError(f"{label} must be a nonnegative integer")
    return value


def load_database(
    path: Path = DEFAULT_PATH,
) -> tuple[dict[str, object], list[dict[str, Any]]]:
    try:
        value = json.loads(path.read_bytes())
    except (OSError, json.JSONDecodeError) as error:
        raise RuntimeError(f"cannot read manual override database {path}: {error}") from error
    if not isinstance(value, dict) or set(value) != TOP_LEVEL_FIELDS:
        raise RuntimeError("manual override database has invalid top-level fields")
    if value.get("kind") != KIND or value.get("schema") != SCHEMA:
        raise RuntimeError("manual override database has unsupported identity")
    mathlib_commit = _string(value.get("mathlibCommit"), "manual override mathlibCommit")
    if len(mathlib_commit) != 40 or any(ch not in "0123456789abcdef" for ch in mathlib_commit):
        raise RuntimeError("manual override database has invalid Mathlib commit")
    lean = value.get("lean")
    if not isinstance(lean, dict) or set(lean) != LEAN_FIELDS:
        raise RuntimeError("manual override database has invalid Lean identity")
    lean_version = _string(lean.get("version"), "manual override Lean version")
    lean_commit = _string(lean.get("commit"), "manual override Lean commit")
    if len(lean_commit) != 40 or any(ch not in "0123456789abcdef" for ch in lean_commit):
        raise RuntimeError("manual override database has invalid Lean commit")
    raw = value.get("overrides")
    if not isinstance(raw, list):
        raise RuntimeError("manual override database overrides must be an array")
    result: list[dict[str, Any]] = []
    identities: set[str] = set()
    ranges: dict[str, list[tuple[int, int]]] = {}
    for index, entry in enumerate(raw):
        if not isinstance(entry, dict) or set(entry) != OVERRIDE_FIELDS:
            raise RuntimeError(f"manual override {index} has invalid fields")
        checked = dict(entry)
        module = _string(checked.get("module"), f"manual override {index} module")
        module_path = PurePosixPath(module)
        if (
            module_path.is_absolute()
            or module != module_path.as_posix()
            or "\\" in module
            or not module_path.parts
            or module_path.parts[0] != "Mathlib"
            or any(part in {"", ".", ".."} for part in module_path.parts)
            or not module.endswith(".lean")
        ):
            raise RuntimeError(f"manual override {index} has invalid Mathlib module path")
        occurrence = _string(
            checked.get("occurrence"), f"manual override {index} occurrence"
        )
        if occurrence in identities:
            raise RuntimeError(f"duplicate manual override occurrence: {occurrence}")
        identities.add(occurrence)
        start = _offset(checked.get("startByte"), f"manual override {index} startByte")
        end = _offset(checked.get("endByte"), f"manual override {index} endByte")
        if end <= start:
            raise RuntimeError(f"manual override {index} has an empty or reversed range")
        for prior_start, prior_end in ranges.setdefault(module, []):
            if start < prior_end and prior_start < end:
                raise RuntimeError(f"overlapping manual overrides in {module}")
        ranges[module].append((start, end))
        source = _string(checked.get("source"), f"manual override {index} source")
        replacement = _string(
            checked.get("replacement"), f"manual override {index} replacement"
        )
        if replacement == source or BANNED_SEARCH_PATTERN.search(replacement):
            raise RuntimeError(f"manual override {occurrence} is not an explicit replacement")
        digest = _string(
            checked.get("moduleSourceSha256"),
            f"manual override {index} moduleSourceSha256",
        )
        if len(digest) != 64 or any(ch not in "0123456789abcdef" for ch in digest):
            raise RuntimeError(f"manual override {index} has invalid source digest")
        result.append(checked)
    expected = sorted(
        result, key=lambda entry: (str(entry["module"]), int(entry["startByte"]))
    )
    if result != expected:
        raise RuntimeError("manual overrides are not in canonical module/range order")
    environment = {
        "mathlibCommit": mathlib_commit,
        "lean": {"version": lean_version, "commit": lean_commit},
    }
    return environment, result


def load(path: Path = DEFAULT_PATH) -> list[dict[str, Any]]:
    return load_database(path)[1]


def validate_against_source(
    module: str, source: bytes, entries: list[dict[str, Any]]
) -> None:
    module_entries = [entry for entry in entries if entry["module"] == module]
    for entry in module_entries:
        if sha256(source) != entry["moduleSourceSha256"]:
            raise RuntimeError(f"manual override module source hash changed: {module}")
        start, end = int(entry["startByte"]), int(entry["endByte"])
        if end > len(source):
            raise RuntimeError(f"manual override range exceeds source: {entry['occurrence']}")
        actual = source[start:end].decode("utf-8")
        if actual != entry["source"]:
            raise RuntimeError(f"manual override source bytes changed: {entry['occurrence']}")
        expected_id = inventory.occurrence_id(module, start, end)
        if entry["occurrence"] != expected_id:
            raise RuntimeError(
                f"manual override occurrence identity changed: {entry['occurrence']} != {expected_id}"
            )


def _column_at(source: bytes, offset: int) -> int:
    prefix = source[:offset].decode("utf-8")
    return len(prefix.rsplit("\n", 1)[-1].expandtabs(8))


def render(entry: dict[str, Any], source: bytes) -> bytes:
    start, end = int(entry["startByte"]), int(entry["endByte"])
    original = source[start:end].decode("utf-8")
    replacement = str(entry["replacement"])
    first, separator, rest = replacement.partition("\n")
    branch_indent = " " * (_column_at(source, start) + 2)
    comments = [branch_indent + "-- Original simp:"]
    comments.extend(branch_indent + "-- " + line for line in original.split("\n"))
    suffix = rest if separator else branch_indent[:-2]
    return (first + "\n" + "\n".join(comments) + "\n" + suffix).encode("utf-8")


def apply(module: str, source: bytes, entries: list[dict[str, Any]]) -> bytes:
    validate_against_source(module, source, entries)
    selected = [entry for entry in entries if entry["module"] == module]
    chunks: list[bytes] = []
    cursor = 0
    for entry in selected:
        start, end = int(entry["startByte"]), int(entry["endByte"])
        chunks.extend((source[cursor:start], render(entry, source)))
        cursor = end
    chunks.append(source[cursor:])
    return b"".join(chunks)


def entries_by_module(entries: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    result: dict[str, list[dict[str, Any]]] = {}
    for entry in entries:
        result.setdefault(str(entry["module"]), []).append(entry)
    return result
