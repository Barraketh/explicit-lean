#!/usr/bin/env python3
"""Authenticated replacements for non-``simp`` simp-family execution sites.

The ordinary simp-site renderer owns only executable ``simp``/``dsimp`` calls.
This overlay is a separate, deliberately sparse lane for broader-family calls
such as ``grind`` and ``simpa``.  Entries authenticate the original Mathlib
bytes; application is performed only after the ordinary renderer has produced
source, and every entry must be consumed exactly once.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
from typing import Any, Iterable

import simp_family_lint

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_PATH = ROOT / "Experiment" / "pipeline" / "broader_simp_family_overrides.json"
KIND = "broader_simp_family_overrides"
SCHEMA = 1
TOP_LEVEL_FIELDS = frozenset({"kind", "schema", "mathlibCommit", "lean", "moduleSourceSha256", "overrides"})
LEAN_FIELDS = frozenset({"version", "commit"})
ENTRY_FIELDS = frozenset({"module", "occurrence", "startByte", "endByte", "source", "replacement"})


def _nonempty_string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise RuntimeError(f"{label} must be a nonempty string")
    return value


def _offset(value: object, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise RuntimeError(f"{label} must be a nonnegative integer")
    return value


def _hex(value: object, label: str, length: int) -> str:
    result = _nonempty_string(value, label)
    if len(result) != length or any(ch not in "0123456789abcdef" for ch in result):
        raise RuntimeError(f"{label} must be {length} lowercase hexadecimal characters")
    return result


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _canonical(entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return sorted(entries, key=lambda entry: (str(entry["module"]), int(entry["startByte"])))


def load_database(path: Path = DEFAULT_PATH) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    try:
        value = json.loads(path.read_bytes())
    except (OSError, json.JSONDecodeError) as error:
        raise RuntimeError(f"cannot read broader overlay {path}: {error}") from error
    if not isinstance(value, dict) or set(value) != TOP_LEVEL_FIELDS:
        raise RuntimeError("broader overlay has invalid top-level fields")
    if value.get("kind") != KIND or value.get("schema") != SCHEMA:
        raise RuntimeError("broader overlay has unsupported identity")
    environment = {
        "mathlibCommit": _hex(value.get("mathlibCommit"), "mathlibCommit", 40),
        "lean": value.get("lean"),
    }
    if not isinstance(environment["lean"], dict) or set(environment["lean"]) != LEAN_FIELDS:
        raise RuntimeError("broader overlay has invalid Lean identity")
    environment["lean"] = {
        "version": _nonempty_string(environment["lean"].get("version"), "lean.version"),
        "commit": _hex(environment["lean"].get("commit"), "lean.commit", 40),
    }
    module_hash = _hex(value.get("moduleSourceSha256"), "moduleSourceSha256", 64)
    raw = value.get("overrides")
    if not isinstance(raw, list):
        raise RuntimeError("broader overlay overrides must be an array")
    entries: list[dict[str, Any]] = []
    occurrences: set[str] = set()
    ranges: dict[str, list[tuple[int, int]]] = {}
    for index, raw_entry in enumerate(raw):
        if not isinstance(raw_entry, dict) or set(raw_entry) != ENTRY_FIELDS:
            raise RuntimeError(f"broader overlay entry {index} has invalid fields")
        entry = dict(raw_entry)
        module = _nonempty_string(entry["module"], f"entry {index} module")
        module_path = PurePosixPath(module)
        if (module_path.is_absolute() or module != module_path.as_posix()
                or "\\" in module or not module_path.parts
                or module_path.parts[0] != "Mathlib"
                or any(part in {"", ".", ".."} for part in module_path.parts)
                or not module.endswith(".lean")):
            raise RuntimeError(f"entry {index} has an invalid Mathlib module path")
        occurrence = _nonempty_string(entry["occurrence"], f"entry {index} occurrence")
        if occurrence in occurrences:
            raise RuntimeError(f"duplicate broader overlay occurrence: {occurrence}")
        occurrences.add(occurrence)
        start = _offset(entry["startByte"], f"entry {index} startByte")
        end = _offset(entry["endByte"], f"entry {index} endByte")
        if end <= start:
            raise RuntimeError(f"broader overlay entry {index} has an empty or reversed range")
        for prior_start, prior_end in ranges.setdefault(module, []):
            if start < prior_end and prior_start < end:
                raise RuntimeError(f"overlapping broader overlays in {module}")
        source = _nonempty_string(entry["source"], f"entry {index} source")
        replacement = _nonempty_string(entry["replacement"], f"entry {index} replacement")
        if source == replacement:
            raise RuntimeError(f"broader overlay {occurrence} is unchanged")
        try:
            simp_family_lint.assert_clean(replacement, f"broader overlay {occurrence}")
        except (AssertionError, RuntimeError) as error:
            raise RuntimeError(f"broader overlay {occurrence} is not ordinary Lean: {error}") from error
        if any(token in replacement for token in ("sorry", "admit")):
            raise RuntimeError(f"broader overlay {occurrence} contains a proof hole")
        entry["module"] = module
        entry["occurrence"] = occurrence
        entry["startByte"] = start
        entry["endByte"] = end
        entry["source"] = source
        entry["replacement"] = replacement
        entries.append(entry)
    if entries != _canonical(entries):
        raise RuntimeError("broader overlay entries are not in canonical module/range order")
    return {**environment, "moduleSourceSha256": module_hash}, entries


def _validate_source(
    module: str,
    source: bytes,
    entries: Iterable[dict[str, Any]],
    module_hash: str,
    protected_ranges: Iterable[tuple[int, int]] = (),
) -> list[dict[str, Any]]:
    selected = [entry for entry in entries if entry["module"] == module]
    if not selected:
        return []
    if _sha256(source) != module_hash:
        raise RuntimeError(f"broader overlay module source hash changed: {module}")
    occupied = sorted((int(start), int(end)) for start, end in protected_ranges)
    previous_end = -1
    for entry in selected:
        start, end = int(entry["startByte"]), int(entry["endByte"])
        if end > len(source):
            raise RuntimeError(f"broader overlay range exceeds source: {entry['occurrence']}")
        try:
            actual = source[start:end].decode("utf-8")
        except UnicodeDecodeError as error:
            raise RuntimeError(f"broader overlay range splits UTF-8: {entry['occurrence']}") from error
        if actual != entry["source"]:
            raise RuntimeError(f"broader overlay source bytes changed: {entry['occurrence']}")
        if start < previous_end:
            raise RuntimeError(f"duplicate or overlapping broader overlay: {entry['occurrence']}")
        previous_end = end
        if any(start < protected_end and protected_start < end
               for protected_start, protected_end in occupied):
            raise RuntimeError(f"broader overlay overlaps a simp site: {entry['occurrence']}")
    return selected


def _comment_original(original: str) -> str:
    return "-- Original broader simp-family call/declaration:\n" + "\n".join(
        "-- " + line for line in original.split("\n")
    )


def apply_to_rendered(
    module: str,
    original: bytes,
    rendered: str,
    protected_ranges: Iterable[tuple[int, int]] = (),
    path: Path = DEFAULT_PATH,
) -> tuple[str, list[str]]:
    """Apply every module entry to already-rendered source exactly once.

    Exact source text is searched in the rendered output only after source
    authentication and protected simp-site overlap checks.  A zero or multiple
    match is rejected, so shifted, missing, duplicate, and unused entries never
    silently disappear.
    """
    metadata, entries = load_database(path)
    selected = _validate_source(module, original, entries, metadata["moduleSourceSha256"], protected_ranges)
    if not selected:
        return rendered, []
    edits: list[tuple[int, int, dict[str, Any]]] = []
    for entry in selected:
        needle = str(entry["source"])
        matches: list[int] = []
        cursor = 0
        while True:
            found = rendered.find(needle, cursor)
            if found < 0:
                break
            matches.append(found)
            cursor = found + 1
        if len(matches) != 1:
            reason = "missing" if not matches else "duplicate"
            raise RuntimeError(f"broader overlay {reason} in rendered source: {entry['occurrence']}")
        start = matches[0]
        edits.append((start, start + len(needle), entry))
    edits.sort(key=lambda item: item[0])
    for (_, end, _), (next_start, _, next_entry) in zip(edits, edits[1:]):
        if end > next_start:
            raise RuntimeError(f"overlapping rendered broader overlays: {next_entry['occurrence']}")
    result = rendered
    for start, end, entry in reversed(edits):
        original_text = str(entry["source"])
        replacement = str(entry["replacement"])
        result = result[:start] + _comment_original(original_text) + "\n" + replacement + result[end:]
    return result, [str(entry["occurrence"]) for entry in selected]
