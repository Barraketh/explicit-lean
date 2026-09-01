#!/usr/bin/env python3
"""Authenticated composition of the small manual simp override table.

The manual table is intentionally a source-level overlay.  This module joins it
to a schema-2 canonical inventory before it can be used, so callers cannot
silently apply a range from a different Mathlib checkout or hide another
supported occurrence inside an override.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path, PurePosixPath
from typing import Any, Mapping

import simp_engine_inventory as inventory
import simp_manual_overrides as manual


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / ".lake" / "boundary-corpus-manifest" / "manifest.json"
DEFAULT_DATABASE = manual.DEFAULT_PATH
MANIFEST_KIND = "simp_engine_boundary_manifest"
SCHEMA = 2
SUPPORTED_KINDS = frozenset(inventory.SUPPORTED_KINDS)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json(value: object) -> str:
    """Return the stable JSON representation used for overlay identities."""
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _error(message: str) -> RuntimeError:
    return RuntimeError(f"manual overlay: {message}")


def _string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise _error(f"{label} must be a nonempty string")
    return value


def _integer(value: object, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise _error(f"{label} must be a nonnegative integer")
    return value


def _module_path(module: str) -> PurePosixPath:
    path = PurePosixPath(module)
    if (
        path.is_absolute()
        or path.as_posix() != module
        or not path.parts
        or path.parts[0] != "Mathlib"
        or any(part in {"", ".", ".."} for part in path.parts)
        or not module.endswith(".lean")
    ):
        raise _error(f"invalid Mathlib module path: {module!r}")
    return path


def _environment(value: Mapping[str, object], label: str) -> dict[str, object]:
    mathlib = _string(value.get("mathlibCommit"), f"{label}.mathlibCommit")
    if len(mathlib) != 40 or any(c not in "0123456789abcdef" for c in mathlib):
        raise _error(f"{label}.mathlibCommit is not a commit hash")
    lean = value.get("lean")
    if not isinstance(lean, Mapping):
        raise _error(f"{label}.lean must be an object")
    version = _string(lean.get("version"), f"{label}.lean.version")
    commit = _string(lean.get("commit"), f"{label}.lean.commit")
    if len(commit) != 40 or any(c not in "0123456789abcdef" for c in commit):
        raise _error(f"{label}.lean.commit is not a commit hash")
    return {"mathlibCommit": mathlib, "lean": {"version": version, "commit": commit}}


def _read_manifest(path: Path) -> tuple[bytes, dict[str, Any]]:
    try:
        payload = path.read_bytes()
        value = json.loads(payload)
    except (OSError, json.JSONDecodeError) as error:
        raise _error(f"cannot read manifest {path}: {error}") from error
    if not isinstance(value, dict):
        raise _error("schema-2 manifest root must be an object")
    if value.get("kind") != MANIFEST_KIND or value.get("reportSchema") != SCHEMA:
        raise _error("only schema-2 simp_engine_boundary_manifest files are accepted")
    if value.get("allowUnresolved") is not False:
        raise _error("schema-2 manifest must set allowUnresolved=false")
    if not isinstance(value.get("modules"), list):
        raise _error("manifest modules must be an array")
    if not isinstance(value.get("occurrenceCount"), int) or value["occurrenceCount"] < 0:
        raise _error("manifest occurrenceCount must be a nonnegative integer")
    return payload, value


def _manifest_db_identity(manifest: Mapping[str, object]) -> Mapping[str, object] | None:
    """Accept the two spellings emitted by old schema-2 producers."""
    for key in ("manualOverrides", "manualOverrideDatabase", "manualDatabase"):
        value = manifest.get(key)
        if isinstance(value, Mapping):
            return value
    return None


def _check_db_binding(raw: bytes, environment: Mapping[str, object], manifest: Mapping[str, object]) -> None:
    expected = _manifest_db_identity(manifest)
    if expected is None:
        # Some producers put the compact binding at the manifest root.
        root_hash = manifest.get("manualOverrideDatabaseSha256", manifest.get("manualOverrideSha256"))
        root_schema = manifest.get("manualOverrideDatabaseSchema", manifest.get("manualOverrideSchema"))
        if root_hash is None or root_schema is None:
            raise _error("schema-2 manifest has no manual override database binding")
        expected = {"sha256": root_hash, "schema": root_schema}
    digest = expected.get("sha256", expected.get("databaseSha256", expected.get("hash")))
    if digest != sha256(raw):
        raise _error("manual override database hash does not match manifest")
    schema = expected.get("schema", expected.get("databaseSchema", expected.get("dbSchema")))
    if schema != manual.SCHEMA:
        raise _error("manual override database schema does not match manifest")
    manifest_environment = expected.get("environment")
    if manifest_environment is not None and manifest_environment != environment:
        raise _error("manual override database environment does not match manifest")


@dataclass(frozen=True)
class Overlay:
    """A validated manual overlay and its canonical schema-2 inventory."""

    database_path: Path
    manifest_path: Path
    database_sha256: str
    database_schema: int
    environment: dict[str, object]
    entries: tuple[dict[str, Any], ...]
    modules: dict[str, tuple[dict[str, Any], ...]]
    sources: dict[str, bytes]
    source_hashes: dict[str, str]
    manifest_hash: str
    global_counts: dict[str, int] | None = None

    @property
    def counts(self) -> dict[str, int]:
        canonical = sum(len(records) for records in self.modules.values())
        if self.global_counts is not None:
            return dict(self.global_counts)
        return {
            "modules": len(self.modules),
            "canonicalOccurrences": canonical,
            "manualOverrides": len(self.entries),
            "untouchedOccurrences": canonical - len(self.entries),
        }

    def identity(self) -> dict[str, object]:
        return {
            "kind": "simp_manual_overlay",
            "schema": SCHEMA,
            "database": {
                "sha256": self.database_sha256,
                "schema": self.database_schema,
                "environment": self.environment,
            },
            "environment": self.environment,
            "counts": self.counts,
        }

    def canonical_identity(self) -> str:
        return canonical_json(self.identity())

    def entries_by_module(self) -> dict[str, tuple[dict[str, Any], ...]]:
        result: dict[str, list[dict[str, Any]]] = {}
        for entry in self.entries:
            result.setdefault(str(entry["module"]), []).append(entry)
        return {module: tuple(values) for module, values in result.items()}

    def source_path(self, module: str, source_root: Path | None = None) -> Path:
        _module_path(module)
        root = (source_root or ROOT / ".lake" / "packages" / "mathlib").resolve()
        path = (root / Path(*module.split("/"))).resolve()
        try:
            path.relative_to(root)
        except ValueError as error:
            raise _error(f"source path escapes source root: {module}") from error
        return path

    def _source(self, module: str, source: bytes | None, source_root: Path | None) -> bytes:
        records = self.modules.get(module)
        if records is None:
            raise _error(f"module is absent from manifest: {module}")
        if source is None:
            source = self.sources[module]
            if source_root is not None:
                try:
                    source = self.source_path(module, source_root).read_bytes()
                except OSError as error:
                    raise _error(f"cannot read canonical source for {module}: {error}") from error
        if sha256(source) != self.source_hashes[module]:
            raise _error(f"canonical source hash changed: {module}")
        return source

    def apply(
        self,
        module: str,
        source: bytes | None = None,
        *,
        source_root: Path | None = None,
    ) -> bytes:
        source_bytes = self._source(module, source, source_root)
        return manual.apply(
            module,
            source_bytes,
            [entry for entry in self.entries if entry["module"] == module],
        )

    def shifted_occurrences(self, module: str) -> tuple[dict[str, object], ...]:
        records = self.modules.get(module)
        if records is None:
            raise _error(f"module is absent from manifest: {module}")
        selected = {
            str(e["occurrence"]): e
            for e in self.entries
            if e["module"] == module
        }
        result: list[dict[str, object]] = []
        for record in records:
            canonical_id = str(record["id"])
            if canonical_id in selected:
                continue
            start, end = int(record["startByte"]), int(record["endByte"])
            delta = sum(
                len(manual.render(entry, self.sources[module]))
                - (int(entry["endByte"]) - int(entry["startByte"]))
                for entry in selected.values()
                if int(entry["endByte"]) <= start
            )
            shifted = dict(record.get("metadata", {}))
            shifted.update(
                {
                    "id": inventory.occurrence_id(module, start + delta, end + delta),
                    "canonicalId": canonical_id,
                    "startByte": start + delta,
                    "endByte": end + delta,
                    "canonicalStartByte": start,
                    "canonicalEndByte": end,
                    "source": record["source"],
                    "kind": record["kind"],
                }
            )
            result.append(shifted)
        return tuple(result)

    shifted_mapping = shifted_occurrences


def _load_overlay_projected(
    manifest_path: Path = DEFAULT_MANIFEST,
    database_path: Path = manual.DEFAULT_PATH,
    *,
    source_root: Path | None = None,
    manifest_value: Mapping[str, object] | None = None,
    manifest_bytes: bytes | None = None,
    module_records: Mapping[str, Mapping[str, object]] | None = None,
) -> Overlay:
    """Load, authenticate, and validate the manual DB against a schema-2 manifest."""
    manifest_path, database_path = (
        Path(manifest_path).resolve(),
        Path(database_path).resolve(),
    )
    try:
        database_bytes = database_path.read_bytes()
    except OSError as error:
        raise _error(f"cannot read manual override database {database_path}: {error}") from error
    environment, entries = manual.load_database(database_path)
    try:
        if database_path.read_bytes() != database_bytes:
            raise _error("manual override database changed while loading")
    except OSError as error:
        raise _error(f"cannot reread manual override database: {error}") from error
    if manifest_value is None:
        read_manifest_bytes, manifest = _read_manifest(manifest_path)
        if manifest_bytes is None:
            manifest_bytes = read_manifest_bytes
    else:
        manifest = dict(manifest_value)
        if manifest_bytes is None:
            # The caller must provide the authenticated bytes when it supplies
            # a projection.  Reading/parsing a large manifest here would defeat
            # the capsule's purpose.
            raise _error("manifest bytes are required with a projected manifest")
    manifest_environment = _environment(manifest, "manifest")
    if manifest_environment != environment:
        raise _error("manual override environment does not match manifest")
    _check_db_binding(database_bytes, environment, manifest)

    configured_root = source_root
    if configured_root is None and isinstance(manifest.get("sourceRoot"), str):
        configured_root = Path(str(manifest["sourceRoot"]))
    canonical_root = (configured_root or ROOT / ".lake" / "packages" / "mathlib").resolve()

    modules: dict[str, tuple[dict[str, Any], ...]] = {}
    sources: dict[str, bytes] = {}
    source_hashes: dict[str, str] = {}
    seen_ids: set[str] = set()
    total = 0
    raw_modules = manifest.get("modules")
    if module_records is not None:
        override_modules = {str(entry["module"]) for entry in entries}
        raw_modules = [module_records[module] for module in sorted(override_modules)
                       if module in module_records]
    if not isinstance(raw_modules, list):
        raise _error("manifest modules must be an array")
    for raw_module in raw_modules:
        if not isinstance(raw_module, Mapping):
            raise _error("manifest module record must be an object")
        module = _string(raw_module.get("module"), "manifest module")
        _module_path(module)
        if module in modules:
            raise _error(f"duplicate manifest module: {module}")
        source_hash = _string(raw_module.get("sourceHash"), f"{module}.sourceHash")
        if len(source_hash) != 64:
            raise _error(f"invalid source hash for {module}")
        records: list[dict[str, Any]] = []
        source_path = (canonical_root / Path(*module.split("/"))).resolve()
        try:
            source_path.relative_to(canonical_root)
            source_bytes = source_path.read_bytes()
        except (OSError, ValueError) as error:
            raise _error(f"cannot read canonical source for {module}: {error}") from error
        if sha256(source_bytes) != source_hash:
            raise _error(f"canonical source hash changed: {module}")
        raw_occurrences = raw_module.get("occurrences")
        if not isinstance(raw_occurrences, list):
            raise _error(f"{module}.occurrences must be an array")
        for raw in raw_occurrences:
            if not isinstance(raw, Mapping):
                raise _error(f"occurrence in {module} must be an object")
            kind = _string(raw.get("kind"), f"{module}.occurrence.kind")
            if kind not in SUPPORTED_KINDS:
                raise _error(f"unsupported occurrence kind in {module}: {kind}")
            start = _integer(raw.get("startByte"), f"{module}.occurrence.startByte")
            end = _integer(raw.get("endByte"), f"{module}.occurrence.endByte")
            source_text = _string(raw.get("source"), f"{module}.occurrence.source")
            occurrence_id = _string(raw.get("id"), f"{module}.occurrence.id")
            if not 0 <= start < end <= len(source_bytes):
                raise _error(f"invalid occurrence range in {module}: {start}:{end}")
            try:
                actual_source = source_bytes[start:end].decode("utf-8")
            except UnicodeDecodeError as error:
                raise _error(f"occurrence range splits UTF-8 in {module}:{start}") from error
            if actual_source != source_text:
                raise _error(f"canonical occurrence source changed in {module}:{start}")
            if occurrence_id != inventory.occurrence_id(module, start, end):
                raise _error(f"canonical occurrence ID mismatch in {module}:{start}")
            if occurrence_id in seen_ids:
                raise _error(f"duplicate canonical occurrence ID: {occurrence_id}")
            seen_ids.add(occurrence_id)
            records.append(
                {
                    "id": occurrence_id,
                    "startByte": start,
                    "endByte": end,
                    "source": source_text,
                    "kind": kind,
                    "metadata": dict(raw),
                    "_module": module,
                    "_sourceHash": source_hash,
                }
            )
        records.sort(key=lambda r: (int(r["startByte"]), int(r["endByte"])))
        modules[module] = tuple(records)
        sources[module] = source_bytes
        source_hashes[module] = source_hash
        total += len(records)
    expected_count = manifest.get("occurrenceCount")
    global_counts = None
    if module_records is not None:
        expected_count = total
        declared_modules = manifest.get("moduleFileCount")
        declared_occurrences = manifest.get("occurrenceCount")
        if not isinstance(declared_modules, int) or not isinstance(declared_occurrences, int):
            raise _error("projected manifest has invalid global counts")
        if declared_modules < 0 or declared_occurrences < len(entries):
            raise _error("projected manifest has inconsistent global counts")
        global_counts = {
            "modules": declared_modules,
            "canonicalOccurrences": declared_occurrences,
            "manualOverrides": len(entries),
            "untouchedOccurrences": declared_occurrences - len(entries),
        }
    if total != expected_count:
        raise _error("manifest occurrenceCount disagrees with records")

    by_id = {str(r["id"]): r for rs in modules.values() for r in rs}
    by_module = {module: list(rs) for module, rs in modules.items()}
    override_modules = {str(entry["module"]) for entry in entries}
    for module in sorted(override_modules):
        if module not in sources:
            raise _error(f"manual override module is absent from manifest: {module}")
        manual.validate_against_source(module, sources[module], list(entries))
    for entry in entries:
        module = str(entry["module"])
        record = by_id.get(str(entry["occurrence"]))
        if record is None or record["_module"] != module:
            raise _error(
                f"manual range is not exactly one manifest occurrence: {entry['occurrence']}"
            )
        if (int(entry["startByte"]), int(entry["endByte"]), str(entry["source"])) != (
            int(record["startByte"]),
            int(record["endByte"]),
            str(record["source"]),
        ):
            raise _error(
                f"manual range/source is not exactly one manifest occurrence: {entry['occurrence']}"
            )
        if str(entry["moduleSourceSha256"]) != source_hashes[module]:
            raise _error(f"manual override source hash does not match manifest: {entry['occurrence']}")
        for other in by_module[module]:
            if other is record:
                continue
            a, b = int(entry["startByte"]), int(entry["endByte"])
            c, d = int(other["startByte"]), int(other["endByte"])
            if a < d and c < b:
                raise _error(
                    "manual range overlaps or contains supported occurrence: "
                    f"{entry['occurrence']}"
                )
    return Overlay(
        database_path=database_path,
        manifest_path=manifest_path,
        database_sha256=sha256(database_bytes),
        database_schema=manual.SCHEMA,
        environment=environment,
        entries=tuple(entries),
        modules={k: tuple(v) for k, v in by_module.items()},
        sources=sources,
        source_hashes=source_hashes,
        manifest_hash=sha256(manifest_bytes),
        global_counts=global_counts,
    )


def load_overlay(
    manifest_path: Path = DEFAULT_MANIFEST,
    database_path: Path = manual.DEFAULT_PATH,
    *,
    source_root: Path | None = None,
) -> Overlay:
    """Load a complete authenticated overlay from a full manifest.

    Projected module records are intentionally private: callers must first
    authenticate the capsule and then use ``_load_overlay_projected``.
    """
    return _load_overlay_projected(
        manifest_path, database_path, source_root=source_root,
    )


load = load_overlay


def entries_by_module(value: Overlay) -> dict[str, tuple[dict[str, Any], ...]]:
    """Functional convenience form of :meth:`Overlay.entries_by_module`."""
    return value.entries_by_module()


def apply(
    value: Overlay,
    module: str,
    source: bytes | None = None,
    *,
    source_root: Path | None = None,
) -> bytes:
    """Apply a previously authenticated overlay to one canonical module."""
    return value.apply(module, source, source_root=source_root)


def shifted_mapping(value: Overlay, module: str) -> tuple[dict[str, object], ...]:
    """Return untouched canonical occurrences at their effective byte ranges."""
    return value.shifted_occurrences(module)
