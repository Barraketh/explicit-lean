#!/usr/bin/env python3
"""Durable, incremental SQLite state for the search-free translation campaign.

This module intentionally uses only the Python standard library.  The database
keeps source versions and attempts forever, while ``modules`` and ``work_queue``
describe the current source version.  A result is reusable only when its
source, implementation, toolchain, and transitive dependency identities all
match the current checkout. A source edit after import therefore fails closed
until a refreshed manifest is imported. Unknown Mathlib dependencies likewise
require an explicit ``dependency_digests`` mapping when planning work.

For projects with a trusted header parser, ``import_manifest`` also accepts a
dependency map keyed by ``<module>@<sourceHash>``. Each value is either a list
of import names or an object containing ``dependencies`` (or ``imports``).
Supplying this map is an exact replacement for the fallback lexer: every
module in the manifest must have an entry, and a missing entry is rejected.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import sys
import time
from typing import Any, Iterator, Mapping, Sequence


SCHEMA_VERSION = 1
MANIFEST_SCHEMA = 2
MANIFEST_KIND = "simp_engine_boundary_manifest"
SUPPORTED_KINDS = {"simp", "simp_only"}
OCCURRENCE_ID_RE = re.compile(r"^[0-9a-f]{16}$")
EXECUTION_ROLES = {"direct_executable", "reusable_executable", "retained_syntax_data", "unresolved"}
DECLARATION_KINDS_BY_ROLE = {
    "direct_executable": {"proof", "computational", "generated_proof", "generated_computational", "signature_or_default", "mixed", "unknown"},
    "reusable_executable": {"caller_dependent"},
    "retained_syntax_data": {"not_applicable"},
    "unresolved": {"mixed", "unknown"},
}
ACTION_BY_DIMENSIONS = {
    ("retained_syntax_data", "not_applicable"): "retain",
    ("reusable_executable", "caller_dependent"): "materialize",
}
MODULE_NAME_RE = re.compile(r"^[A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*$")


class IndexError(RuntimeError):
    """An invalid manifest, join, identity, or queue operation."""


def canonical(value: object) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_text(value: str) -> str:
    return sha256_bytes(value.encode("utf-8"))


def occurrence_id(module: str, start: int, end: int) -> str:
    """The stable ID used by the boundary inventory protocol."""
    return sha256_text(f"{module}:{start}:{end}")[:16]


SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS meta (
  key TEXT PRIMARY KEY,
  value TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS manifests (
  manifest_hash TEXT PRIMARY KEY,
  path TEXT NOT NULL,
  schema_version INTEGER NOT NULL,
  payload_json TEXT NOT NULL,
  diagnostic INTEGER NOT NULL DEFAULT 0,
  imported_at REAL NOT NULL
);
CREATE TABLE IF NOT EXISTS modules (
  module TEXT PRIMARY KEY,
  compiled_module TEXT NOT NULL,
  source_path TEXT NOT NULL,
  source_hash TEXT NOT NULL,
  module_hash TEXT NOT NULL,
  manifest_hash TEXT NOT NULL,
  analysis_identity TEXT NOT NULL,
  diagnostic INTEGER NOT NULL DEFAULT 0,
  unresolved_count INTEGER NOT NULL DEFAULT 0,
  updated_at REAL NOT NULL
);
CREATE TABLE IF NOT EXISTS module_versions (
  module TEXT NOT NULL,
  source_hash TEXT NOT NULL,
  compiled_module TEXT NOT NULL,
  source_path TEXT NOT NULL,
  module_hash TEXT NOT NULL,
  manifest_hash TEXT NOT NULL,
  analysis_identity TEXT NOT NULL,
  imported_at REAL NOT NULL,
  PRIMARY KEY (module, source_hash)
);
CREATE TABLE IF NOT EXISTS imports (
  module TEXT NOT NULL,
  source_hash TEXT NOT NULL,
  dependency TEXT NOT NULL,
  PRIMARY KEY (module, source_hash, dependency)
);
CREATE TABLE IF NOT EXISTS occurrence_facts (
  module TEXT NOT NULL,
  source_hash TEXT NOT NULL,
  occurrence_id TEXT NOT NULL,
  start_byte INTEGER NOT NULL,
  end_byte INTEGER NOT NULL,
  source_text TEXT NOT NULL,
  kind TEXT NOT NULL,
  metadata_json TEXT NOT NULL,
  PRIMARY KEY (module, source_hash, occurrence_id)
);
CREATE TABLE IF NOT EXISTS occurrence_analyses (
  module TEXT NOT NULL,
  source_hash TEXT NOT NULL,
  occurrence_id TEXT NOT NULL,
  analysis_identity TEXT NOT NULL,
  classification TEXT,
  disposition TEXT,
  execution_role TEXT NOT NULL,
  action TEXT NOT NULL,
  declaration_kind TEXT NOT NULL,
  metadata_json TEXT NOT NULL,
  PRIMARY KEY (module, source_hash, occurrence_id, analysis_identity)
);
CREATE TABLE IF NOT EXISTS unresolved_backlog (
  module TEXT NOT NULL,
  source_hash TEXT NOT NULL,
  occurrence_id TEXT NOT NULL,
  analysis_identity TEXT NOT NULL,
  metadata_json TEXT NOT NULL,
  status TEXT NOT NULL DEFAULT 'open',
  recorded_at REAL NOT NULL,
  PRIMARY KEY (module, source_hash, occurrence_id, analysis_identity)
);
CREATE VIEW IF NOT EXISTS occurrences AS
SELECT f.module, f.source_hash, f.occurrence_id, f.start_byte, f.end_byte,
  f.source_text, f.kind, a.classification, a.disposition,
  a.execution_role, a.action, a.declaration_kind, a.metadata_json,
  a.analysis_identity
FROM occurrence_facts f
JOIN modules m ON m.module=f.module AND m.source_hash=f.source_hash
JOIN occurrence_analyses a ON a.module=f.module AND a.source_hash=f.source_hash
  AND a.occurrence_id=f.occurrence_id AND a.analysis_identity=m.analysis_identity;
CREATE TABLE IF NOT EXISTS result_cache (
  cache_key TEXT PRIMARY KEY,
  module TEXT NOT NULL,
  source_hash TEXT NOT NULL,
  analysis_identity TEXT NOT NULL,
  implementation_identity TEXT NOT NULL,
  toolchain_identity TEXT NOT NULL,
  dependency_identity TEXT NOT NULL,
  status TEXT NOT NULL,
  translation_status TEXT NOT NULL,
  result_json TEXT NOT NULL,
  failure TEXT,
  log_ref TEXT,
  artifact_ref TEXT,
  recorded_at REAL NOT NULL
);
CREATE TABLE IF NOT EXISTS attempts (
  attempt_id INTEGER PRIMARY KEY AUTOINCREMENT,
  module TEXT NOT NULL,
  cache_key TEXT NOT NULL,
  worker TEXT NOT NULL,
  status TEXT NOT NULL,
  failure TEXT,
  log_ref TEXT,
  artifact_ref TEXT,
  started_at REAL NOT NULL,
  finished_at REAL
);
CREATE TABLE IF NOT EXISTS work_queue (
  module TEXT PRIMARY KEY,
  cache_key TEXT NOT NULL,
  state TEXT NOT NULL,
  priority INTEGER NOT NULL DEFAULT 0,
  worker TEXT,
  lease_expires_at REAL,
  attempt_count INTEGER NOT NULL DEFAULT 0,
  last_attempt_id INTEGER,
  updated_at REAL NOT NULL
);
CREATE INDEX IF NOT EXISTS imports_dependency_idx ON imports(dependency);
CREATE INDEX IF NOT EXISTS occurrences_module_idx ON occurrence_facts(module, source_hash);
CREATE INDEX IF NOT EXISTS results_module_idx ON result_cache(module, source_hash);
CREATE INDEX IF NOT EXISTS attempts_module_idx ON attempts(module, started_at);
"""


def connect(path: str | Path) -> sqlite3.Connection:
    """Open an index and install conservative settings suitable for workers."""
    connection = sqlite3.connect(str(path), timeout=30.0, isolation_level=None)
    connection.row_factory = sqlite3.Row
    connection.execute("PRAGMA foreign_keys = ON")
    connection.execute("PRAGMA busy_timeout = 30000")
    connection.execute("PRAGMA journal_mode = WAL")
    connection.executescript(SCHEMA_SQL)
    connection.execute(
        "INSERT OR IGNORE INTO meta(key, value) VALUES ('schema_version', ?)",
        (str(SCHEMA_VERSION),),
    )
    return connection


@contextmanager
def transaction(connection: sqlite3.Connection, *, immediate: bool = False) -> Iterator[None]:
    connection.execute("BEGIN IMMEDIATE" if immediate else "BEGIN")
    try:
        yield
    except BaseException:
        connection.rollback()
        raise
    else:
        connection.commit()


def initialize(path: str | Path) -> None:
    database = Path(path)
    if str(database) != ":memory:":
        database.parent.mkdir(parents=True, exist_ok=True)
    connection = connect(database)
    connection.close()


def _require_string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise IndexError(f"{label} must be a nonempty string")
    return value


def _require_int(value: object, label: str, *, nonnegative: bool = False) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise IndexError(f"{label} must be an integer")
    if nonnegative and value < 0:
        raise IndexError(f"{label} must be nonnegative")
    return value


def _source_root(manifest_path: Path, source_root: str | Path | None) -> Path:
    if source_root is not None:
        root = Path(source_root).resolve()
        if not root.is_dir():
            raise IndexError(f"source root does not exist: {root}")
        return root
    candidates = [
        manifest_path.parent,
        manifest_path.parent.parent / "packages" / "mathlib",
        manifest_path.parent.parent.parent / "packages" / "mathlib",
        Path.cwd(),
    ]
    for candidate in candidates:
        if candidate.is_dir() and (candidate / "Mathlib").is_dir():
            return candidate.resolve()
    raise IndexError("cannot locate Mathlib source root; pass --source-root")


def _module_source(root: Path, module: str) -> Path:
    if not module.startswith("Mathlib/") or not module.endswith(".lean"):
        raise IndexError(f"invalid Mathlib module path: {module!r}")
    relative = Path(module)
    path = (root / relative).resolve()
    try:
        path.relative_to(root.resolve())
    except ValueError as error:
        raise IndexError(f"module escapes source root: {module!r}") from error
    if not path.is_file():
        raise IndexError(f"module source is missing: {path}")
    return path


def _clean_lean_lines(source: str) -> Iterator[str]:
    """Yield comment-erased lines lazily, preserving token boundaries.

    Keeping this iterator lazy matters for a source file whose body is large:
    ``_imports`` stops as soon as the first non-header command is seen and does
    not scan strings or comments in the rest of that body.
    """
    line: list[str] = []
    depth = 0
    index = 0
    in_string = False
    while index < len(source):
        pair = source[index : index + 2]
        if depth:
            if pair == "/-":
                line.append(" ")
                depth += 1; index += 2
            elif pair == "-/":
                depth -= 1
                line.append(" ")
                index += 2
            else:
                if source[index] in "\r\n":
                    line.append(source[index])
                    yield "".join(line)
                    line = []
                index += 1
            continue
        if in_string:
            character = source[index]
            line.append(character)
            if character == "\\":
                if index + 1 < len(source):
                    line.append(source[index + 1]); index += 2; continue
            elif character == '"':
                in_string = False
            if character in "\r\n":
                yield "".join(line)
                line = []
            index += 1; continue
        if pair == "/-":
            depth = 1
            line.append(" ")
            index += 2
        elif pair == "--":
            newline = source.find("\n", index)
            if newline < 0:
                index = len(source)
            else:
                line.append("\n")
                yield "".join(line)
                line = []
                index = newline + 1
        elif source[index] == '"':
            in_string = True; line.append(source[index]); index += 1
        else:
            character = source[index]
            line.append(character)
            if character in "\r\n":
                yield "".join(line)
                line = []
            index += 1
    if depth:
        raise IndexError("unterminated block comment in import header")
    if line:
        yield "".join(line)


def _strip_lean_comments(source: str) -> str:
    """Erase nested block/line comments without touching string contents."""
    return "".join(_clean_lean_lines(source))


def _imports(source: str) -> list[str]:
    """Parse only the contiguous Lean import header, failing closed on gaps."""
    names: list[str] = []
    pending = False
    continuation_allowed = False
    for raw_line in _clean_lean_lines(source):
        stripped = raw_line.strip()
        if not stripped:
            if pending:
                raise IndexError("unsupported multiline import header")
            continuation_allowed = False
            continue
        indent = len(raw_line) - len(raw_line.lstrip())
        if pending:
            tokens = stripped.split()
            if indent == 0 or not tokens or not all(MODULE_NAME_RE.fullmatch(token) for token in tokens):
                raise IndexError("unsupported multiline import header")
            names.extend(tokens); pending = False; continuation_allowed = True; continue
        if continuation_allowed and indent > 0:
            tokens = stripped.split()
            if all(MODULE_NAME_RE.fullmatch(token) for token in tokens):
                raise IndexError("unsupported multiline import header")
        continuation_allowed = False
        if stripped == "module" or stripped.startswith("module ") or stripped == "prelude":
            continue
        tokens = stripped.split()
        if "import" in tokens[:4]:
            import_index = tokens.index("import")
            prefixes = set(tokens[:import_index])
            if not prefixes <= {"public", "private", "meta", "all"}:
                raise IndexError(f"unsupported import header prefix: {stripped}")
            imported = tokens[import_index + 1 :]
            # ``all`` is an import modifier, not a module name. Lean emits
            # this form in a small number of Mathlib headers.
            if imported and imported[0] == "all":
                imported = imported[1:]
            if not imported:
                pending = True; continue
            if not all(MODULE_NAME_RE.fullmatch(token) for token in imported):
                raise IndexError(f"unsupported import header form: {stripped}")
            names.extend(imported); continuation_allowed = True; continue
        # The first real command ends the header. A later commented import was
        # removed above and therefore cannot invent a dependency edge.
        break
    if pending:
        raise IndexError("unterminated multiline import header")
    return sorted(set(names))


def _dependency_map_entries(
    dependency_map: Mapping[str, object], module: str, source_hash: str,
) -> list[str]:
    """Return one exact source-bound dependency-map entry.

    The source hash is part of the key even when the value is a plain list, so
    a parser result cannot accidentally be reused after a source edit. An
    optional duplicate ``module``/``sourceHash`` in object values is checked
    too, making hand-authored maps fail closed on bad joins.
    """
    key = f"{module}@{source_hash}"
    if key not in dependency_map:
        raise IndexError(f"dependency map is missing {key}")
    value = dependency_map[key]
    if isinstance(value, list):
        dependencies = value
    elif isinstance(value, dict):
        if value.get("module", module) != module:
            raise IndexError(f"dependency map module disagrees for {key}")
        if "sourceHash" in value and value["sourceHash"] != source_hash:
            raise IndexError(f"dependency map source hash disagrees for {key}")
        dependencies = value.get("dependencies", value.get("imports"))
    else:
        raise IndexError(f"dependency map entry must be an array or object: {key}")
    if not isinstance(dependencies, list) or not all(isinstance(item, str) and item for item in dependencies):
        raise IndexError(f"dependency map dependencies must be nonempty strings: {key}")
    return sorted(set(_normalize_dependency(item) for item in dependencies))


def _normalize_dependency(name: str) -> str:
    """Use the manifest's source-path identity for Mathlib imports.

    Lean writes imports as ``Mathlib.Foo.Bar`` while manifest module keys are
    ``Mathlib/Foo/Bar.lean``.  Keeping one spelling is necessary for joins and
    dependency-closure invalidation; imports outside Mathlib remain compiled
    module names and are stable external identities.
    """
    if name.startswith("Mathlib."):
        return "Mathlib/" + name[len("Mathlib.") :].replace(".", "/") + ".lean"
    return name


def _resolve_manifest(path: str | Path, *, diagnostic: bool = False) -> tuple[Path, bytes, dict[str, Any], str]:
    manifest_path = Path(path).resolve()
    try:
        payload = manifest_path.read_bytes()
        value = json.loads(payload)
    except (OSError, json.JSONDecodeError) as error:
        raise IndexError(f"cannot read manifest {manifest_path}: {error}") from error
    if not isinstance(value, dict):
        raise IndexError("manifest root must be an object")
    if value.get("kind") != MANIFEST_KIND or value.get("reportSchema") != MANIFEST_SCHEMA:
        raise IndexError(
            "only schema-2 simp_engine_boundary_manifest files are accepted "
            f"(kind={value.get('kind')!r}, schema={value.get('reportSchema')!r})"
        )
    if value.get("allowUnresolved") is not False and not diagnostic:
        raise IndexError("schema-2 manifest must set allowUnresolved=false")
    if diagnostic and value.get("allowUnresolved") is not True:
        raise IndexError("diagnostic intake requires allowUnresolved=true")
    prefix = value.get("modulePrefix")
    if prefix is not None and (not isinstance(prefix, str) or not prefix.startswith("Mathlib/")):
        raise IndexError("schema-2 manifest modulePrefix must be a Mathlib/ path")
    modules = value.get("modules")
    if not isinstance(modules, list):
        raise IndexError("manifest modules must be an array")
    declared_count = value.get("occurrenceCount")
    if not isinstance(declared_count, int) or declared_count < 0:
        raise IndexError("manifest occurrenceCount must be a nonnegative integer")
    return manifest_path, payload, value, sha256_bytes(payload)


def _validated_modules(
    manifest_path: Path,
    manifest: Mapping[str, Any],
    source_root: str | Path | None,
    dependency_map: Mapping[str, object] | None = None,
) -> list[dict[str, Any]]:
    root = _source_root(manifest_path, source_root)
    seen_modules: set[str] = set()
    seen_ids: set[str] = set()
    total_occurrences = 0
    records: list[dict[str, Any]] = []
    for raw_module in manifest["modules"]:
        if not isinstance(raw_module, dict):
            raise IndexError("manifest module record must be an object")
        module = _require_string(raw_module.get("module"), "module")
        if module in seen_modules:
            raise IndexError(f"duplicate module record: {module}")
        seen_modules.add(module)
        compiled = _require_string(raw_module.get("compiledModule"), f"{module}.compiledModule")
        expected_compiled = module[:-5].replace("/", ".")
        if compiled != expected_compiled:
            raise IndexError(
                f"compiledModule disagrees with source path for {module}: "
                f"{compiled!r} != {expected_compiled!r}"
            )
        source_path = _module_source(root, module)
        source_bytes = source_path.read_bytes()
        try:
            source_text = source_bytes.decode("utf-8")
        except UnicodeDecodeError as error:
            raise IndexError(f"module source is not UTF-8: {module}") from error
        source_hash = _require_string(raw_module.get("sourceHash"), f"{module}.sourceHash")
        if sha256_bytes(source_bytes) != source_hash:
            raise IndexError(f"source hash mismatch for {module}")
        module_hash = _require_string(raw_module.get("moduleHash"), f"{module}.moduleHash")
        raw_occurrences = raw_module.get("occurrences")
        if not isinstance(raw_occurrences, list):
            raise IndexError(f"{module}.occurrences must be an array")
        occurrences: list[dict[str, Any]] = []
        for raw in raw_occurrences:
            if not isinstance(raw, dict):
                raise IndexError(f"occurrence in {module} must be an object")
            kind = _require_string(raw.get("kind"), f"{module} occurrence kind")
            if kind not in SUPPORTED_KINDS:
                raise IndexError(f"unsupported occurrence kind in {module}: {kind!r}")
            text = _require_string(raw.get("source"), f"{module} occurrence source")
            start = _require_int(raw.get("startByte"), f"{module} occurrence startByte", nonnegative=True)
            end = _require_int(raw.get("endByte"), f"{module} occurrence endByte", nonnegative=True)
            if not 0 <= start < end <= len(source_bytes):
                raise IndexError(f"invalid occurrence range in {module}: {start}:{end}")
            try:
                actual = source_bytes[start:end].decode("utf-8")
            except UnicodeDecodeError as error:
                raise IndexError(f"occurrence range splits UTF-8 in {module}:{start}") from error
            if actual != text:
                raise IndexError(f"stale occurrence source in {module}:{start}")
            if raw.get("syntaxKind") != "Lean.Parser.Tactic.simp":
                raise IndexError(f"unexpected occurrence syntax kind in {module}:{start}")
            execution_role = _require_string(raw.get("executionRole"), f"{module} occurrence executionRole")
            declaration_kind = _require_string(raw.get("declarationKind"), f"{module} occurrence declarationKind")
            action = _require_string(raw.get("action"), f"{module} occurrence action")
            if execution_role not in EXECUTION_ROLES or declaration_kind not in DECLARATION_KINDS_BY_ROLE.get(execution_role, set()):
                raise IndexError(f"invalid scope dimensions in {module}:{start}")
            expected_action = ACTION_BY_DIMENSIONS.get((execution_role, declaration_kind), "materialize" if execution_role == "direct_executable" else "unresolved")
            if action != expected_action:
                raise IndexError(f"scope dimensions imply {expected_action!r}, found {action!r} in {module}:{start}")
            declarations = raw.get("declarations")
            if declarations is not None:
                if not isinstance(declarations, list):
                    raise IndexError(f"{module} occurrence declarations must be an array")
                for declaration in declarations:
                    if not isinstance(declaration, dict) or declaration.get("module") != compiled:
                        raise IndexError(f"occurrence declaration join disagrees with compiled module in {module}:{start}")
            expected_id = occurrence_id(module, start, end)
            actual_id = _require_string(raw.get("id"), f"{module} occurrence id")
            if actual_id != expected_id or not OCCURRENCE_ID_RE.fullmatch(actual_id):
                raise IndexError(
                    f"occurrence ID mismatch in {module}:{start}: {actual_id!r} != {expected_id!r}"
                )
            if actual_id in seen_ids:
                raise IndexError(f"duplicate occurrence ID: {actual_id}")
            seen_ids.add(actual_id)
            occurrences.append(
                {
                    "id": actual_id,
                    "start": start,
                    "end": end,
                    "source": text,
                    "kind": kind,
                    "classification": raw.get("classification"),
                    "disposition": raw.get("disposition"),
                    "execution_role": execution_role,
                    "action": action,
                    "declaration_kind": declaration_kind,
                    "metadata": raw,
                }
            )
        total_occurrences += len(occurrences)
        unresolved_count = sum(occurrence["action"] == "unresolved" for occurrence in occurrences)
        if dependency_map is not None:
            dependency_names = _dependency_map_entries(dependency_map, module, source_hash)
        else:
            dependencies = raw_module.get("imports", raw_module.get("dependencies"))
            if dependencies is None:
                dependency_names = [_normalize_dependency(name) for name in _imports(source_text)]
            elif isinstance(dependencies, list) and all(isinstance(item, str) and item for item in dependencies):
                dependency_names = sorted(set(_normalize_dependency(name) for name in dependencies))
            else:
                raise IndexError(f"{module}.imports must be an array of nonempty strings")
        records.append(
            {
                "module": module,
                "compiled": compiled,
                "source_path": str(source_path),
                "source_hash": source_hash,
                "module_hash": module_hash,
                "analysis_identity": sha256_text(canonical({
                    "module": module,
                    "occurrences": [occurrence["metadata"] for occurrence in occurrences],
                })),
                "unresolved_count": unresolved_count,
                "occurrences": occurrences,
                "dependencies": dependency_names,
            }
        )
    if total_occurrences != manifest["occurrenceCount"]:
        raise IndexError(
            f"manifest occurrenceCount disagrees with records: {manifest['occurrenceCount']} != {total_occurrences}"
        )
    return records


def import_manifest(
    connection: sqlite3.Connection,
    manifest_path: str | Path,
    *,
    source_root: str | Path | None = None,
    diagnostic: bool = False,
    dependency_map: Mapping[str, object] | None = None,
) -> dict[str, Any]:
    """Validate and import a schema-2 manifest atomically.

    Existing source versions are compared on their immutable identity fields.  Thus a malformed
    second manifest cannot silently overwrite a previously imported join.
    """
    path, payload, manifest, manifest_hash = _resolve_manifest(manifest_path, diagnostic=diagnostic)
    if dependency_map is not None and not isinstance(dependency_map, Mapping):
        raise IndexError("dependency map must be an object keyed by module@sourceHash")
    records = _validated_modules(path, manifest, source_root, dependency_map)
    now = time.time()
    changed_modules: set[str] = set()
    with transaction(connection, immediate=True):
        connection.execute(
            "INSERT OR IGNORE INTO manifests VALUES (?, ?, ?, ?, ?, ?)",
            (manifest_hash, str(path), MANIFEST_SCHEMA, payload.decode("utf-8"), int(diagnostic), now),
        )
        for record in records:
            module = record["module"]
            source_hash = record["source_hash"]
            current = connection.execute(
                "SELECT source_hash,analysis_identity FROM modules WHERE module=?", (module,)
            ).fetchone()
            if current is not None and (
                current["source_hash"] != source_hash or current["analysis_identity"] != record["analysis_identity"]
            ):
                changed_modules.add(module)
            version = connection.execute(
                "SELECT * FROM module_versions WHERE module=? AND source_hash=?",
                (module, source_hash),
            ).fetchone()
            version_values = (
                module,
                source_hash,
                record["compiled"],
                record["source_path"],
                record["module_hash"],
                manifest_hash,
                record["analysis_identity"],
                now,
            )
            # ``imported_at`` and the manifest carrying an unchanged source
            # are provenance, rather than part of the source-version join.
            # Keep the first provenance row while rejecting changed compiled
            # or source identities.
            if version is not None and tuple(version[:5]) != version_values[:5]:
                raise IndexError(f"conflicting historical module join for {module}@{source_hash}")
            connection.execute(
                "INSERT OR IGNORE INTO module_versions VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                version_values,
            )
            old_dependencies = {
                row[0]
                for row in connection.execute(
                    "SELECT dependency FROM imports WHERE module=? AND source_hash=?", (module, source_hash)
                )
            }
            if old_dependencies and old_dependencies != set(record["dependencies"]):
                raise IndexError(f"conflicting dependency join for {module}@{source_hash}")
            connection.executemany(
                "INSERT OR IGNORE INTO imports VALUES (?, ?, ?)",
                [(module, source_hash, dependency) for dependency in record["dependencies"]],
            )
            for occurrence in record["occurrences"]:
                fact_values = (
                    module,
                    source_hash,
                    occurrence["id"],
                    occurrence["start"],
                    occurrence["end"],
                    occurrence["source"],
                    occurrence["kind"],
                    canonical({"syntaxKind": occurrence["metadata"].get("syntaxKind")}),
                )
                previous = connection.execute(
                    "SELECT * FROM occurrence_facts WHERE module=? AND source_hash=? AND occurrence_id=?",
                    (module, source_hash, occurrence["id"]),
                ).fetchone()
                if previous is not None and tuple(previous) != fact_values:
                    raise IndexError(f"conflicting immutable occurrence fact: {occurrence['id']}")
                connection.execute(
                    "INSERT OR IGNORE INTO occurrence_facts VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                    fact_values,
                )
                connection.execute(
                    "INSERT INTO occurrence_analyses VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?) "
                    "ON CONFLICT(module,source_hash,occurrence_id,analysis_identity) DO UPDATE SET "
                    "classification=excluded.classification,disposition=excluded.disposition,"
                    "execution_role=excluded.execution_role,action=excluded.action,"
                    "declaration_kind=excluded.declaration_kind,metadata_json=excluded.metadata_json",
                    (
                        module, source_hash, occurrence["id"], record["analysis_identity"],
                        occurrence["classification"], occurrence["disposition"],
                        occurrence["execution_role"], occurrence["action"],
                        occurrence["declaration_kind"], canonical(occurrence["metadata"]),
                    ),
                )
                if occurrence["action"] == "unresolved":
                    connection.execute(
                        "INSERT OR REPLACE INTO unresolved_backlog "
                        "(module,source_hash,occurrence_id,analysis_identity,metadata_json,status,recorded_at) "
                        "VALUES (?, ?, ?, ?, ?, 'open', ?)",
                        (module, source_hash, occurrence["id"], record["analysis_identity"], canonical(occurrence["metadata"]), now),
                    )
            connection.execute(
                "INSERT INTO modules VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?) "
                "ON CONFLICT(module) DO UPDATE SET compiled_module=excluded.compiled_module, "
                "source_path=excluded.source_path, source_hash=excluded.source_hash, "
                "module_hash=excluded.module_hash, manifest_hash=excluded.manifest_hash, "
                "analysis_identity=excluded.analysis_identity, diagnostic=excluded.diagnostic, "
                "unresolved_count=excluded.unresolved_count, updated_at=excluded.updated_at",
                (module, record["compiled"], record["source_path"], source_hash, record["module_hash"], manifest_hash, record["analysis_identity"], int(diagnostic), record["unresolved_count"], now),
            )
        # A new analysis or source version invalidates the reverse dependency
        # closure. Independent modules retain their queue/cache state.
        affected = set(changed_modules)
        frontier = list(changed_modules)
        while frontier:
            dependency = frontier.pop()
            dependents = [row[0] for row in connection.execute(
                "SELECT DISTINCT module FROM imports WHERE dependency=?", (dependency,)
            )]
            for dependent in dependents:
                if dependent not in affected:
                    affected.add(dependent)
                    frontier.append(dependent)
        for affected_module in affected:
            connection.execute(
                "UPDATE attempts SET status='stale',failure='source or analysis changed',finished_at=? "
                "WHERE attempt_id=(SELECT last_attempt_id FROM work_queue WHERE module=?) AND status='running'",
                (now, affected_module),
            )
            connection.execute(
                "UPDATE work_queue SET state='stale',worker=NULL,lease_expires_at=NULL,updated_at=? WHERE module=?",
                (now, affected_module),
            )
    unresolved = sum(record["unresolved_count"] for record in records)
    return {
        "manifestHash": manifest_hash,
        "modules": len(records),
        "occurrences": manifest["occurrenceCount"],
        "diagnostic": diagnostic,
        "unresolved": unresolved,
    }


def _module_row(connection: sqlite3.Connection, module: str) -> sqlite3.Row:
    row = connection.execute("SELECT * FROM modules WHERE module=?", (module,)).fetchone()
    if row is None:
        raise IndexError(f"unknown module: {module}")
    source_path = Path(row["source_path"])
    if not source_path.is_file() or sha256_bytes(source_path.read_bytes()) != row["source_hash"]:
        raise IndexError(f"source changed after import for {module}; import a refreshed manifest")
    return row


def _effective_identity(
    connection: sqlite3.Connection,
    module: str,
    memo: dict[str, str],
    visiting: set[str],
    dependency_digests: Mapping[str, str] | None = None,
    source_memo: dict[str, str] | None = None,
) -> str:
    if module in memo:
        return memo[module]
    if module in visiting:
        # Lean imports should be acyclic; retaining the edge in the identity is
        # deterministic and avoids recursion failure on a malformed fixture.
        return sha256_text(f"cycle:{module}")
    row = connection.execute("SELECT source_hash,module_hash,analysis_identity,source_path FROM modules WHERE module=?", (module,)).fetchone()
    if row is None:
        if module.startswith("Mathlib/"):
            digest = (dependency_digests or {}).get(module)
            if digest is None:
                raise IndexError(
                    f"dependency is outside the imported manifest: {module}; "
                    "import its module or provide dependency_digests"
                )
            return sha256_text(canonical({"external": module, "digest": digest}))
        return sha256_text(f"external:{module}")
    if source_memo is None:
        source_memo = {}
    if module not in source_memo:
        source_path = Path(row["source_path"])
        source_memo[module] = sha256_bytes(source_path.read_bytes()) if source_path.is_file() else ""
    if source_memo[module] != row["source_hash"]:
        raise IndexError(f"source changed after import for {module}; import a refreshed manifest")
    visiting.add(module)
    deps = [r[0] for r in connection.execute(
        "SELECT dependency FROM imports WHERE module=? AND source_hash=? ORDER BY dependency",
        (module, row["source_hash"]),
    )]
    dependency_parts = [
        (dependency, _effective_identity(connection, dependency, memo, visiting, dependency_digests, source_memo))
        for dependency in deps
    ]
    visiting.remove(module)
    identity = sha256_text(canonical({"module": module, "source": row["source_hash"], "moduleHash": row["module_hash"], "analysis": row["analysis_identity"], "dependencies": dependency_parts}))
    memo[module] = identity
    return identity


def dependency_identity(
    connection: sqlite3.Connection,
    module: str,
    dependency_digests: Mapping[str, str] | None = None,
    *,
    memo: dict[str, str] | None = None,
    source_memo: dict[str, str] | None = None,
    module_row: sqlite3.Row | None = None,
) -> str:
    row = module_row if module_row is not None else _module_row(connection, module)
    if memo is None:
        memo = {}
    parts = []
    for dependency in [r[0] for r in connection.execute(
        "SELECT dependency FROM imports WHERE module=? AND source_hash=? ORDER BY dependency",
        (module, row["source_hash"]),
    )]:
        parts.append((dependency, _effective_identity(connection, dependency, memo, set(), dependency_digests, source_memo)))
    return sha256_text(canonical(parts))


def cache_key(
    connection: sqlite3.Connection,
    module: str,
    implementation_identity: object,
    toolchain_identity: object,
    dependency_digests: Mapping[str, str] | None = None,
    *,
    identity_memo: dict[str, str] | None = None,
    source_memo: dict[str, str] | None = None,
) -> tuple[str, str]:
    row = _module_row(connection, module)
    implementation = canonical(implementation_identity)
    toolchain = canonical(toolchain_identity)
    dependencies = dependency_identity(connection, module, dependency_digests, memo=identity_memo, source_memo=source_memo, module_row=row)
    key = sha256_text(canonical({
        "module": module,
        "source": row["source_hash"],
        "moduleHash": row["module_hash"],
        "analysis": row["analysis_identity"],
        "implementation": implementation,
        "toolchain": toolchain,
        "dependencies": dependencies,
    }))
    return key, dependencies


def plan_work(
    connection: sqlite3.Connection,
    implementation_identity: object,
    toolchain_identity: object,
    *,
    modules: Sequence[str] | None = None,
    dependency_digests: Mapping[str, str] | None = None,
) -> list[dict[str, Any]]:
    """Refresh the queue and return modules whose current result is absent."""
    selected = list(modules) if modules is not None else [
        row[0] for row in connection.execute("SELECT module FROM modules ORDER BY module")
    ]
    now = time.time()
    planned: list[dict[str, Any]] = []
    identity_memo: dict[str, str] = {}
    source_memo: dict[str, str] = {}
    with transaction(connection, immediate=True):
        for module in selected:
            key, dependencies = cache_key(connection, module, implementation_identity, toolchain_identity, dependency_digests, identity_memo=identity_memo, source_memo=source_memo)
            result = connection.execute("SELECT status,translation_status FROM result_cache WHERE cache_key=?", (key,)).fetchone()
            # A failure remains historical evidence, but planning makes it
            # claimable again so a bounded worker can retry it.
            desired = "succeeded" if result is not None and result["status"] == "success" and result["translation_status"] == "verified_translated" else "queued"
            queue = connection.execute("SELECT * FROM work_queue WHERE module=?", (module,)).fetchone()
            if queue is not None and queue["cache_key"] != key and queue["state"] == "running":
                connection.execute(
                    "UPDATE attempts SET status='stale',failure='source or identity changed',finished_at=? "
                    "WHERE attempt_id=? AND status='running'",
                    (now, queue["last_attempt_id"]),
                )
            if queue is None or queue["cache_key"] != key or queue["state"] not in {"running"}:
                connection.execute(
                    "INSERT INTO work_queue(module,cache_key,state,priority,updated_at) VALUES (?, ?, ?, 0, ?) "
                    "ON CONFLICT(module) DO UPDATE SET cache_key=excluded.cache_key,state=excluded.state,"
                    "worker=NULL,lease_expires_at=NULL,updated_at=excluded.updated_at",
                    (module, key, desired, now),
                )
            planned.append({"module": module, "cacheKey": key, "dependencyIdentity": dependencies, "state": desired})
    return planned


def order_retryable(
    connection: sqlite3.Connection, modules: Sequence[str],
    *, manifest_order: Mapping[str, int] | None = None,
    cache_keys: Mapping[str, str] | None = None,
) -> list[str]:
    """Order bounded retry work so repeated failures cannot starve fresh work.

    Modules with no recorded attempt for their current cache key are placed first.  Previously attempted
    modules are then ordered by their attempt count and oldest attempt, with
    manifest order (when supplied) as the final stable tie-breaker.  Keeping
    module names out of the tie-breaker makes ordering independent of naming.
    """
    indexed = {module: index for index, module in enumerate(modules)}
    if len(indexed) != len(modules):
        raise IndexError("retry ordering modules must be unique")
    if not indexed:
        return []
    if cache_keys is None or any(module not in cache_keys for module in modules):
        raise IndexError("retry ordering requires current cache keys for every module")
    # Keep each query comfortably below SQLite's parameter limit.  Attempts
    # are filtered in Python because each module has a different current key.
    details: dict[str, tuple[int, float | None]] = {}
    for offset in range(0, len(modules), 800):
        chunk = list(modules[offset:offset + 800])
        placeholders = ",".join("?" for _ in chunk)
        queue_rows = connection.execute(
            f"SELECT module FROM work_queue WHERE module IN ({placeholders})",
            tuple(chunk),
        ).fetchall()
        for row in queue_rows:
            details[row["module"]] = (0, None)
        attempt_rows = connection.execute(
            f"SELECT module,cache_key,started_at FROM attempts WHERE module IN ({placeholders})",
            tuple(chunk),
        ).fetchall()
        counts: dict[str, int] = {}
        oldest: dict[str, float] = {}
        for row in attempt_rows:
            module = row["module"]
            if row["cache_key"] != cache_keys[module]:
                continue
            counts[module] = counts.get(module, 0) + 1
            oldest[module] = min(oldest.get(module, row["started_at"]), row["started_at"])
        for module, count in counts.items():
            details[module] = (count, oldest[module])
    return sorted(
        modules,
        key=lambda module: (
            0 if details.get(module, (0, None))[0] == 0 else 1,
            details.get(module, (0, None))[0],
            details.get(module, (0, None))[1] is not None,
            details.get(module, (0, None))[1] if details.get(module, (0, None))[1] is not None else 0,
            (manifest_order or {}).get(module, indexed[module]),
        ),
    )


@dataclass(frozen=True)
class Lease:
    attempt_id: int
    module: str
    cache_key: str
    worker: str
    lease_expires_at: float


def claim_work(
    connection: sqlite3.Connection,
    worker: str,
    *,
    limit: int = 1,
    lease_seconds: float = 900,
    now: float | None = None,
    modules: Sequence[str] | None = None,
) -> list[Lease]:
    if not worker:
        raise IndexError("worker must be nonempty")
    if limit <= 0 or lease_seconds <= 0:
        raise IndexError("limit and lease_seconds must be positive")
    current = time.time() if now is None else now
    leases: list[Lease] = []
    with transaction(connection, immediate=True):
        expired = connection.execute(
            "SELECT module FROM work_queue WHERE state='running' AND lease_expires_at <= ?", (current,)
        ).fetchall()
        for row in expired:
            connection.execute(
                "UPDATE attempts SET status='abandoned', failure='lease expired', finished_at=? "
                "WHERE attempt_id=(SELECT last_attempt_id FROM work_queue WHERE module=?) AND status='running'",
                (current, row[0]),
            )
            connection.execute(
                "UPDATE work_queue SET state='queued',worker=NULL,lease_expires_at=NULL,updated_at=? WHERE module=?",
                (current, row[0]),
            )
        if modules is None:
            rows = connection.execute(
                "SELECT module,cache_key FROM work_queue WHERE state='queued' "
                "ORDER BY priority DESC,module LIMIT ?",
                (limit,),
            ).fetchall()
        else:
            requested = list(modules)
            if any(not isinstance(module, str) or not module for module in requested):
                raise IndexError("claim module filters must be nonempty strings")
            if len(set(requested)) != len(requested):
                raise IndexError("claim module filters must be unique")
            if not requested:
                rows = []
            else:
                placeholders = ",".join("?" for _ in requested)
                rows = connection.execute(
                    "SELECT module,cache_key FROM work_queue WHERE state='queued' "
                    f"AND module IN ({placeholders}) ORDER BY priority DESC,module LIMIT ?",
                    (*requested, limit),
                ).fetchall()
        for row in rows:
            expires = current + lease_seconds
            cursor = connection.execute(
                "INSERT INTO attempts(module,cache_key,worker,status,started_at) VALUES (?, ?, ?, 'running', ?)",
                (row["module"], row["cache_key"], worker, current),
            )
            attempt_id = int(cursor.lastrowid)
            connection.execute(
                "UPDATE work_queue SET state='running',worker=?,lease_expires_at=?,attempt_count=attempt_count+1,"
                "last_attempt_id=?,updated_at=? WHERE module=?",
                (worker, expires, attempt_id, current, row["module"]),
            )
            leases.append(Lease(attempt_id, row["module"], row["cache_key"], worker, expires))
    return leases


def abandon_lease(
    connection: sqlite3.Connection,
    attempt_id: int,
    worker: str,
    failure: str,
    *,
    now: float | None = None,
) -> None:
    """Abandon one active lease and requeue it without changing result cache."""
    if attempt_id <= 0 or not worker or not isinstance(failure, str) or not failure.strip():
        raise IndexError("attempt, worker, and failure are required")
    current = time.time() if now is None else now
    with transaction(connection, immediate=True):
        attempt = connection.execute(
            "SELECT module FROM attempts WHERE attempt_id=? AND worker=? AND status='running'",
            (attempt_id, worker),
        ).fetchone()
        if attempt is None:
            raise IndexError("attempt is missing, completed, or owned by another worker")
        queue = connection.execute(
            "SELECT state,worker,last_attempt_id FROM work_queue WHERE module=?",
            (attempt["module"],),
        ).fetchone()
        if (queue is None or queue["state"] != "running" or queue["worker"] != worker
                or queue["last_attempt_id"] != attempt_id):
            raise IndexError("lease queue identity is missing or no longer active")
        connection.execute(
            "UPDATE attempts SET status='abandoned',failure=?,finished_at=? "
            "WHERE attempt_id=? AND status='running'",
            (failure.strip(), current, attempt_id),
        )
        connection.execute(
            "UPDATE work_queue SET state='queued',worker=NULL,lease_expires_at=NULL,updated_at=? "
            "WHERE module=? AND state='running' AND worker=? AND last_attempt_id=?",
            (current, attempt["module"], worker, attempt_id),
        )


def renew_lease(
    connection: sqlite3.Connection,
    attempt_id: int,
    worker: str,
    *,
    lease_seconds: float = 900,
    now: float | None = None,
) -> float:
    """Extend one active lease atomically and return its new expiry."""
    if not worker or lease_seconds <= 0:
        raise IndexError("worker must be nonempty and lease_seconds must be positive")
    current = time.time() if now is None else now
    expires = current + lease_seconds
    with transaction(connection, immediate=True):
        row = connection.execute(
            "SELECT module FROM attempts WHERE attempt_id=? AND worker=? AND status='running'",
            (attempt_id, worker),
        ).fetchone()
        if row is None:
            raise IndexError("attempt is missing, completed, or owned by another worker")
        updated = connection.execute(
            "UPDATE work_queue SET lease_expires_at=?,updated_at=? WHERE module=? AND state='running' "
            "AND last_attempt_id=? AND worker=? AND lease_expires_at > ?",
            (expires, current, row["module"], attempt_id, worker, current),
        )
        if updated.rowcount != 1:
            raise IndexError("lease has expired; it cannot be renewed")
    return expires


def cached_result(
    connection: sqlite3.Connection,
    module: str,
    implementation_identity: object,
    toolchain_identity: object,
    dependency_digests: Mapping[str, str] | None = None,
) -> dict[str, Any] | None:
    """Return the exact current cache row, or ``None`` when it is stale/missing."""
    key, _ = cache_key(connection, module, implementation_identity, toolchain_identity, dependency_digests)
    row = connection.execute("SELECT * FROM result_cache WHERE cache_key=?", (key,)).fetchone()
    if row is None:
        return None
    value = dict(row)
    value["result"] = json.loads(value.pop("result_json"))
    return value


def record_result(
    connection: sqlite3.Connection,
    module: str,
    implementation_identity: object,
    toolchain_identity: object,
    *,
    status: str,
    result: object | None = None,
    translated: bool = False,
    failure: str | None = None,
    log_ref: str | None = None,
    artifact_ref: str | None = None,
    attempt_id: int | None = None,
    worker: str | None = None,
    verified: bool = False,
    now: float | None = None,
    dependency_digests: Mapping[str, str] | None = None,
) -> str:
    if status not in {"success", "failure", "partial"}:
        raise IndexError("status must be success, failure, or partial")
    if not isinstance(translated, bool):
        raise IndexError("translated must be boolean")
    if not isinstance(verified, bool):
        raise IndexError("verified must be boolean")
    key, dependencies = cache_key(connection, module, implementation_identity, toolchain_identity, dependency_digests)
    row = _module_row(connection, module)
    if status == "success" and translated and verified and row["unresolved_count"]:
        raise IndexError(
            f"module {module} has {row['unresolved_count']} unresolved occurrences; "
            "verified translation is prohibited"
        )
    current = time.time() if now is None else now
    stale_attempt = False
    expired_attempt = False
    with transaction(connection, immediate=True):
        if attempt_id is not None:
            attempt = connection.execute("SELECT * FROM attempts WHERE attempt_id=?", (attempt_id,)).fetchone()
            if attempt is None or attempt["module"] != module or attempt["status"] != "running":
                raise IndexError("attempt is missing or no longer active")
            if worker is not None and attempt["worker"] != worker:
                raise IndexError("attempt belongs to another worker")
            queue = connection.execute(
                "SELECT lease_expires_at FROM work_queue WHERE module=? AND last_attempt_id=?",
                (module, attempt_id),
            ).fetchone()
            if queue is None or queue["lease_expires_at"] is None or queue["lease_expires_at"] <= current:
                connection.execute(
                    "UPDATE attempts SET status='abandoned',failure='lease expired',finished_at=? WHERE attempt_id=?",
                    (current, attempt_id),
                )
                connection.execute(
                    "UPDATE work_queue SET state='queued',worker=NULL,lease_expires_at=NULL,updated_at=? "
                    "WHERE module=? AND last_attempt_id=?",
                    (current, module, attempt_id),
                )
                expired_attempt = True
            elif attempt["cache_key"] != key:
                connection.execute(
                    "UPDATE attempts SET status='stale',failure='source or identity changed',finished_at=? WHERE attempt_id=?",
                    (current, attempt_id),
                )
                stale_attempt = True
        if not stale_attempt and not expired_attempt:
            # A worker claim is useful cache data, but closure evidence needs
            # a separate explicit verification bit.  This prevents a
            # diagnostic ``translated=true`` or a zero-variant success from
            # counting as campaign coverage.
            if status == "success" and translated and verified:
                translation_status = "verified_translated"
            elif status == "success" and translated:
                translation_status = "candidate_translated"
            elif status == "success" and verified:
                translation_status = "verified_untranslated"
            elif translated:
                translation_status = "failed_translated"
            else:
                translation_status = "unverified"
            connection.execute(
                "INSERT INTO result_cache VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?) "
                "ON CONFLICT(cache_key) DO UPDATE SET status=excluded.status,translation_status=excluded.translation_status,"
                "result_json=excluded.result_json,failure=excluded.failure,log_ref=excluded.log_ref,"
                "artifact_ref=excluded.artifact_ref,recorded_at=excluded.recorded_at",
                (key, module, row["source_hash"], row["analysis_identity"], canonical(implementation_identity), canonical(toolchain_identity), dependencies,
                 status, translation_status, canonical(result), failure, log_ref, artifact_ref, current),
            )
            if attempt_id is not None:
                connection.execute(
                    "UPDATE attempts SET status=?,failure=?,log_ref=?,artifact_ref=?,finished_at=? WHERE attempt_id=?",
                    (status, failure, log_ref, artifact_ref, current, attempt_id),
                )
            connection.execute(
                "INSERT INTO work_queue(module,cache_key,state,updated_at) VALUES (?, ?, ?, ?) "
                "ON CONFLICT(module) DO UPDATE SET cache_key=excluded.cache_key,state=excluded.state,"
                "worker=NULL,lease_expires_at=NULL,updated_at=excluded.updated_at",
                (
                    module,
                    key,
                    "succeeded"
                    if status == "success" and translation_status == "verified_translated"
                    else "queued"
                    if status == "success"
                    else "failed",
                    current,
                ),
            )
    if expired_attempt:
        raise IndexError("lease expired; result was rejected and the module was re-queued")
    if stale_attempt:
        raise IndexError("result identity is stale; re-plan and claim the module")
    return key


def status(connection: sqlite3.Connection) -> dict[str, Any]:
    rows = connection.execute(
        "SELECT m.module,m.source_hash,m.diagnostic,m.unresolved_count,q.state,q.worker,q.lease_expires_at,"
        "r.status,r.translation_status,r.analysis_identity FROM modules m LEFT JOIN work_queue q ON q.module=m.module "
        "LEFT JOIN result_cache r ON r.cache_key=q.cache_key ORDER BY m.module"
    ).fetchall()
    counts: dict[str, int] = {}
    translated = 0
    for row in rows:
        state = row["state"] or "unplanned"
        counts[state] = counts.get(state, 0) + 1
        translated += (
            row["state"] == "succeeded"
            and row["status"] == "success"
            and row["translation_status"] == "verified_translated"
        )
    return {"schema": SCHEMA_VERSION, "modules": len(rows), "states": counts,
            "unresolved": sum(row["unresolved_count"] for row in rows), "translated": translated,
            "rows": [dict(row) for row in rows]}


def _json_identity(value: str) -> object:
    try:
        return json.loads(value)
    except json.JSONDecodeError:
        return value


def _dependency_digests(value: str | None) -> Mapping[str, str] | None:
    if value is None:
        return None
    parsed = _json_identity(value)
    if not isinstance(parsed, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in parsed.items()):
        raise IndexError("dependency digests must be a JSON object mapping module paths to strings")
    return parsed


def _read_dependency_map(path: str | None) -> Mapping[str, object] | None:
    if path is None:
        return None
    try:
        parsed = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise IndexError(f"cannot read dependency map {path}: {error}") from error
    if not isinstance(parsed, dict) or not all(isinstance(key, str) for key in parsed):
        raise IndexError("dependency map must be an object keyed by module@sourceHash")
    return parsed


def cli(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    init = sub.add_parser("init"); init.add_argument("database")
    imp = sub.add_parser("import-manifest"); imp.add_argument("database"); imp.add_argument("manifest"); imp.add_argument("--source-root"); imp.add_argument("--diagnostic", action="store_true", help="explicitly accept allowUnresolved=true and retain an unresolved backlog"); imp.add_argument("--dependency-map", help="JSON map keyed by module@sourceHash, produced by a trusted header parser")
    stat = sub.add_parser("status"); stat.add_argument("database")
    queue = sub.add_parser("queue"); queue.add_argument("database"); queue.add_argument("--implementation", default="campaign"); queue.add_argument("--toolchain", default="current"); queue.add_argument("--dependency-digests", help="JSON object for Mathlib modules outside this manifest"); queue.add_argument("--claim-worker"); queue.add_argument("--limit", type=int, default=1); queue.add_argument("--lease-seconds", type=float, default=900)
    rec = sub.add_parser("record-result"); rec.add_argument("database"); rec.add_argument("module"); rec.add_argument("--implementation", default="campaign"); rec.add_argument("--toolchain", default="current"); rec.add_argument("--dependency-digests", help="JSON object for Mathlib modules outside this manifest"); rec.add_argument("--status", required=True, choices=["success", "failure", "partial"]); rec.add_argument("--result", default="null"); rec.add_argument("--translated", action="store_true"); rec.add_argument("--verified", action="store_true"); rec.add_argument("--failure"); rec.add_argument("--log-ref"); rec.add_argument("--artifact-ref"); rec.add_argument("--attempt-id", type=int); rec.add_argument("--worker")
    args = parser.parse_args(argv)
    if args.command == "init":
        initialize(args.database); return 0
    connection = connect(args.database)
    try:
        if args.command == "import-manifest":
            output = import_manifest(connection, args.manifest, source_root=args.source_root, diagnostic=args.diagnostic, dependency_map=_read_dependency_map(args.dependency_map))
        elif args.command == "status":
            output = status(connection)
        elif args.command == "queue":
            output = {"plan": plan_work(connection, _json_identity(args.implementation), _json_identity(args.toolchain), dependency_digests=_dependency_digests(args.dependency_digests))}
            if args.claim_worker:
                output["leases"] = [lease.__dict__ for lease in claim_work(connection, args.claim_worker, limit=args.limit, lease_seconds=args.lease_seconds)]
        else:
            output = {"cacheKey": record_result(connection, args.module, _json_identity(args.implementation), _json_identity(args.toolchain), status=args.status, result=_json_identity(args.result), translated=args.translated, verified=args.verified, failure=args.failure, log_ref=args.log_ref, artifact_ref=args.artifact_ref, attempt_id=args.attempt_id, worker=args.worker, dependency_digests=_dependency_digests(args.dependency_digests))}
        print(json.dumps(output, sort_keys=True, indent=2))
    except IndexError as error:
        print(f"translation-index: {error}", file=sys.stderr)
        return 2
    finally:
        connection.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(cli())
