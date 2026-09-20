#!/usr/bin/env python3
"""Build the minimal pinned-Mathlib source-command SQLite database."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
from typing import Any, Iterable, NoReturn

ROOT = Path(__file__).resolve().parent.parent
EXTRACTOR = ROOT / ".lake" / "build" / "bin" / "sourceCommandExtractor"


def _error(message: str) -> NoReturn:
    raise RuntimeError(message)


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _allowed_relative(path: Path) -> bool:
    return path == Path("Mathlib.lean") or (
        len(path.parts) >= 2 and path.parts[0] == "Mathlib" and path.suffix == ".lean"
    )


def _module_files(mathlib_root: Path, requested: list[str]) -> list[Path]:
    if requested:
        candidates = [mathlib_root / Path(item) for item in requested]
    else:
        candidates = [mathlib_root / "Mathlib.lean"] + sorted(
            (mathlib_root / "Mathlib").rglob("*.lean")
        )
    result: list[Path] = []
    seen: set[Path] = set()
    for candidate in candidates:
        try:
            path = candidate.resolve(strict=True)
        except OSError as exc:
            _error(f"source file does not exist: {candidate}: {exc}")
        if path.suffix != ".lean" or not path.is_file():
            _error(f"not a Lean source file: {path}")
        try:
            relative = path.relative_to(mathlib_root)
        except ValueError:
            _error(f"source file is outside --mathlib-root: {path}")
        if not _allowed_relative(relative):
            _error(
                "source file is outside the pinned Mathlib set "
                f"(Mathlib.lean or Mathlib/**/*.lean): {relative}"
            )
        if path in seen:
            _error(f"duplicate source file: {path}")
        seen.add(path)
        result.append(path)
    if not requested:
        result.sort(key=lambda path: path.relative_to(mathlib_root).as_posix())
    return result


def _module_name(mathlib_root: Path, path: Path) -> str:
    relative = path.relative_to(mathlib_root).with_suffix("")
    return ".".join(relative.parts)


def _json_object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        _error(f"extractor output for {label} is not an object")
    return value


def _nat(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        _error(f"{label} is not a natural number")
    return value


def _text(value: Any, label: str) -> str:
    if not isinstance(value, str):
        _error(f"{label} is not text")
    return value


def _extractor_command(paths: Iterable[Path]) -> list[str]:
    if not EXTRACTOR.is_file():
        subprocess.run(["lake", "build", "sourceCommandExtractor"], cwd=ROOT, check=True)
    if not EXTRACTOR.is_file():
        _error(f"Lean extractor was not built: {EXTRACTOR}")
    return ["lake", "env", str(EXTRACTOR), *(str(path) for path in paths)]


def _read_records(paths: list[Path]) -> list[dict[str, Any]]:
    # Lean's imported-environment objects are intentionally bounded to a small
    # worker batch.  Restarting the extractor prevents native frontend state
    # from accumulating across the full pinned tree.
    batch_size = 16
    records: list[dict[str, Any]] = []
    for batch_start in range(0, len(paths), batch_size):
        batch = paths[batch_start:batch_start + batch_size]
        with tempfile.TemporaryFile() as error_stream:
            process = subprocess.Popen(
                _extractor_command(batch),
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=error_stream,
            )
            assert process.stdout is not None
            try:
                for line_number, raw_line in enumerate(process.stdout, start=1):
                    if not raw_line.strip():
                        _error(f"extractor emitted a blank line at batch output line {line_number}")
                    try:
                        value = json.loads(raw_line.decode("utf-8"))
                    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                        _error(f"malformed extractor output at batch line {line_number}: {exc}")
                    records.append(_json_object(value, f"batch line {line_number}"))
            finally:
                process.stdout.close()
            return_code = process.wait()
            if return_code != 0:
                error_stream.seek(0)
                diagnostic = error_stream.read().decode("utf-8", errors="replace").strip()
                _error(
                    f"Lean parser failed (exit {return_code})"
                    + (f":\n{diagnostic}" if diagnostic else "")
                )
        if len(records) != batch_start + len(batch):
            _error(f"extractor emitted an incomplete batch at source {batch_start}")
    if len(records) != len(paths):
        _error(f"extractor emitted {len(records)} records for {len(paths)} source files")
    return records


def _validate_record(
    record: dict[str, Any], path: Path, source: bytes, module_name: str
) -> tuple[list[str], list[tuple[int, int, str, str]]]:
    if set(record) != {"path", "imports", "commands"}:
        _error(f"malformed extractor fields for {module_name}")
    if record["path"] != str(path):
        _error(f"extractor path mismatch for {module_name}: {record.get('path')!r}")
    imports_value = record["imports"]
    commands_value = record["commands"]
    if not isinstance(imports_value, list) or not isinstance(commands_value, list):
        _error(f"malformed extractor arrays for {module_name}")

    imports: list[str] = []
    seen_imports: set[str] = set()
    for ordinal, raw_import in enumerate(imports_value):
        imported = _json_object(raw_import, f"{module_name} import {ordinal}")
        if set(imported) != {"name"}:
            _error(f"malformed import output in {module_name}")
        name = _text(imported["name"], f"{module_name} import name")
        if not name or name in seen_imports:
            _error(f"empty or duplicate imported module in {module_name}: {name!r}")
        seen_imports.add(name)
        imports.append(name)

    previous_end = 0
    commands: list[tuple[int, int, str, str]] = []
    for ordinal, raw_command in enumerate(commands_value):
        command = _json_object(raw_command, f"{module_name} command {ordinal}")
        if set(command) != {"ordinal", "startByte", "endByte", "kind"}:
            _error(f"malformed command output in {module_name} command {ordinal}")
        if command["ordinal"] != ordinal:
            _error(f"non-sequential command ordinal in {module_name}")
        start = _nat(command["startByte"], f"{module_name} command start")
        end = _nat(command["endByte"], f"{module_name} command end")
        if start >= end or end > len(source):
            _error(f"invalid command range [{start}, {end}) in {module_name}")
        if start < previous_end:
            _error(f"overlapping or nonmonotone command ranges in {module_name}")
        kind = _text(command["kind"], f"{module_name} command kind")
        if not kind:
            _error(f"empty command kind in {module_name} command {ordinal}")
        try:
            source[start:end].decode("utf-8")
        except UnicodeDecodeError as exc:
            _error(f"command range splits UTF-8 in {module_name}: {exc}")
        commands.append((start, end, kind, _sha256(source[start:end])))
        previous_end = end
    return imports, commands


_SCHEMA = """
CREATE TABLE modules (
    name TEXT PRIMARY KEY,
    path TEXT NOT NULL UNIQUE,
    source BLOB NOT NULL,
    source_sha256 TEXT NOT NULL
);
CREATE TABLE imports (
    module_name TEXT NOT NULL REFERENCES modules(name),
    imported_name TEXT NOT NULL,
    PRIMARY KEY(module_name, imported_name)
);
CREATE TABLE commands (
    module_name TEXT NOT NULL REFERENCES modules(name),
    ordinal INTEGER NOT NULL CHECK(ordinal >= 0),
    start_byte INTEGER NOT NULL CHECK(start_byte >= 0),
    end_byte INTEGER NOT NULL CHECK(end_byte > start_byte),
    kind TEXT NOT NULL,
    source_sha256 TEXT NOT NULL,
    PRIMARY KEY(module_name, ordinal)
);
"""


def _validate_graph(module_names: set[str], imports: dict[str, list[str]]) -> None:
    adjacency = {
        name: {imported for imported in imports.get(name, []) if imported in module_names}
        for name in module_names
    }
    indegree = {name: 0 for name in module_names}
    for imported_names in adjacency.values():
        for imported in imported_names:
            indegree[imported] += 1
    ready = sorted(name for name, degree in indegree.items() if degree == 0)
    covered = 0
    while ready:
        name = ready.pop(0)
        covered += 1
        for imported in sorted(adjacency[name]):
            indegree[imported] -= 1
            if indegree[imported] == 0:
                ready.append(imported)
                ready.sort()
    if covered != len(module_names):
        cycle_nodes = sorted(name for name, degree in indegree.items() if degree > 0)
        _error(f"internal Mathlib import cycle: {', '.join(cycle_nodes)}")


def _insert_database(
    db_path: Path,
    records: list[dict[str, Any]],
    paths: list[Path],
    mathlib_root: Path,
    sources: dict[Path, bytes],
) -> tuple[int, int, int]:
    connection = sqlite3.connect(db_path)
    try:
        connection.execute("PRAGMA foreign_keys = ON")
        connection.executescript(_SCHEMA)
        modules_seen: set[str] = set()
        paths_seen: set[str] = set()
        imports_by_module: dict[str, list[str]] = {}
        parsed: list[tuple[str, str, bytes, str, list[str], list[tuple[int, int, str, str]]]] = []
        for record, path in zip(records, paths):
            module_name = _module_name(mathlib_root, path)
            relative_path = path.relative_to(mathlib_root).as_posix()
            if module_name in modules_seen:
                _error(f"duplicate module name: {module_name}")
            if relative_path in paths_seen:
                _error(f"duplicate module path: {relative_path}")
            modules_seen.add(module_name)
            paths_seen.add(relative_path)
            source = sources[path]
            imports, commands = _validate_record(record, path, source, module_name)
            modules_sha256 = _sha256(source)
            parsed.append((module_name, relative_path, source, modules_sha256, imports, commands))
            imports_by_module[module_name] = imports
        _validate_graph(modules_seen, imports_by_module)

        connection.execute("BEGIN")
        for module_name, relative_path, source, source_sha256, imports, commands in parsed:
            connection.execute(
                "INSERT INTO modules(name, path, source, source_sha256) VALUES (?, ?, ?, ?)",
                (module_name, relative_path, source, source_sha256),
            )
            for imported_name in imports:
                connection.execute(
                    "INSERT INTO imports(module_name, imported_name) VALUES (?, ?)",
                    (module_name, imported_name),
                )
            for ordinal, (start, end, kind, source_sha256) in enumerate(commands):
                connection.execute(
                    "INSERT INTO commands(module_name, ordinal, start_byte, end_byte, kind, source_sha256) "
                    "VALUES (?, ?, ?, ?, ?, ?)",
                    (module_name, ordinal, start, end, kind, source_sha256),
                )
        foreign_keys = connection.execute("PRAGMA foreign_key_check").fetchall()
        if foreign_keys:
            _error(f"SQLite foreign_key_check failed: {foreign_keys}")
        integrity = connection.execute("PRAGMA integrity_check").fetchone()[0]
        if integrity != "ok":
            _error(f"SQLite integrity_check failed: {integrity}")
        connection.commit()
        return len(parsed), sum(len(item[4]) for item in parsed), sum(len(item[5]) for item in parsed)
    except Exception:
        connection.rollback()
        raise
    finally:
        connection.close()


def build(args: argparse.Namespace) -> int:
    mathlib_root = Path(args.mathlib_root).resolve(strict=True)
    if not mathlib_root.is_dir():
        _error(f"--mathlib-root is not a directory: {mathlib_root}")
    output = Path(args.output).resolve()
    try:
        output.relative_to(mathlib_root)
    except ValueError:
        pass
    else:
        _error("--output must not be inside the read-only Mathlib package tree")
    if output.exists() or os.path.lexists(output):
        if not args.overwrite:
            _error(f"destination already exists; pass --overwrite: {output}")
        if output.is_dir():
            _error(f"destination is a directory: {output}")
    if not output.parent.is_dir():
        _error(f"destination parent does not exist: {output.parent}")
    paths = _module_files(mathlib_root, args.files)
    if not paths:
        _error(f"no pinned Mathlib .lean files under: {mathlib_root}")
    sources = {path: path.read_bytes() for path in paths}
    before_hashes = {path: _sha256(source) for path, source in sources.items()}
    records = _read_records(paths)
    after_sources = {path: path.read_bytes() for path in paths}
    after_hashes = {path: _sha256(source) for path, source in after_sources.items()}
    if before_hashes != after_hashes:
        _error("pinned Mathlib source changed while extracting")
    if records and [record.get("path") for record in records] != [str(path) for path in paths]:
        _error("extractor output is incomplete, reordered, or contains duplicate paths")
    if len(records) != len(paths):
        _error(f"extractor emitted {len(records)} records for {len(paths)} source files")

    temp_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            dir=output.parent, prefix=f".{output.name}.", suffix=".tmp", delete=False
        ) as temporary:
            temp_path = Path(temporary.name)
        counts = _insert_database(temp_path, records, paths, mathlib_root, after_sources)
        if output.exists() or os.path.lexists(output):
            if not args.overwrite:
                _error(f"destination appeared during build; refusing: {output}")
            if output.is_dir():
                _error(f"destination became a directory: {output}")
        os.replace(temp_path, output)
        temp_path = None
    finally:
        if temp_path is not None:
            temp_path.unlink(missing_ok=True)
    print(json.dumps({"output": str(output), "modules": counts[0], "imports": counts[1],
                      "commands": counts[2], "bytes": output.stat().st_size}, sort_keys=True))
    return 0


def stats(args: argparse.Namespace) -> int:
    path = Path(args.database).resolve(strict=True)
    connection = sqlite3.connect(path)
    try:
        tables = [row[0] for row in connection.execute(
            "SELECT name FROM sqlite_master WHERE type = 'table' ORDER BY name"
        )]
        if tables != ["commands", "imports", "modules"]:
            _error(f"unexpected database tables: {tables}")
        result = {
            "database": str(path),
            "bytes": path.stat().st_size,
            "modules": connection.execute("SELECT count(*) FROM modules").fetchone()[0],
            "imports": connection.execute("SELECT count(*) FROM imports").fetchone()[0],
            "commands": connection.execute("SELECT count(*) FROM commands").fetchone()[0],
        }
        print(json.dumps(result, sort_keys=True))
        return 0
    finally:
        connection.close()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="subcommand", required=True)
    build_parser = subparsers.add_parser("build", help="parse pinned Lean files and atomically build a fresh database")
    build_parser.add_argument("--mathlib-root", required=True, help="read-only pinned Mathlib package root")
    build_parser.add_argument("--output", required=True, help="SQLite destination path outside the package tree")
    build_parser.add_argument("--overwrite", action="store_true", help="replace an existing destination explicitly")
    build_parser.add_argument("files", nargs="*", help="optional package-relative Mathlib.lean selectors")
    build_parser.set_defaults(function=build)
    stats_parser = subparsers.add_parser("stats", help="report counts from a T61 database")
    stats_parser.add_argument("database")
    stats_parser.set_defaults(function=stats)
    args = parser.parse_args(argv)
    try:
        return args.function(args)
    except (OSError, RuntimeError, sqlite3.Error, subprocess.CalledProcessError) as exc:
        print(f"source-command-db: error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
