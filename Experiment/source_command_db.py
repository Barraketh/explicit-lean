#!/usr/bin/env python3
"""Build the minimal pinned-Mathlib source-command SQLite database."""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
import hashlib
import heapq
import json
import os
from pathlib import Path
import signal
import sqlite3
import subprocess
import sys
import tempfile
import threading
import time
from typing import Any, Callable, Iterable, NoReturn

ROOT = Path(__file__).resolve().parent.parent
EXTRACTOR = ROOT / ".lake" / "build" / "bin" / "sourceCommandExtractor"


class _Interrupted(Exception):
    def __init__(self, signum: int) -> None:
        super().__init__()
        self.signum = signum
        self.exit_code = 128 + signum


class _ExtractionCancelled(Exception):
    """A worker was stopped after another worker or the coordinator failed."""


_STOP_REQUESTED = False
_STOP_SIGNAL: int | None = None
_CANCEL_REQUESTED = threading.Event()
_PROCESS_LOCK = threading.Lock()
_ACTIVE_PROCESSES: dict[int, subprocess.Popen[Any]] = {}


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


def _inventory(
    mathlib_root: Path, paths: list[Path]
) -> dict[str, tuple[str, Path]]:
    """Return the deterministic name/path inventory used by this invocation."""
    result: dict[str, tuple[str, Path]] = {}
    paths_seen: set[str] = set()
    for path in paths:
        module_name = _module_name(mathlib_root, path)
        relative_path = path.relative_to(mathlib_root).as_posix()
        if module_name in result:
            _error(f"duplicate module name: {module_name}")
        if relative_path in paths_seen:
            _error(f"duplicate module path: {relative_path}")
        paths_seen.add(relative_path)
        result[module_name] = (relative_path, path)
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


def _terminate_process_group(process: subprocess.Popen[Any], force: bool = False) -> None:
    """Terminate one extractor and every child in its private process group."""
    termination_signal = signal.SIGKILL if force else signal.SIGTERM
    if os.name == "posix":
        try:
            os.killpg(os.getpgid(process.pid), termination_signal)
            return
        except (OSError, ProcessLookupError):
            pass
    try:
        (process.kill if force else process.terminate)()
    except (OSError, ProcessLookupError):
        pass


def _register_process(process: subprocess.Popen[Any]) -> None:
    with _PROCESS_LOCK:
        _ACTIVE_PROCESSES[id(process)] = process
    # A signal or a failed peer may arrive between Popen and registration.
    if _STOP_REQUESTED or _CANCEL_REQUESTED.is_set():
        _terminate_process_group(process)


def _unregister_process(process: subprocess.Popen[Any]) -> None:
    with _PROCESS_LOCK:
        _ACTIVE_PROCESSES.pop(id(process), None)


def _terminate_active_processes(force: bool = False) -> None:
    with _PROCESS_LOCK:
        processes = tuple(_ACTIVE_PROCESSES.values())
    for process in processes:
        _terminate_process_group(process, force=force)


def _reap_active_processes() -> None:
    """Defensively reap anything still registered after executor shutdown."""
    with _PROCESS_LOCK:
        processes = tuple(_ACTIVE_PROCESSES.values())
    for process in processes:
        _terminate_process_group(process, force=True)
        try:
            process.wait(timeout=5.0)
        except subprocess.TimeoutExpired:
            _terminate_process_group(process, force=True)
            process.wait(timeout=5.0)
        finally:
            _unregister_process(process)


def _cancel_extractor_workers() -> None:
    _CANCEL_REQUESTED.set()
    _terminate_active_processes()


def _finish_process(process: subprocess.Popen[Any]) -> int:
    """Stop a process group after cancellation and always reap its leader."""
    if not (_STOP_REQUESTED or _CANCEL_REQUESTED.is_set()):
        return process.wait()
    _terminate_process_group(process)
    try:
        return process.wait(timeout=1.0)
    except subprocess.TimeoutExpired:
        _terminate_process_group(process, force=True)
        return process.wait(timeout=5.0)


def _request_stop(signum: int, _frame: Any) -> None:
    global _STOP_REQUESTED, _STOP_SIGNAL
    _STOP_REQUESTED = True
    if _STOP_SIGNAL is None:
        _STOP_SIGNAL = signum
    _cancel_extractor_workers()


def _check_stop() -> None:
    if _STOP_REQUESTED:
        raise _Interrupted(_STOP_SIGNAL or signal.SIGINT)


def _check_worker_abort() -> None:
    _check_stop()
    if _CANCEL_REQUESTED.is_set():
        raise _ExtractionCancelled()


def _install_signal_handlers() -> dict[int, Any]:
    global _STOP_REQUESTED, _STOP_SIGNAL
    _STOP_REQUESTED = False
    _STOP_SIGNAL = None
    _CANCEL_REQUESTED.clear()
    previous: dict[int, Any] = {}
    for signum in (signal.SIGINT, signal.SIGTERM):
        previous[signum] = signal.getsignal(signum)
        signal.signal(signum, _request_stop)
    return previous


def _restore_signal_handlers(previous: dict[int, Any]) -> None:
    for signum, handler in previous.items():
        signal.signal(signum, handler)


def _ensure_extractor() -> None:
    if EXTRACTOR.is_file():
        return
    _check_stop()
    with tempfile.TemporaryFile() as log:
        process = subprocess.Popen(
            ["lake", "build", "sourceCommandExtractor"],
            cwd=ROOT,
            stdout=log,
            stderr=log,
            start_new_session=(os.name == "posix"),
        )
        _register_process(process)
        try:
            return_code = _finish_process(process)
        finally:
            _unregister_process(process)
        if _STOP_REQUESTED:
            _check_stop()
        if return_code != 0:
            log.seek(0)
            diagnostic = log.read().decode("utf-8", errors="replace").strip()
            _error(
                f"could not build Lean extractor (exit {return_code})"
                + (f":\n{diagnostic}" if diagnostic else "")
            )
    if not EXTRACTOR.is_file():
        _error(f"Lean extractor was not built: {EXTRACTOR}")


def _extractor_command(paths: Iterable[Path]) -> list[str]:
    _ensure_extractor()
    return ["lake", "env", str(EXTRACTOR), *(str(path) for path in paths)]


def _read_records(paths: list[Path]) -> list[dict[str, Any]]:
    """Run one bounded extractor worker and return exactly one record per path."""
    if not paths:
        return []
    _check_worker_abort()
    with tempfile.TemporaryFile() as error_stream:
        process = subprocess.Popen(
            _extractor_command(paths),
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=error_stream,
            start_new_session=(os.name == "posix"),
        )
        _register_process(process)
        records: list[dict[str, Any]] = []
        return_code: int | None = None
        assert process.stdout is not None
        try:
            try:
                for line_number, raw_line in enumerate(process.stdout, start=1):
                    _check_worker_abort()
                    if not raw_line.strip():
                        _error(
                            f"extractor emitted a blank line at batch output line {line_number}"
                        )
                    try:
                        value = json.loads(raw_line.decode("utf-8"))
                    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                        _error(f"malformed extractor output at batch line {line_number}: {exc}")
                    records.append(_json_object(value, f"batch line {line_number}"))
            except BaseException:
                # A malformed result must not leave a producer blocked on a
                # pipe while the coordinator waits for the failed future.
                _terminate_process_group(process)
                raise
        finally:
            process.stdout.close()
            try:
                return_code = _finish_process(process)
            finally:
                _unregister_process(process)
        _check_worker_abort()
        if return_code != 0:
            error_stream.seek(0)
            diagnostic = error_stream.read().decode("utf-8", errors="replace").strip()
            _error(
                f"Lean parser failed (exit {return_code})"
                + (f":\n{diagnostic}" if diagnostic else "")
            )
    if len(records) != len(paths):
        _error(f"extractor emitted {len(records)} records for {len(paths)} source files")
    if [record.get("path") for record in records] != [str(path) for path in paths]:
        _error("extractor output is incomplete, reordered, or contains duplicate paths")
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


def _schema_signature(connection: sqlite3.Connection) -> tuple[Any, ...]:
    objects = tuple(
        connection.execute(
            "SELECT type,name,tbl_name,sql FROM sqlite_master ORDER BY type,name"
        ).fetchall()
    )
    columns = tuple(
        (
            table,
            tuple(connection.execute(f"PRAGMA table_info({table})").fetchall()),
        )
        for table in ("modules", "imports", "commands")
    )
    foreign_keys = tuple(
        (
            table,
            tuple(connection.execute(f"PRAGMA foreign_key_list({table})").fetchall()),
        )
        for table in ("modules", "imports", "commands")
    )
    indexes = tuple(
        (
            table,
            tuple(
                sorted(
                    (row[1], row[2], row[3], row[4])
                    for row in connection.execute(f"PRAGMA index_list({table})")
                )
            ),
        )
        for table in ("modules", "imports", "commands")
    )
    return objects, columns, foreign_keys, indexes


def _expected_schema_signature() -> tuple[Any, ...]:
    connection = sqlite3.connect(":memory:")
    try:
        connection.executescript(_SCHEMA)
        return _schema_signature(connection)
    finally:
        connection.close()


_EXPECTED_SCHEMA_SIGNATURE = _expected_schema_signature()


def _validate_schema(connection: sqlite3.Connection) -> None:
    if _schema_signature(connection) != _EXPECTED_SCHEMA_SIGNATURE:
        _error("partial database has an unexpected schema")


def _connect_database(path: Path) -> sqlite3.Connection:
    connection = sqlite3.connect(path)
    connection.execute("PRAGMA foreign_keys = ON")
    connection.execute("PRAGMA synchronous = FULL")
    connection.execute("PRAGMA journal_mode = DELETE")
    return connection


def _create_partial_database(path: Path) -> None:
    connection = _connect_database(path)
    try:
        connection.executescript(_SCHEMA)
        connection.commit()
        _validate_schema(connection)
    finally:
        connection.close()
    _fsync_file(path)


def _fsync_file(path: Path) -> None:
    with path.open("rb") as handle:
        os.fsync(handle.fileno())


def _fsync_directory(path: Path) -> None:
    flags = os.O_RDONLY
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    descriptor = os.open(path, flags)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _discard_partial(path: Path) -> None:
    if not os.path.lexists(path):
        return
    if path.is_dir() and not path.is_symlink():
        _error(f"partial destination is a directory: {path}")
    path.unlink()


def _validate_partial(
    connection: sqlite3.Connection,
    inventory: dict[str, tuple[str, Path]],
    sources: dict[Path, bytes],
) -> tuple[set[str], dict[str, list[str]]]:
    """Validate committed rows and return the completed module subset."""
    _validate_schema(connection)
    foreign_keys = connection.execute("PRAGMA foreign_key_check").fetchall()
    if foreign_keys:
        _error(f"SQLite foreign_key_check failed: {foreign_keys}")
    integrity = connection.execute("PRAGMA integrity_check").fetchone()[0]
    if integrity != "ok":
        _error(f"SQLite integrity_check failed: {integrity}")

    completed: set[str] = set()
    for name, relative_path, source_value, source_sha256 in connection.execute(
        "SELECT name,path,source,source_sha256 FROM modules"
    ):
        if not isinstance(name, str) or not isinstance(relative_path, str):
            _error("partial modules row has a non-text name or path")
        expected = inventory.get(name)
        if expected is None:
            _error(f"partial database has extra module: {name}")
        expected_path, path = expected
        if relative_path != expected_path:
            _error(f"partial path mismatch for {name}: {relative_path!r}")
        if not isinstance(source_value, (bytes, bytearray, memoryview)):
            _error(f"partial source is not a BLOB for {name}")
        source = bytes(source_value)
        expected_source = sources[path]
        if source != expected_source:
            _error(f"partial source drift for {name}")
        if not isinstance(source_sha256, str) or source_sha256 != _sha256(source):
            _error(f"partial source hash mismatch for {name}")
        completed.add(name)

    imports: dict[str, list[str]] = {name: [] for name in completed}
    for module_name, imported_name in connection.execute(
        "SELECT module_name,imported_name FROM imports ORDER BY module_name,imported_name"
    ):
        if not isinstance(module_name, str) or module_name not in completed:
            _error(f"partial imports row has an unknown module: {module_name!r}")
        if not isinstance(imported_name, str) or not imported_name:
            _error(f"partial imports row has an invalid imported name: {imported_name!r}")
        if imported_name in imports[module_name]:
            _error(f"partial imports row is duplicated for {module_name}: {imported_name}")
        imports[module_name].append(imported_name)

    previous_end: dict[str, int] = {}
    next_ordinal: dict[str, int] = {name: 0 for name in completed}
    for module_name, ordinal, start, end, kind, source_sha256 in connection.execute(
        "SELECT module_name,ordinal,start_byte,end_byte,kind,source_sha256 "
        "FROM commands ORDER BY module_name,ordinal"
    ):
        if not isinstance(module_name, str) or module_name not in completed:
            _error(f"partial commands row has an unknown module: {module_name!r}")
        if not isinstance(ordinal, int) or ordinal < 0:
            _error(f"partial command ordinal is invalid for {module_name}")
        if ordinal != next_ordinal[module_name]:
            _error(f"partial command ordinals are not sequential for {module_name}")
        if not isinstance(start, int) or not isinstance(end, int):
            _error(f"partial command bounds are not integers for {module_name}")
        source = sources[inventory[module_name][1]]
        if start < 0 or start >= end or end > len(source):
            _error(f"partial command range [{start}, {end}) is invalid for {module_name}")
        if start < previous_end.get(module_name, 0):
            _error(f"partial command ranges overlap for {module_name}")
        try:
            source[start:end].decode("utf-8")
        except UnicodeDecodeError as exc:
            _error(f"partial command range splits UTF-8 for {module_name}: {exc}")
        if not isinstance(kind, str) or not kind:
            _error(f"partial command kind is invalid for {module_name}")
        if not isinstance(source_sha256, str) or source_sha256 != _sha256(source[start:end]):
            _error(f"partial command slice hash mismatch for {module_name} ordinal {ordinal}")
        previous_end[module_name] = end
        next_ordinal[module_name] += 1
    return completed, imports


def _validate_graph(module_names: set[str], imports: dict[str, list[str]]) -> None:
    unexpected = set(imports) - module_names
    if unexpected:
        _error(f"import graph has unknown module rows: {', '.join(sorted(unexpected))}")
    adjacency = {
        name: {imported for imported in imports.get(name, []) if imported in module_names}
        for name in module_names
    }
    indegree = {name: 0 for name in module_names}
    for imported_names in adjacency.values():
        for imported in imported_names:
            indegree[imported] += 1
    ready = [name for name, degree in indegree.items() if degree == 0]
    heapq.heapify(ready)
    covered = 0
    while ready:
        name = heapq.heappop(ready)
        covered += 1
        for imported in sorted(adjacency[name]):
            indegree[imported] -= 1
            if indegree[imported] == 0:
                heapq.heappush(ready, imported)
    if covered != len(module_names):
        cycle_nodes = sorted(name for name, degree in indegree.items() if degree > 0)
        _error(f"internal Mathlib import cycle: {', '.join(cycle_nodes)}")


def _parse_batch(
    records: list[dict[str, Any]],
    paths: list[Path],
    mathlib_root: Path,
    sources: dict[Path, bytes],
) -> list[tuple[str, str, bytes, str, list[str], list[tuple[int, int, str, str]]]]:
    if len(records) != len(paths):
        _error(f"extractor emitted {len(records)} records for {len(paths)} source files")
    parsed: list[tuple[str, str, bytes, str, list[str], list[tuple[int, int, str, str]]]] = []
    seen: set[str] = set()
    for record, path in zip(records, paths):
        module_name = _module_name(mathlib_root, path)
        if module_name in seen:
            _error(f"duplicate module name in extractor batch: {module_name}")
        seen.add(module_name)
        source = sources[path]
        imports, commands = _validate_record(record, path, source, module_name)
        parsed.append(
            (
                module_name,
                path.relative_to(mathlib_root).as_posix(),
                source,
                _sha256(source),
                imports,
                commands,
            )
        )
    return parsed


def _insert_batch(
    connection: sqlite3.Connection,
    parsed: list[tuple[str, str, bytes, str, list[str], list[tuple[int, int, str, str]]]],
) -> tuple[int, int, int]:
    if not parsed:
        return 0, 0, 0
    try:
        _check_stop()
        connection.execute("BEGIN IMMEDIATE")
        for module_name, relative_path, source, source_sha256, imports, commands in parsed:
            _check_stop()
            connection.execute(
                "INSERT INTO modules(name,path,source,source_sha256) VALUES (?, ?, ?, ?)",
                (module_name, relative_path, source, source_sha256),
            )
            for imported_name in imports:
                connection.execute(
                    "INSERT INTO imports(module_name,imported_name) VALUES (?, ?)",
                    (module_name, imported_name),
                )
            for ordinal, (start, end, kind, slice_sha256) in enumerate(commands):
                connection.execute(
                    "INSERT INTO commands(module_name,ordinal,start_byte,end_byte,kind,source_sha256) "
                    "VALUES (?, ?, ?, ?, ?, ?)",
                    (module_name, ordinal, start, end, kind, slice_sha256),
                )
        if _STOP_REQUESTED:
            connection.rollback()
            _check_stop()
        connection.commit()
    except Exception:
        if connection.in_transaction:
            connection.rollback()
        raise
    return (
        len(parsed),
        sum(len(item[4]) for item in parsed),
        sum(len(item[5]) for item in parsed),
    )


def _run_extraction_batches(
    batches: list[tuple[int, list[Path]]],
    jobs: int,
    on_completed: Callable[[int, list[Path], list[dict[str, Any]]], None],
) -> None:
    """Extract batches concurrently while keeping validation in the caller thread."""
    if not batches:
        return
    executor = ThreadPoolExecutor(max_workers=jobs, thread_name_prefix="source-extractor")
    in_flight: dict[Future[list[dict[str, Any]]], tuple[int, list[Path]]] = {}
    next_batch = 0

    def submit_next() -> None:
        nonlocal next_batch
        if next_batch >= len(batches):
            return
        _check_stop()
        batch_number, batch_paths = batches[next_batch]
        next_batch += 1
        future = executor.submit(_read_records, batch_paths)
        in_flight[future] = (batch_number, batch_paths)

    try:
        while len(in_flight) < jobs and next_batch < len(batches):
            submit_next()
        while in_flight:
            done, _ = wait(tuple(in_flight), return_when=FIRST_COMPLETED)
            for future in done:
                batch_number, batch_paths = in_flight.pop(future)
                records = future.result()
                _check_stop()
                # This callback runs only on the coordinator thread.  It owns
                # record validation, SQLite transactions, and progress output.
                on_completed(batch_number, batch_paths, records)
                submit_next()
    except BaseException:
        # A parser, validator, database, or signal failure invalidates every
        # outstanding worker.  Completed transactions remain durable in the
        # partial database; no result from an incomplete batch is committed.
        _cancel_extractor_workers()
        for future in in_flight:
            future.cancel()
        raise
    finally:
        for future in in_flight:
            future.cancel()
        executor.shutdown(wait=True, cancel_futures=True)
        if _CANCEL_REQUESTED.is_set():
            _terminate_active_processes(force=True)
        _reap_active_processes()


def _source_snapshot(paths: list[Path]) -> dict[Path, bytes]:
    return {path: path.read_bytes() for path in paths}


def _assert_sources_unchanged(paths: list[Path], sources: dict[Path, bytes]) -> None:
    for path in paths:
        if path.read_bytes() != sources[path]:
            _error(f"pinned Mathlib source changed while extracting: {path}")


def _emit_progress(
    *,
    event: str,
    completed: int,
    total: int,
    already_complete: int,
    batch: int,
    batch_modules: int,
    completed_batches: int,
    total_batches: int,
    started: float,
) -> None:
    elapsed = max(0.0, time.monotonic() - started)
    processed = completed - already_complete
    rate = processed / elapsed if processed and elapsed > 0 else None
    remaining = total - completed
    eta = remaining / rate if rate and remaining else (0.0 if remaining == 0 and rate else None)
    payload = {
        "event": event,
        "completed_modules": completed,
        "total_modules": total,
        "already_complete": already_complete,
        "batch": batch,
        "current_batch": batch,
        "batch_modules": batch_modules,
        "completed_batches": completed_batches,
        "total_batches": total_batches,
        "elapsed_seconds": round(elapsed, 3),
        "modules_per_second": None if rate is None else round(rate, 3),
        "eta_seconds": None if eta is None else round(eta, 3),
    }
    print(json.dumps(payload, sort_keys=True), file=sys.stderr, flush=True)


def _counts(connection: sqlite3.Connection) -> tuple[int, int, int]:
    return tuple(
        connection.execute(f"SELECT count(*) FROM {table}").fetchone()[0]
        for table in ("modules", "imports", "commands")
    )  # type: ignore[return-value]


def _build(args: argparse.Namespace) -> int:
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
        if output.is_dir() or output.is_symlink():
            _error(f"destination is not a regular database file: {output}")
    if not output.parent.is_dir():
        _error(f"destination parent does not exist: {output.parent}")
    if args.batch_size <= 0:
        _error("--batch-size must be positive")
    if args.jobs <= 0:
        _error("--jobs must be positive")

    paths = _module_files(mathlib_root, args.files)
    if not paths:
        _error(f"no pinned Mathlib .lean files under: {mathlib_root}")
    inventory = _inventory(mathlib_root, paths)
    sources = _source_snapshot(paths)
    partial = Path(f"{output}.partial")
    if args.discard_partial:
        _discard_partial(partial)

    started = time.monotonic()
    connection: sqlite3.Connection | None = None
    completed: set[str]
    try:
        if os.path.lexists(partial):
            if partial.is_symlink() or partial.is_dir():
                _error(f"partial destination is not a regular database file: {partial}")
            connection = _connect_database(partial)
            completed, _imports = _validate_partial(connection, inventory, sources)
        else:
            _create_partial_database(partial)
            _check_stop()
            connection = _connect_database(partial)
            completed, _imports = _validate_partial(connection, inventory, sources)

        already_complete = len(completed)
        pending = [path for path in paths if _module_name(mathlib_root, path) not in completed]
        batches = [
            (batch_start // args.batch_size + 1, pending[batch_start:batch_start + args.batch_size])
            for batch_start in range(0, len(pending), args.batch_size)
        ]
        _emit_progress(
            event="resume",
            completed=already_complete,
            total=len(paths),
            already_complete=already_complete,
            batch=0,
            batch_modules=0,
            completed_batches=0,
            total_batches=len(batches),
            started=started,
        )
        completed_batches = 0

        def accept_batch(
            batch_number: int,
            batch_paths: list[Path],
            records: list[dict[str, Any]],
        ) -> None:
            nonlocal completed_batches
            _check_stop()
            _assert_sources_unchanged(batch_paths, sources)
            parsed = _parse_batch(records, batch_paths, mathlib_root, sources)
            _insert_batch(connection, parsed)
            completed.update(item[0] for item in parsed)
            completed_batches += 1
            _emit_progress(
                event="progress",
                completed=len(completed),
                total=len(paths),
                already_complete=already_complete,
                batch=batch_number,
                batch_modules=len(parsed),
                completed_batches=completed_batches,
                total_batches=len(batches),
                started=started,
            )

        if batches:
            _ensure_extractor()
            _run_extraction_batches(batches, args.jobs, accept_batch)

        _check_stop()
        _assert_sources_unchanged(paths, sources)
        final_completed, imports = _validate_partial(connection, inventory, sources)
        if final_completed != set(inventory):
            missing = sorted(set(inventory) - final_completed)
            _error(f"partial database is incomplete; missing modules: {', '.join(missing[:20])}")
        _validate_graph(set(inventory), imports)
        module_count, import_count, command_count = _counts(connection)
        _check_stop()
    except BaseException:
        _cancel_extractor_workers()
        raise
    finally:
        if connection is not None:
            connection.close()

    _check_stop()
    if output.exists() or os.path.lexists(output):
        if not args.overwrite:
            _error(f"destination appeared during build; refusing: {output}")
        if output.is_dir() or output.is_symlink():
            _error(f"destination became a non-file: {output}")
    _fsync_file(partial)
    _check_stop()
    os.replace(partial, output)
    _fsync_directory(output.parent)
    elapsed = round(max(0.0, time.monotonic() - started), 3)
    print(
        json.dumps(
            {
                "output": str(output),
                "modules": module_count,
                "imports": import_count,
                "commands": command_count,
                "bytes": output.stat().st_size,
                "elapsed_seconds": elapsed,
            },
            sort_keys=True,
        )
    )
    return 0


def build(args: argparse.Namespace) -> int:
    previous = _install_signal_handlers()
    try:
        return _build(args)
    finally:
        _restore_signal_handlers(previous)


def stats(args: argparse.Namespace) -> int:
    path = Path(args.database).resolve(strict=True)
    connection = _connect_database(path)
    try:
        _validate_schema(connection)
        foreign_keys = connection.execute("PRAGMA foreign_key_check").fetchall()
        if foreign_keys:
            _error(f"SQLite foreign_key_check failed: {foreign_keys}")
        integrity = connection.execute("PRAGMA integrity_check").fetchone()[0]
        if integrity != "ok":
            _error(f"SQLite integrity_check failed: {integrity}")
        modules, imports, commands = _counts(connection)
        result = {
            "database": str(path),
            "bytes": path.stat().st_size,
            "modules": modules,
            "imports": imports,
            "commands": commands,
        }
        print(json.dumps(result, sort_keys=True))
        return 0
    finally:
        connection.close()


def _positive_int(value: str) -> int:
    try:
        parsed = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("expected a positive integer") from exc
    if parsed <= 0:
        raise argparse.ArgumentTypeError("expected a positive integer")
    return parsed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="subcommand", required=True)
    build_parser = subparsers.add_parser(
        "build", help="parse pinned Lean files into a resumable database"
    )
    build_parser.add_argument("--mathlib-root", required=True, help="read-only pinned Mathlib package root")
    build_parser.add_argument("--output", required=True, help="SQLite destination path outside the package tree")
    build_parser.add_argument("--overwrite", action="store_true", help="replace an existing destination explicitly")
    build_parser.add_argument(
        "--discard-partial",
        action="store_true",
        help="discard the deterministic .partial database and restart explicitly",
    )
    build_parser.add_argument(
        "--batch-size",
        type=_positive_int,
        default=16,
        help="number of modules per extractor transaction (default: 16)",
    )
    build_parser.add_argument(
        "--jobs",
        type=_positive_int,
        default=1,
        help="number of extractor batches to run concurrently (default: 1)",
    )
    build_parser.add_argument("files", nargs="*", help="optional package-relative Mathlib.lean selectors")
    build_parser.set_defaults(function=build)
    stats_parser = subparsers.add_parser("stats", help="report counts from a T61 database")
    stats_parser.add_argument("database")
    stats_parser.set_defaults(function=stats)
    args = parser.parse_args(argv)
    try:
        return args.function(args)
    except _Interrupted as exc:
        output = getattr(args, "output", "the requested output")
        partial = f"{output}.partial" if hasattr(args, "output") else "the partial database"
        print(
            f"source-command-db: interrupted; final output was not published; "
            f"resume from {partial}",
            file=sys.stderr,
            flush=True,
        )
        return exc.exit_code
    except (OSError, RuntimeError, sqlite3.Error, subprocess.CalledProcessError) as exc:
        print(f"source-command-db: error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
