#!/usr/bin/env python3
"""Bootstrap and run the schema-13 v10 direct materialization campaign.

The v10 boundary is deliberately explicit: a clean v10 manifest is
authenticated and imported into the existing v9 index before queue planning.
Cache identity is recomputed from that v10 manifest's implementation and
toolchain identities, and every reusable row is checked against those exact
values before dispatch.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import dataclass
import fcntl
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import sys
import time
import uuid
from collections.abc import Mapping, Sequence
from functools import lru_cache

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "Experiment"))

import boundary_materialize_shard as materializer
import campaign_budget
import campaign_worker
from translation_index import IndexError as TranslationIndexError
from translation_index import connect, import_manifest, plan_work


V10_MANIFEST_LABEL = "schema13-isolated-closed-manifest-v10.json"
V10_WORKER_LABEL = "schema13-v10-direct-closure"
V10_LOCK_LABEL = "schema13-v10-supervisor.lock"
RESOURCE_FAILURE = "materializer stopped by memory guard (exit 125)"
DEFAULT_MINIMUM_FREE_BYTES = 12 * 1024**3


@dataclass(frozen=True)
class SupervisorConfig:
    database: Path
    manifest: Path
    dependency_map: Path | None
    source_root: Path
    output_parent: Path
    lock_path: Path
    expected_v9_manifest_hash: str
    expected_v10_manifest_hash: str
    expected_modules: int
    expected_occurrences: int
    run_id: str
    minimum_free_bytes: int = DEFAULT_MINIMUM_FREE_BYTES
    module_timeout: int = 900
    max_passes: int = 1000
    max_seconds: float = 21600.0
    start_pass: int = 1


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _hash_argument(value: str, label: str) -> str:
    if len(value) != 64 or any(character not in "0123456789abcdef" for character in value):
        raise TranslationIndexError(f"{label} must be a lowercase SHA-256 digest")
    return value


def _safe_label(value: str, label: str) -> str:
    if not value or value in {".", ".."} or any(character not in "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789._-" for character in value):
        raise TranslationIndexError(f"{label} contains an unsafe path label")
    return value


def v10_identity(manifest_value: Mapping[str, object], manifest_hash: str) -> tuple[dict[str, object], dict[str, object]]:
    """Return the ordinary worker identities, checked against this v10 hash."""
    _hash_argument(manifest_hash, "v10 manifest hash")
    implementation, toolchain = campaign_worker._identities(manifest_value)
    # The manifest path/hash is checked independently by bootstrap. Keeping
    # the worker's c328 identity contract unchanged avoids changing historical
    # cache semantics; the exact v10 toolchain object is still checked below.
    if not isinstance(toolchain.get("repositoryCommit"), str):
        raise TranslationIndexError("v10 toolchain identity omitted repositoryCommit")
    return implementation, toolchain


def authenticate_v10_manifest(config: SupervisorConfig) -> tuple[Path, bytes, dict[str, object], str]:
    """Authenticate the fresh closed manifest before any index planning."""
    manifest_path, payload, value, actual_hash = campaign_worker._read_manifest(config.manifest)
    if manifest_path.name != V10_MANIFEST_LABEL:
        raise TranslationIndexError(
            f"v10 manifest must use fresh label {V10_MANIFEST_LABEL}: {manifest_path.name}"
        )
    if actual_hash != _hash_argument(config.expected_v10_manifest_hash, "v10 manifest hash"):
        raise TranslationIndexError(
            f"v10 manifest hash changed: {actual_hash} != {config.expected_v10_manifest_hash}"
        )
    # This checks the current implementation source set before the expensive
    # source/occurrence join in import_manifest.
    materializer.verify_implementation_hashes(value)
    return manifest_path, payload, value, actual_hash


def _current_manifest_rows(connection: sqlite3.Connection) -> list[tuple[str, int]]:
    return [
        (str(row[0]), int(row[1]))
        for row in connection.execute(
            "SELECT manifest_hash,COUNT(*) FROM modules GROUP BY manifest_hash ORDER BY manifest_hash"
        )
    ]


def verify_v9_index(connection: sqlite3.Connection, config: SupervisorConfig) -> None:
    expected = _hash_argument(config.expected_v9_manifest_hash, "v9 manifest hash")
    rows = _current_manifest_rows(connection)
    if rows != [(expected, config.expected_modules)]:
        raise TranslationIndexError(f"index is not the expected v9 current index: {rows}")
    record = connection.execute(
        "SELECT path,schema_version,diagnostic FROM manifests WHERE manifest_hash=?",
        (expected,),
    ).fetchone()
    if record is None or int(record[1]) != 2 or int(record[2]) != 0:
        raise TranslationIndexError("expected authenticated v9 manifest record is missing")


def verify_v10_index(
    connection: sqlite3.Connection,
    config: SupervisorConfig,
    manifest_path: Path,
    manifest_hash: str,
    manifest_value: Mapping[str, object],
) -> None:
    rows = _current_manifest_rows(connection)
    if rows != [(manifest_hash, config.expected_modules)]:
        raise TranslationIndexError(f"index is not exact v10 after bootstrap: {rows}")
    occurrences = connection.execute("SELECT COUNT(*) FROM occurrences").fetchone()[0]
    if int(occurrences) != config.expected_occurrences:
        raise TranslationIndexError(
            f"v10 occurrence count changed: {occurrences} != {config.expected_occurrences}"
        )
    record = connection.execute(
        "SELECT path,schema_version,diagnostic FROM manifests WHERE manifest_hash=?",
        (manifest_hash,),
    ).fetchone()
    expected_record = (str(manifest_path.resolve()), 2, 0)
    if record is None or tuple(record) != expected_record:
        raise TranslationIndexError(f"v10 manifest record changed: {record!r}")
    if manifest_value.get("moduleFileCount") != config.expected_modules:
        raise TranslationIndexError("v10 moduleFileCount disagrees with configured identity")
    if manifest_value.get("occurrenceCount") != config.expected_occurrences:
        raise TranslationIndexError("v10 occurrenceCount disagrees with configured identity")


def bootstrap_index(config: SupervisorConfig) -> tuple[Path, bytes, dict[str, object], str]:
    """Verify v9, then authenticate and import v10 as one ordered operation."""
    manifest_path, payload, manifest_value, manifest_hash = authenticate_v10_manifest(config)
    dependency_map = None
    if config.dependency_map is not None:
        try:
            dependency_map = json.loads(config.dependency_map.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise TranslationIndexError(f"cannot read v10 dependency map: {error}") from error
        if not isinstance(dependency_map, dict):
            raise TranslationIndexError("v10 dependency map must be an object")
    connection = connect(config.database)
    try:
        verify_v9_index(connection, config)
        imported = import_manifest(
            connection,
            manifest_path,
            source_root=config.source_root,
            dependency_map=dependency_map,
        )
        if imported != {
            "manifestHash": manifest_hash,
            "modules": config.expected_modules,
            "occurrences": config.expected_occurrences,
            "diagnostic": False,
            "unresolved": 0,
        }:
            raise TranslationIndexError(f"v10 import result is not exact: {imported}")
        verify_v10_index(connection, config, manifest_path, manifest_hash, manifest_value)
    finally:
        connection.close()
    return manifest_path, payload, manifest_value, manifest_hash


def ordered_modules(
    config: SupervisorConfig,
    manifest_value: Mapping[str, object],
    manifest_hash: str,
) -> tuple[list[str], int]:
    """Plan with the v10 identity, then return closure ordered retry work."""
    implementation, toolchain = v10_identity(manifest_value, manifest_hash)
    connection = connect(config.database)
    try:
        verify_v10_index(connection, config, config.manifest.resolve(), manifest_hash, manifest_value)
        modules = {
            str(row[0]) for row in connection.execute("SELECT module FROM modules")
        }
        dependencies = {module: [] for module in modules}
        for row in connection.execute("SELECT module,dependency FROM imports"):
            if row[1] in modules:
                dependencies[row[0]].append(row[1])
        eligible = [
            str(row[0])
            for row in connection.execute(
                "SELECT module FROM occurrences GROUP BY module "
                "HAVING SUM(action='materialize') > 0 "
                "AND SUM(execution_role='reusable_executable') = 0"
            )
        ]
        planned = plan_work(connection, implementation, toolchain, modules=eligible)
        expected_keys = {entry["module"]: entry["cacheKey"] for entry in planned}
        queue_keys = {
            str(row[0]): str(row[1])
            for row in connection.execute("SELECT module,cache_key FROM work_queue")
            if row[0] in expected_keys
        }
        if queue_keys != expected_keys:
            raise TranslationIndexError("v10 queue cache identity does not match the planned identity")
        implementation_json = json.dumps(implementation, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        toolchain_json = json.dumps(toolchain, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        for row in connection.execute(
            "SELECT cache_key,implementation_identity,toolchain_identity,status,result_json "
            "FROM result_cache WHERE cache_key IN (%s)" % ",".join("?" * len(expected_keys)),
            tuple(expected_keys.values()),
        ) if expected_keys else ():
            if row[1] != implementation_json or row[2] != toolchain_json:
                raise TranslationIndexError("v10 cache row has a mismatched implementation/toolchain identity")
            if row[3] == "success":
                try:
                    report = json.loads(row[4])
                except json.JSONDecodeError as error:
                    raise TranslationIndexError("v10 cache report is not JSON") from error
                if not isinstance(report, dict) or report.get("manifestHash") != manifest_hash:
                    raise TranslationIndexError("v10 cache report is bound to a different manifest")
    finally:
        connection.close()

    visiting: set[str] = set()

    @lru_cache(None)
    def closure(module: str) -> frozenset[str]:
        if module in visiting:
            raise TranslationIndexError(f"import cycle at {module}")
        visiting.add(module)
        result = {module}
        for dependency in dependencies[module]:
            result.update(closure(dependency))
        visiting.remove(module)
        return frozenset(result)

    resource_deferred = set()
    connection = connect(config.database)
    try:
        resource_deferred = {
            str(row[0])
            for row in connection.execute(
                "SELECT w.module FROM work_queue w JOIN attempts a "
                "ON a.attempt_id=w.last_attempt_id WHERE w.state='queued' "
                "AND a.status='abandoned' AND a.cache_key=w.cache_key AND a.failure=?",
                (RESOURCE_FAILURE,),
            )
        }
    finally:
        connection.close()
    eligible.sort(key=lambda module: (module in resource_deferred, len(closure(module)), module))
    return eligible, len(resource_deferred)


@contextmanager
def supervisor_lock(path: Path, run_id: str, manifest_hash: str):
    path = path.resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
    try:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError(f"another v10 supervisor holds {path}") from error
        os.ftruncate(descriptor, 0)
        os.write(descriptor, f"schema={V10_WORKER_LABEL}\nrun={run_id}\nmanifest={manifest_hash}\npid={os.getpid()}\n".encode())
        yield
    finally:
        os.close(descriptor)


def fresh_paths(config: SupervisorConfig, pass_number: int) -> tuple[str, Path]:
    nonce = f"{time.time_ns()}-{uuid.uuid4().hex}"
    worker = f"{V10_WORKER_LABEL}-{_safe_label(config.run_id, 'run id')}-pass-{pass_number}-{nonce}"
    output = config.output_parent / worker
    try:
        output.mkdir(parents=True, exist_ok=False)
    except FileExistsError as error:
        raise RuntimeError(f"refusing existing immutable v10 output root: {output}") from error
    return worker, output


def run_supervisor(config: SupervisorConfig) -> int:
    if config.start_pass <= 0 or config.max_passes <= 0 or config.max_seconds <= 0:
        raise TranslationIndexError("pass counts and max-seconds must be positive")
    if config.expected_modules <= 0 or config.expected_occurrences < 0:
        raise TranslationIndexError("v10 manifest counts are invalid")
    _safe_label(config.run_id, "run id")
    output_parent = config.output_parent.resolve()
    try:
        output_parent.relative_to(materializer.BOUNDARY_DEBUG_ROOT.resolve())
    except ValueError as error:
        raise TranslationIndexError("v10 output parent must be below .lake/boundary-materialization") from error
    _, _, manifest_value, manifest_hash = bootstrap_index(config)
    dependency_map = None
    if config.dependency_map is not None:
        dependency_map = json.loads(config.dependency_map.read_text(encoding="utf-8"))
    started = time.monotonic()
    pass_number = config.start_pass
    completed_passes = 0
    while completed_passes < config.max_passes and time.monotonic() - started < config.max_seconds:
        budget = campaign_budget.check()
        if budget.get("canDispatch") is not True:
            print(json.dumps({"event": "v10_budget_stop", "budget": budget}, sort_keys=True), flush=True)
            return 0
        memory = campaign_worker.memory_status()
        storage = campaign_worker.storage_status(config.output_parent, config.minimum_free_bytes)
        if not memory["canDispatch"]:
            print(json.dumps({"event": "v10_memory_wait", **memory}, sort_keys=True), flush=True)
            time.sleep(min(30.0, max(0.0, config.max_seconds - (time.monotonic() - started))))
            continue
        if not storage["canDispatch"]:
            print(json.dumps({"event": "v10_storage_stop", **storage}, sort_keys=True), flush=True)
            return 0
        worker, output = fresh_paths(config, pass_number)
        modules, deferred = ordered_modules(config, manifest_value, manifest_hash)
        print(json.dumps({
            "event": "v10_pass_start", "pass": pass_number, "worker": worker,
            "eligible": len(modules), "resourceDeferred": deferred,
            "availableBytes": memory.get("availableBytes"), "freeBytes": storage.get("freeBytes"),
        }, sort_keys=True), flush=True)
        remaining = config.max_seconds - (time.monotonic() - started)
        if remaining <= 0:
            break
        result = campaign_worker.run_worker(
            config.database,
            config.manifest,
            output,
            worker,
            modules=modules,
            retry_failed=True,
            module_timeout=config.module_timeout,
            max_seconds=min(21600.0, remaining),
            dependency_map=dependency_map,
            minimum_free_bytes=config.minimum_free_bytes,
        )
        print(json.dumps({"event": "v10_pass_result", "pass": pass_number, **result}, sort_keys=True), flush=True)
        completed_passes += 1
        pass_number += 1
        if result.get("budgetDenied") or result.get("storageDenied") or result.get("timedOut"):
            return 0
        if not result.get("resourceStopped") and not result.get("memoryDenied"):
            return 0
    print(json.dumps({
        "event": "v10_limit_stop", "completedPasses": completed_passes,
        "nextPass": pass_number, "elapsedSeconds": time.monotonic() - started,
    }, sort_keys=True), flush=True)
    return 0


def _config_from_args(args: argparse.Namespace) -> SupervisorConfig:
    return SupervisorConfig(
        database=Path(args.database).resolve(),
        manifest=Path(args.manifest).resolve(),
        dependency_map=Path(args.dependency_map).resolve() if args.dependency_map else None,
        source_root=Path(args.source_root).resolve(),
        output_parent=Path(args.output_parent).resolve(),
        lock_path=Path(args.lock_path).resolve(),
        expected_v9_manifest_hash=_hash_argument(args.v9_manifest_sha256, "v9 manifest hash"),
        expected_v10_manifest_hash=_hash_argument(args.v10_manifest_sha256, "v10 manifest hash"),
        expected_modules=args.modules,
        expected_occurrences=args.occurrences,
        run_id=_safe_label(args.run_id, "run id"),
        minimum_free_bytes=args.minimum_free_bytes,
        module_timeout=args.module_timeout,
        max_passes=args.max_passes,
        max_seconds=args.max_seconds,
        start_pass=args.start_pass,
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--source-root", required=True)
    parser.add_argument("--output-parent", required=True)
    parser.add_argument("--lock-path", default=str(ROOT / ".lake" / V10_LOCK_LABEL))
    parser.add_argument("--dependency-map")
    parser.add_argument("--v9-manifest-sha256", required=True)
    parser.add_argument("--v10-manifest-sha256", required=True)
    parser.add_argument("--modules", type=int, required=True)
    parser.add_argument("--occurrences", type=int, required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--minimum-free-bytes", type=int, default=DEFAULT_MINIMUM_FREE_BYTES)
    parser.add_argument("--module-timeout", type=int, default=900)
    parser.add_argument("--max-passes", type=int, default=1000)
    parser.add_argument("--max-seconds", type=float, default=21600.0)
    parser.add_argument("--start-pass", type=int, required=True)
    args = parser.parse_args(argv)
    config = _config_from_args(args)
    # The lock is acquired only after static v10 authentication has enough
    # information to write an auditable owner record.
    manifest_hash = sha256(config.manifest.read_bytes())
    with supervisor_lock(config.lock_path, config.run_id, manifest_hash):
        return run_supervisor(config)


if __name__ == "__main__":
    raise SystemExit(main())
