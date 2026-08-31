#!/usr/bin/env python3
"""Run bounded, lease-backed materialization work for selected modules.

The worker accepts only a closed schema-2 boundary manifest. It derives cache
identities from that manifest and the current artifact protocol, claims one
module at a time, and records each validated report or failure before moving
on. Reports and worker logs are immutable per-attempt files under the supplied
output root (which must be below ``.lake/boundary-materialization``).
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from collections.abc import Callable, Mapping, Sequence
from typing import Any

import boundary_materialize_shard as materializer
from boundary_protocol import artifact_protocol
import campaign_budget
from process_runner import run_process
from translation_index import (
    IndexError as TranslationIndexError,
    cache_key,
    claim_work,
    connect,
    import_manifest,
    order_retryable,
    plan_work,
    record_result,
)


ROOT = Path(__file__).resolve().parents[1]
MATHLIB = materializer.MATHLIB
DEFAULT_MINIMUM_FREE_BYTES = 12 * 1024**3


def storage_status(path: Path, minimum_free_bytes: int) -> dict[str, Any]:
    """Fail closed on unavailable space telemetry; never remove old evidence."""
    try:
        free = shutil.disk_usage(path).free
    except OSError as error:
        return {"canDispatch": False, "freeBytes": None,
                "minimumFreeBytes": minimum_free_bytes, "error": str(error)}
    return {"canDispatch": free >= minimum_free_bytes, "freeBytes": free,
            "minimumFreeBytes": minimum_free_bytes}


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _read_manifest(path: str | Path) -> tuple[Path, bytes, dict[str, Any], str]:
    manifest_path = Path(path).resolve()
    try:
        payload = manifest_path.read_bytes()
        value = json.loads(payload)
    except (OSError, json.JSONDecodeError) as error:
        raise TranslationIndexError(f"cannot read manifest {manifest_path}: {error}") from error
    if not isinstance(value, dict):
        raise TranslationIndexError("manifest root must be an object")
    if value.get("kind") != "simp_engine_boundary_manifest" or value.get("reportSchema") != 2:
        raise TranslationIndexError("worker requires a schema-2 boundary manifest")
    if value.get("allowUnresolved") is not False or value.get("allowDirty") is not False:
        raise TranslationIndexError(
            "worker requires allowUnresolved=false and allowDirty=false; diagnostic manifests are rejected"
        )
    if not isinstance(value.get("modules"), list):
        raise TranslationIndexError("manifest modules must be an array")
    return manifest_path, payload, value, _sha256(payload)


def _selected_modules(
    manifest: Mapping[str, Any], requested: Sequence[str] | None,
) -> tuple[list[str], int]:
    records = manifest["modules"]
    by_name: dict[str, Mapping[str, Any]] = {}
    for raw in records:
        if not isinstance(raw, dict) or not isinstance(raw.get("module"), str):
            raise TranslationIndexError("manifest contains an invalid module record")
        module = raw["module"]
        if module in by_name:
            raise TranslationIndexError(f"manifest contains duplicate module: {module}")
        by_name[module] = raw
    empty = sum(
        not any(isinstance(occurrence, dict) and occurrence.get("action") == "materialize"
                for occurrence in raw.get("occurrences", []))
        for raw in by_name.values()
    )
    if requested is None:
        return sorted(
            module for module, raw in by_name.items()
            if any(isinstance(occurrence, dict) and occurrence.get("action") == "materialize"
                   for occurrence in raw.get("occurrences", []))
        ), empty
    selected = list(requested)
    if not selected or len(set(selected)) != len(selected):
        raise TranslationIndexError("--module selections must be nonempty and unique")
    unknown = sorted(set(selected) - set(by_name))
    if unknown:
        raise TranslationIndexError(f"selected module is absent from manifest: {unknown}")
    return selected, empty


def _identities(manifest: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    implementations = manifest.get("implementationHashes")
    if not isinstance(implementations, dict) or not implementations:
        raise TranslationIndexError("manifest implementationHashes must be a nonempty object")
    repository = manifest.get("repositoryCommit")
    mathlib = manifest.get("mathlibCommit")
    lean = manifest.get("lean")
    if not all(isinstance(value, str) and value for value in (repository, mathlib)):
        raise TranslationIndexError("manifest repository and Mathlib identities are required")
    if not isinstance(lean, dict) or not all(isinstance(lean.get(key), str) and lean[key] for key in ("version", "commit")):
        raise TranslationIndexError("manifest Lean identity is incomplete")
    protocol = artifact_protocol()
    materializer_hash = _sha256(Path(materializer.__file__).read_bytes())
    worker_hash = _sha256(Path(__file__).read_bytes())
    implementation = {
        "manifestImplementationHashes": implementations,
        "materializerHash": materializer_hash,
        "workerHash": worker_hash,
        "orchestrationHashes": {
            name: _sha256((Path(__file__).resolve().parent / name).read_bytes())
            for name in ("translation_index.py", "campaign_budget.py", "process_runner.py")
        },
        "artifactProtocol": protocol,
    }
    toolchain = {
        "repositoryCommit": repository,
        "mathlibCommit": mathlib,
        "lean": lean,
        "artifactProtocol": protocol,
    }
    return implementation, toolchain


def _read_dependency_map(path: str | Path | None) -> Mapping[str, object] | None:
    if path is None:
        return None
    try:
        value = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise TranslationIndexError(f"cannot read dependency map {path}: {error}") from error
    if not isinstance(value, dict):
        raise TranslationIndexError("dependency map must be an object")
    return value


def _slug(module: str) -> str:
    value = module.removeprefix("Mathlib/").removesuffix(".lean")
    return re.sub(r"[^A-Za-z0-9._-]+", "-", value).strip(".-") or "module"


def _atomic_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    try:
        temporary.write_text(text, encoding="utf-8")
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def _report_is_verified(
    report: object, module: str, manifest_path: Path, manifest_hash: str,
) -> bool:
    """Validate report shape and require complete observed success evidence."""
    value = materializer.validate_shard_shape(report)
    if value.get("manifestPath") != str(manifest_path) or value.get("manifestHash") != manifest_hash:
        raise TranslationIndexError("materialization report is bound to another manifest")
    if value.get("manifestPolicy") != {"allowDirty": False, "allowUnresolved": False}:
        raise TranslationIndexError("materialization report is not from a closed manifest")
    if value.get("selectedModules") != [module] or value.get("compileSuccess") is not True:
        raise TranslationIndexError("materialization report does not select one successful module")
    if value.get("unobservedIds") != []:
        return False
    aggregate = value.get("aggregate")
    if not isinstance(aggregate, dict) or aggregate.get("unobservedCount") != 0:
        return False
    results = value.get("occurrenceResults")
    if not isinstance(results, list):
        raise TranslationIndexError("materialization report occurrenceResults is invalid")
    for result in results:
        if not isinstance(result, dict):
            raise TranslationIndexError("materialization report occurrence result is invalid")
        if result.get("action") == "materialize" and result.get("coveredBy") is None:
            if (result.get("classification") != "materialized"
                    or result.get("executionCount", 0) <= 0
                    or result.get("variantCount", 0) <= 0
                    or result.get("successVariantCount") != result.get("variantCount")
                    or result.get("failureVariantCount") != 0):
                return False
    return True


def invoke_materializer(
    manifest_path: Path, output_path: Path, module: str, timeout: int,
) -> tuple[int, str]:
    command = [
        sys.executable,
        str(Path(materializer.__file__).resolve()),
        "--manifest", str(manifest_path),
        "--output", str(output_path),
        "--module", module,
        "--timeout", str(timeout),
    ]
    try:
        completed = run_process(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return 124, output + "\nworker: materializer timed out\n"
    return completed.returncode, completed.stdout


def run_worker(
    database: str | Path,
    manifest: str | Path,
    output_root: str | Path,
    worker: str,
    *,
    modules: Sequence[str] | None = None,
    max_modules: int | None = None,
    module_timeout: int = 600,
    max_seconds: float | None = None,
    retry_failed: bool = False,
    dependency_map: Mapping[str, object] | None = None,
    dependency_digests: Mapping[str, str] | None = None,
    budget_guard: Callable[[], Mapping[str, Any]] = campaign_budget.check,
    minimum_free_bytes: int = DEFAULT_MINIMUM_FREE_BYTES,
) -> dict[str, Any]:
    if not worker:
        raise TranslationIndexError("worker must be nonempty")
    if module_timeout <= 0 or (max_modules is not None and max_modules <= 0):
        raise TranslationIndexError("module timeout and max modules must be positive")
    if max_seconds is not None and max_seconds <= 0:
        raise TranslationIndexError("max seconds must be positive")
    if type(minimum_free_bytes) is not int or minimum_free_bytes <= 0:
        raise TranslationIndexError("minimum free bytes must be a positive integer")
    manifest_path, manifest_bytes, manifest_value, manifest_hash = _read_manifest(manifest)
    materializer.verify_implementation_hashes(manifest_value)
    selected, skipped_empty = _selected_modules(manifest_value, modules)
    manifest_order = {
        raw["module"]: index
        for index, raw in enumerate(manifest_value["modules"])
        if isinstance(raw, dict) and isinstance(raw.get("module"), str)
    }
    output = Path(output_root).resolve()
    manifest_location = Path(manifest).absolute()
    if manifest_location.is_relative_to(output) or manifest_path.is_relative_to(output):
        raise TranslationIndexError("worker manifest must not be inside its materializer output root")
    try:
        output.relative_to(materializer.BOUNDARY_DEBUG_ROOT.resolve())
    except ValueError as error:
        raise TranslationIndexError("worker output root must be below .lake/boundary-materialization") from error
    if str(database) != ":memory:":
        database_path = Path(database)
        if database_path.absolute().is_relative_to(output) or database_path.resolve().is_relative_to(output):
            raise TranslationIndexError("worker database must not be inside its materializer cleanup root")
    output.mkdir(parents=True, exist_ok=True)
    implementation, toolchain = _identities(manifest_value)
    try:
        preflight_budget = budget_guard()
    except Exception:
        preflight_budget = {"canDispatch": False}
    preflight_denied = (not isinstance(preflight_budget, Mapping)
                        or preflight_budget.get("canDispatch") is not True)
    storage = storage_status(output, minimum_free_bytes)
    if preflight_denied or not storage["canDispatch"]:
        return {
            "manifestHash": manifest_hash, "selected": len(selected), "candidates": 0,
            "processed": 0, "succeeded": 0, "candidateReports": 0, "failures": 0,
            "skippedFailed": 0, "skippedVerified": 0,
            "skippedEmpty": skipped_empty if modules is None else 0,
            "budgetDenied": preflight_denied, "timedOut": False,
            "storageDenied": not storage["canDispatch"], "storage": storage,
        }
    materializer.corpus.assert_repository(
        str(manifest_value["repositoryCommit"]), False,
    )
    materializer.verify_environment(manifest_value, module_timeout)
    connection = connect(database)
    started = time.monotonic()
    processed = succeeded = candidates = failures = skipped_failed = candidate_reports = skipped_verified = 0
    budget_denied = timed_out = storage_denied = False
    try:
        import_manifest(
            connection, manifest_path, source_root=MATHLIB,
            dependency_map=dependency_map,
        )
        retryable: list[str] = []
        # Keep one identity/source memo for this preflight pass.  A cache key
        # walks the imported dependency graph, so adjacent selected modules
        # commonly revisit the same dependency identities.  This memo is
        # deliberately pass-scoped: a memo hit does not re-read its source;
        # each selected root is still checked by `_module_row`, and the
        # independent `plan_work` pass creates fresh memos.
        identity_memo: dict[str, str] = {}
        source_memo: dict[str, str] = {}
        for module in selected:
            key, _ = cache_key(
                connection, module, implementation, toolchain, dependency_digests,
                identity_memo=identity_memo, source_memo=source_memo,
            )
            prior = connection.execute(
                "SELECT status,translation_status FROM result_cache WHERE cache_key=?", (key,)
            ).fetchone()
            if prior is not None and not retry_failed:
                if prior[0] in {"failure", "partial"} or (
                    prior[0] == "success" and prior[1] != "verified_translated"
                ):
                    skipped_failed += 1
                    continue
            if prior is not None and prior[0] == "success" and prior[1] == "verified_translated":
                skipped_verified += 1
            else:
                retryable.append(module)
        if retry_failed:
            retryable = order_retryable(connection, retryable, manifest_order=manifest_order)
        if max_modules is not None:
            retryable = retryable[:max_modules]
        planned = plan_work(
            connection, implementation, toolchain,
            modules=retryable, dependency_digests=dependency_digests,
        )
        candidates = len(planned)
        for entry in planned:
            if entry["state"] == "succeeded":
                continue
            if max_seconds is not None and time.monotonic() - started >= max_seconds:
                timed_out = True
                break
            try:
                budget = budget_guard()
            except Exception:
                budget = {"canDispatch": False}
            if not isinstance(budget, Mapping) or budget.get("canDispatch") is not True:
                budget_denied = True
                break
            storage = storage_status(output, minimum_free_bytes)
            if not storage["canDispatch"]:
                storage_denied = True
                print(json.dumps({"event": "storage_stop", **storage}, sort_keys=True), flush=True)
                break
            leases = claim_work(
                connection, worker, limit=1,
                lease_seconds=max(float(module_timeout) + 120.0, 900.0),
                modules=[entry["module"]],
            )
            if not leases:
                continue
            lease = leases[0]
            print(json.dumps({
                "event": "module_start", "module": lease.module,
                "attemptId": lease.attempt_id,
            }, sort_keys=True), flush=True)
            report_path = output / f"{_slug(lease.module)}-{lease.attempt_id}.json"
            log_path = output / f"{_slug(lease.module)}-{lease.attempt_id}.log"
            code, command_output = invoke_materializer(
                manifest_path, report_path, lease.module, module_timeout,
            )
            _atomic_text(log_path, command_output)
            processed += 1
            if code != 0:
                timed_out = timed_out or code == 124
                failures += 1
                record_result(
                    connection, lease.module, implementation, toolchain,
                    status="failure", result=None, failure=f"materializer exit {code}",
                    log_ref=str(log_path), artifact_ref=str(report_path) if report_path.is_file() else None,
                    attempt_id=lease.attempt_id, worker=worker,
                    dependency_digests=dependency_digests,
                )
                print(json.dumps({"event": "module_failure", "module": lease.module,
                                  "exitCode": code, "log": str(log_path)}, sort_keys=True), flush=True)
                continue
            try:
                report = json.loads(report_path.read_text(encoding="utf-8"))
                verified = _report_is_verified(report, lease.module, manifest_path, manifest_hash)
            except (OSError, json.JSONDecodeError, TranslationIndexError, RuntimeError) as error:
                failures += 1
                record_result(
                    connection, lease.module, implementation, toolchain,
                    status="failure", result=None, failure=str(error),
                    log_ref=str(log_path), artifact_ref=str(report_path) if report_path.is_file() else None,
                    attempt_id=lease.attempt_id, worker=worker,
                    dependency_digests=dependency_digests,
                )
                print(json.dumps({"event": "module_invalid_report", "module": lease.module,
                                  "detail": str(error), "log": str(log_path)}, sort_keys=True), flush=True)
                continue
            record_result(
                connection, lease.module, implementation, toolchain,
                status="success", result=report, translated=True, verified=verified,
                log_ref=str(log_path), artifact_ref=str(report_path),
                attempt_id=lease.attempt_id, worker=worker,
                dependency_digests=dependency_digests,
            )
            if verified:
                succeeded += 1
            else:
                candidate_reports += 1
            print(json.dumps({"event": "module_result", "module": lease.module,
                              "verified": verified, "report": str(report_path)}, sort_keys=True), flush=True)
    finally:
        connection.close()
    return {
        "manifestHash": manifest_hash,
        "selected": len(selected),
        "candidates": candidates,
        "processed": processed,
        "succeeded": succeeded,
        "candidateReports": candidate_reports,
        "failures": failures,
        "skippedFailed": skipped_failed,
        "skippedVerified": skipped_verified,
        "skippedEmpty": skipped_empty if modules is None else 0,
        "budgetDenied": budget_denied,
        "timedOut": timed_out,
        "storageDenied": storage_denied,
        "storage": storage,
    }


def _json_map(path: str | None) -> Mapping[str, str] | None:
    if path is None:
        return None
    try:
        value = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise TranslationIndexError(f"cannot read JSON map {path}: {error}") from error
    if not isinstance(value, dict) or not all(isinstance(key, str) and isinstance(item, str) for key, item in value.items()):
        raise TranslationIndexError("dependency digests must be a string map")
    return value


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--output-root", required=True)
    parser.add_argument("--worker", required=True)
    parser.add_argument("--module", action="append")
    parser.add_argument("--max-modules", type=int)
    parser.add_argument("--module-timeout", type=int, default=600)
    parser.add_argument("--max-seconds", type=float)
    parser.add_argument("--retry-failed", action="store_true")
    parser.add_argument("--dependency-map")
    parser.add_argument("--dependency-digests")
    parser.add_argument("--minimum-free-bytes", type=int, default=DEFAULT_MINIMUM_FREE_BYTES,
                        help="Pause before claiming another module below this free-space reserve (default: 12 GiB).")
    args = parser.parse_args(argv)
    try:
        result = run_worker(
            args.database, args.manifest, args.output_root, args.worker,
            modules=args.module, max_modules=args.max_modules,
            module_timeout=args.module_timeout, max_seconds=args.max_seconds,
            retry_failed=args.retry_failed,
            dependency_map=_read_dependency_map(args.dependency_map),
            dependency_digests=_json_map(args.dependency_digests),
            minimum_free_bytes=args.minimum_free_bytes,
        )
    except (TranslationIndexError, RuntimeError, OSError, ValueError) as error:
        print(f"campaign-worker: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
