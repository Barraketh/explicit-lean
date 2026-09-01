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
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from collections.abc import Callable, Mapping, Sequence
from typing import Any

import boundary_materialize_shard as materializer
import manual_overlay
from boundary_protocol import artifact_protocol
import campaign_budget
from process_runner import run_process
from translation_index import (
    IndexError as TranslationIndexError,
    cache_key,
    claim_work,
    connect,
    abandon_lease,
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


def _identities(
    manifest: Mapping[str, Any], overlay_identity: Mapping[str, object] | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
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
        # The overlay is deliberately a global implementation salt.  It
        # invalidates more modules than strictly necessary when the tiny
        # exceptional table changes, but can never reuse a result produced by
        # different replacement bytes.
        "manualOverlay": dict(overlay_identity) if overlay_identity is not None else None,
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
    temporary = path.with_name(path.name + f".tmp-{os.getpid()}-{time.time_ns()}")
    try:
        temporary.write_text(text, encoding="utf-8")
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def _cleanup_stale_atomic_temps(root: Path) -> None:
    """Remove worker temporaries whose owning local process no longer exists."""
    pattern = re.compile(r"\.tmp-([1-9][0-9]*)-[0-9]+$")
    for path in root.glob("*.tmp-*"):
        match = pattern.search(path.name)
        if match is None:
            continue
        owner = int(match.group(1))
        try:
            os.kill(owner, 0)
        except ProcessLookupError:
            path.unlink(missing_ok=True)
        except PermissionError:
            # Another user's live process is not ours to disturb.
            continue


def _write_manifest_capsule(
    manifest_path: Path,
    manifest_bytes: bytes,
    manifest: Mapping[str, Any],
    selected: Sequence[materializer.SelectedModule],
    output: Path,
    *,
    overlay: manual_overlay.Overlay | None = None,
) -> tuple[Path, str]:
    """Publish a compact immutable projection outside per-run cleanup."""
    manual_modules = tuple(sorted(overlay.modules)) if overlay is not None else ()
    capsule = materializer.make_manifest_capsule(
        manifest_path, manifest_bytes, manifest, selected,
        overlay_identity=overlay.identity() if overlay is not None else None,
        manual_modules=manual_modules,
    )
    payload = json.dumps(capsule, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()
    boundary_root = materializer.BOUNDARY_DEBUG_ROOT.resolve()
    root = materializer.BOUNDARY_DEBUG_ROOT / "capsules"
    if root.exists() and root.is_symlink():
        raise TranslationIndexError("manifest capsule directory must not be a symlink")
    if root.exists() and not root.is_dir():
        raise TranslationIndexError("manifest capsule directory is not a directory")
    try:
        root.parent.resolve().relative_to(boundary_root)
    except ValueError as error:
        raise TranslationIndexError("manifest capsule directory escapes boundary root") from error
    path = root / f"{manifest_path.stem}-{_sha256(manifest_bytes)[:24]}-{_sha256(payload)[:24]}.json"
    root.mkdir(parents=True, exist_ok=True)
    if path.is_symlink():
        raise TranslationIndexError("manifest capsule file must not be a symlink")
    temporary = path.with_name(path.name + f".tmp-{os.getpid()}-{time.time_ns()}")
    try:
        temporary.write_bytes(payload)
        try:
            # ``link`` publishes without replacing an existing capsule.  Two
            # workers may therefore safely converge on the same immutable file.
            os.link(temporary, path)
        except FileExistsError:
            pass
        if path.is_symlink():
            raise TranslationIndexError("manifest capsule file must not be a symlink")
        if path.read_bytes() != payload:
            raise TranslationIndexError(f"manifest capsule path collision: {path}")
    finally:
        temporary.unlink(missing_ok=True)
    return path, _sha256(payload)


def _selected_for_report_evidence(
    manifest: dict[str, Any],
    module: str,
    overlay: manual_overlay.Overlay | None,
    debug_root: Path,
    validated_selection: Mapping[str, materializer.SelectedModule] | None = None,
) -> list[materializer.SelectedModule]:
    """Reconstruct a report's immutable selection without changing evidence.

    The producer freshly classifies an overlaid source before recording it.
    The consumer starts from the closed canonical manifest and applies the
    authenticated coordinate shift.  It deliberately does not call
    ``prepare_overlay_selection`` here because that producer helper writes the
    effective source into the run directory before verification.
    """
    if validated_selection is None:
        canonical = materializer.validate_manifest_selection(
            manifest, [module], expect_total=None, expect_materialize=None
        )
    else:
        canonical = [validated_selection[module]] if module in validated_selection else []
    if len(canonical) != 1:
        raise TranslationIndexError(
            f"closed manifest did not select exactly one module: {module}"
        )
    selected = canonical[0]
    if overlay is None or not overlay.entries_by_module().get(module):
        return [selected]

    effective_source = overlay.apply(module, selected.source)
    shifted = tuple(
        materializer._validate_occurrence(module, effective_source, dict(raw))
        for raw in overlay.shifted_occurrences(module)
    )
    reusable = [
        str(item["id"])
        for item in shifted
        if item["executionRole"] == "reusable_executable"
    ]
    if reusable:
        raise TranslationIndexError(
            f"overlaid report contains unsupported reusable occurrences: {module}: {reusable}"
        )
    unresolved = [str(item["id"]) for item in shifted if item["action"] == "unresolved"]
    if unresolved:
        raise TranslationIndexError(
            f"overlaid report contains unresolved occurrences: {module}: {unresolved}"
        )
    effective_path = (
        debug_root / "manual-overlay-input" / Path(*module.split("/"))
    ).resolve()
    return [materializer.SelectedModule(
        module=module,
        compiled_module=selected.compiled_module,
        source_path=effective_path,
        source=effective_source,
        occurrences=shifted,
        materialize=tuple(item for item in shifted if item["action"] == "materialize"),
        retain=tuple(item for item in shifted if item["action"] == "retain"),
    )]


def _report_is_verified(
    report: object,
    module: str,
    manifest_path: Path,
    manifest_bytes: bytes,
    manifest: dict[str, Any],
    report_path: Path,
    overlay: manual_overlay.Overlay | None = None,
    timeout: int = 600,
    validated_selection: Mapping[str, materializer.SelectedModule] | None = None,
) -> bool:
    """Reproduce all durable evidence, then require observed success."""
    value = materializer.validate_shard_shape(report)
    manifest_hash = hashlib.sha256(manifest_bytes).hexdigest()
    if value.get("manifestPath") != str(manifest_path) or value.get("manifestHash") != manifest_hash:
        raise TranslationIndexError("materialization report is bound to another manifest")
    if value.get("manifestPolicy") != {"allowDirty": False, "allowUnresolved": False}:
        raise TranslationIndexError("materialization report is not from a closed manifest")
    if value.get("selectedModules") != [module] or value.get("compileSuccess") is not True:
        raise TranslationIndexError("materialization report does not select one successful module")
    expected_overlay = overlay.identity() if overlay is not None else None
    if value.get("manualOverlay") != expected_overlay:
        raise TranslationIndexError("materialization report is bound to another manual overlay")
    debug_root = materializer.debug_root_for(report_path.resolve())
    selected = _selected_for_report_evidence(
        manifest, module, overlay, debug_root, validated_selection
    )
    materializer.verify_shard_evidence(
        value,
        manifest=manifest,
        manifest_path=manifest_path,
        manifest_bytes=manifest_bytes,
        selected=selected,
        debug_root=debug_root,
        timeout=timeout,
        overlay=overlay,
    )
    if overlay is not None:
        modules = value.get("modules")
        if not isinstance(modules, list) or len(modules) != 1 or not isinstance(modules[0], dict):
            raise TranslationIndexError("manual overlay report has invalid module evidence")
        materializer.verify_manual_overlay_evidence(
            modules[0], overlay, module, timeout, debug_root=debug_root
        )
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
    manual_overrides: Path | None = None,
    capsule: Path | None = None,
    capsule_hash: str | None = None,
) -> tuple[int, str]:
    command = [
        sys.executable,
        str(Path(materializer.__file__).resolve()),
        "--manifest", str(manifest_path),
        "--output", str(output_path),
        "--module", module,
        "--timeout", str(timeout),
    ]
    if manual_overrides is not None:
        command.extend(("--manual-overrides", str(manual_overrides)))
    if capsule is not None:
        command.extend(("--capsule", str(capsule)))
        if capsule_hash is None:
            raise TranslationIndexError("capsule hash is required")
        command.extend(("--capsule-sha256", capsule_hash))
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
    manual_overrides: str | Path | None = None,
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
    # A producer worker is the one place that pays for complete manifest
    # validation.  Reports below reuse these checked selections; they never
    # independently walk the 205MiB global occurrence array.
    validated_selection: dict[str, materializer.SelectedModule] | None = None
    complete_manifest = all(
        key in manifest_value
        for key in ("countsByExecutionRole", "countsByDeclarationKind", "countsByAction")
    )
    if complete_manifest:
        by_name = {
            str(raw["module"]): raw for raw in manifest_value["modules"]
            if isinstance(raw, Mapping) and isinstance(raw.get("module"), str)
        }
        capsule_candidates = [
            module for module in selected
            if not any(
                isinstance(item, Mapping)
                and item.get("executionRole") == "reusable_executable"
                for item in by_name[module].get("occurrences", [])
            )
        ]
        validated = materializer.validate_manifest_selection(
            manifest_value, capsule_candidates,
            expect_total=None, expect_materialize=None,
        ) if capsule_candidates else []
        validated_selection = {item.module: item for item in validated}
    overlay = None
    if manual_overrides is not None:
        module_records = {
            str(raw["module"]): raw
            for raw in manifest_value["modules"]
            if isinstance(raw, Mapping) and isinstance(raw.get("module"), str)
        }
        if complete_manifest:
            overlay = manual_overlay._load_overlay_projected(
                manifest_path, Path(manual_overrides), source_root=MATHLIB,
                manifest_value=manifest_value, manifest_bytes=manifest_bytes,
                module_records=module_records,
            )
        else:
            overlay = manual_overlay.load_overlay(
                manifest_path, Path(manual_overrides), source_root=MATHLIB,
            )
    overlay_identity = overlay.identity() if overlay is not None else None
    manifest_order = {
        raw["module"]: index
        for index, raw in enumerate(manifest_value["modules"])
        if isinstance(raw, dict) and isinstance(raw.get("module"), str)
    }
    output = Path(output_root).resolve()
    manifest_location = Path(manifest).absolute()
    if manifest_location.is_relative_to(output) or manifest_path.is_relative_to(output):
        raise TranslationIndexError("worker manifest must not be inside its materializer output root")
    if manual_overrides is not None:
        manual_location = Path(manual_overrides).absolute()
        manual_path = Path(manual_overrides).resolve()
        if manual_location.is_relative_to(output) or manual_path.is_relative_to(output):
            raise TranslationIndexError(
                "manual override database must not be inside its materializer output root"
            )
    try:
        output.relative_to(materializer.BOUNDARY_DEBUG_ROOT.resolve())
    except ValueError as error:
        raise TranslationIndexError("worker output root must be below .lake/boundary-materialization") from error
    if str(database) != ":memory:":
        database_path = Path(database)
        if database_path.absolute().is_relative_to(output) or database_path.resolve().is_relative_to(output):
            raise TranslationIndexError("worker database must not be inside its materializer cleanup root")
    output.mkdir(parents=True, exist_ok=True)
    _cleanup_stale_atomic_temps(output)
    capsules: dict[str, tuple[Path, str]] = {}
    if validated_selection:
        shared_capsule = _write_manifest_capsule(
            manifest_path, manifest_bytes, manifest_value,
            list(validated_selection.values()), output, overlay=overlay,
        )
        capsules = {item.module: shared_capsule for item in validated_selection.values()}
    implementation, toolchain = _identities(manifest_value, overlay_identity)
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
    active_lease = None
    try:
        import_manifest(
            connection, manifest_path, source_root=MATHLIB,
            dependency_map=dependency_map,
        )
        retryable: list[str] = []
        current_cache_keys: dict[str, str] = {}
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
            current_cache_keys[module] = key
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
            retryable = order_retryable(
                connection, retryable, manifest_order=manifest_order,
                cache_keys=current_cache_keys,
            )
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
            active_lease = lease
            capsule = capsules.get(lease.module)
            if capsule is not None:
                try:
                    current_capsule_hash = _sha256(capsule[0].read_bytes())
                except OSError as error:
                    raise TranslationIndexError(f"cannot reread manifest capsule: {error}") from error
                if current_capsule_hash != capsule[1]:
                    raise TranslationIndexError("manifest capsule changed before child dispatch")
            print(json.dumps({
                "event": "module_start", "module": lease.module,
                "attemptId": lease.attempt_id,
            }, sort_keys=True), flush=True)
            report_path = output / f"{_slug(lease.module)}-{lease.attempt_id}.json"
            log_path = output / f"{_slug(lease.module)}-{lease.attempt_id}.log"
            if manual_overrides is None:
                if capsule is None:
                    code, command_output = invoke_materializer(
                        manifest_path, report_path, lease.module, module_timeout
                    )
                else:
                    code, command_output = invoke_materializer(
                        manifest_path, report_path, lease.module, module_timeout,
                        capsule=capsule[0], capsule_hash=capsule[1],
                    )
            else:
                if capsule is None:
                    code, command_output = invoke_materializer(
                        manifest_path, report_path, lease.module, module_timeout,
                        Path(manual_overrides).resolve(),
                    )
                else:
                    code, command_output = invoke_materializer(
                        manifest_path, report_path, lease.module, module_timeout,
                        Path(manual_overrides).resolve(),
                        capsule=capsule[0], capsule_hash=capsule[1],
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
                active_lease = None
                continue
            try:
                report = json.loads(report_path.read_text(encoding="utf-8"))
                verified = _report_is_verified(
                    report,
                    lease.module,
                    manifest_path,
                    manifest_bytes,
                    manifest_value,
                    report_path,
                    overlay,
                    module_timeout,
                    validated_selection=validated_selection,
                )
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
                active_lease = None
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
            active_lease = None
    except BaseException as error:
        if active_lease is not None:
            try:
                abandon_lease(
                    connection, active_lease.attempt_id, worker,
                    f"worker interrupted: {type(error).__name__}: {error}",
                )
            except BaseException:
                pass
        raise
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
    parser.add_argument(
        "--manual-overrides",
        default=str(manual_overlay.DEFAULT_DATABASE),
        help="authenticated manual override DB (pass an empty string to disable)",
    )
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
            manual_overrides=args.manual_overrides or None,
            minimum_free_bytes=args.minimum_free_bytes,
        )
    except (TranslationIndexError, RuntimeError, OSError, ValueError) as error:
        print(f"campaign-worker: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
