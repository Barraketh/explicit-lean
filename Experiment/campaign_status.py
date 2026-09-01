#!/usr/bin/env python3
"""Read identity-aware campaign status without invoking Lean or changing state.

Status is meaningful only relative to a complete, closed schema-2 manifest.
When no manifest is supplied, the newest manifest payload stored in the index is
used. Cache keys are recomputed with :func:`translation_index.cache_key`, the
same function used by the worker, so old successful rows remain visible as
historical evidence without being counted as current coverage.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import sqlite3
import sys
from urllib.parse import quote
from typing import Any, Mapping

import campaign_worker
import manual_overlay
from boundary_materialize_shard import REPORT_SCHEMA
from translation_index import (
    IndexError as TranslationIndexError,
    _source_root,
    _validated_modules,
    cache_key,
    canonical,
    sha256_bytes,
)

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DATABASE = ROOT / ".lake/search-free-mathlib/translation-index.sqlite3"
DEFAULT_MINIMUM_FREE_BYTES = 12 * 1024**3


class StatusError(RuntimeError):
    """The requested current identity cannot be established safely."""


def _read_json_map(path: Path | None) -> Mapping[str, str] | None:
    if path is None:
        return None
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise StatusError(f"cannot read dependency digests {path}: {error}") from error
    if not isinstance(value, dict) or not all(
        isinstance(key, str) and isinstance(item, str) for key, item in value.items()
    ):
        raise StatusError("dependency digests must be a JSON object mapping module paths to strings")
    return value


def _complete_manifest(
    path: Path,
    payload: bytes,
    value: object,
    connection: sqlite3.Connection,
    source_root: Path | None,
) -> tuple[dict[str, Any], list[dict[str, Any]], str, Path]:
    """Validate all manifest joins needed to derive current cache identities."""
    if not isinstance(value, dict):
        raise StatusError("manifest root must be an object")
    if value.get("kind") != "simp_engine_boundary_manifest" or value.get("reportSchema") != 2:
        raise StatusError("status requires a schema-2 simp_engine_boundary_manifest")
    if value.get("allowDirty") is not False or value.get("allowUnresolved") is not False:
        raise StatusError("status requires a closed manifest (allowDirty=false and allowUnresolved=false)")
    modules = value.get("modules")
    if not isinstance(modules, list):
        raise StatusError("manifest modules must be an array")
    if value.get("moduleFileCount") != len(modules):
        raise StatusError("manifest moduleFileCount does not match modules")
    if not isinstance(value.get("occurrenceCount"), int) or value["occurrenceCount"] < 0:
        raise StatusError("manifest occurrenceCount must be a nonnegative integer")
    if not isinstance(value.get("implementationHashes"), dict) or not value["implementationHashes"]:
        raise StatusError("manifest implementationHashes must be a nonempty object")
    for field in ("repositoryCommit", "mathlibCommit"):
        if not isinstance(value.get(field), str) or not value[field]:
            raise StatusError(f"manifest {field} is required for current identity")
    lean = value.get("lean")
    if not isinstance(lean, dict) or not all(
        isinstance(lean.get(field), str) and lean[field] for field in ("version", "commit")
    ):
        raise StatusError("manifest Lean identity is incomplete")

    # Prefer the caller's root, then an authenticated root in the manifest,
    # then the same candidates used by the index importer. A derived status can
    # still work when the historical manifest path was moved by inferring the
    # root from an indexed module source path below.
    candidates: list[Path] = []
    if source_root is not None:
        candidates.append(source_root.resolve())
    if isinstance(value.get("sourceRoot"), str) and value["sourceRoot"]:
        candidates.append(Path(value["sourceRoot"]).resolve())
    try:
        candidates.append(_source_root(path, None))
    except TranslationIndexError:
        pass
    for raw in modules:
        if not isinstance(raw, dict) or not isinstance(raw.get("module"), str):
            continue
        row = connection.execute("SELECT source_path FROM modules WHERE module=?", (raw["module"],)).fetchone()
        if row is None:
            continue
        source_path = Path(row["source_path"]).resolve()
        parts = Path(raw["module"]).parts
        if len(parts) >= 2:
            candidates.append(source_path.parents[len(parts) - 1])
    root = next((candidate for candidate in candidates if (candidate / "Mathlib").is_dir()), None)
    if root is None:
        raise StatusError("cannot locate Mathlib source root to validate the manifest")

    try:
        # The importer has already authenticated dependency joins in the
        # durable index. Here we validate source and occurrence identities;
        # cache_key below uses those durable joins for the actual dependency
        # identity. Let the validator parse headers when no explicit map is
        # available, as an explicit empty map is not a valid index map.
        records = _validated_modules(path, value, root)
    except (TranslationIndexError, OSError, ValueError) as error:
        raise StatusError(f"invalid or incomplete manifest: {error}") from error
    if sum(len(record["occurrences"]) for record in records) != value["occurrenceCount"]:
        raise StatusError("manifest occurrenceCount does not match validated occurrences")
    manifest_hash = sha256_bytes(payload)
    return value, records, manifest_hash, root


def _manifest_input(connection: sqlite3.Connection, manifest: Path | None) -> tuple[Path, bytes, object]:
    if manifest is not None:
        path = manifest.resolve()
        try:
            payload = path.read_bytes()
            return path, payload, json.loads(payload)
        except (OSError, json.JSONDecodeError) as error:
            raise StatusError(f"cannot read manifest {path}: {error}") from error
    try:
        row = connection.execute(
            "SELECT path,payload_json FROM manifests ORDER BY imported_at DESC, manifest_hash DESC LIMIT 1"
        ).fetchone()
    except sqlite3.OperationalError as error:
        raise StatusError("database has no manifest history; pass --manifest") from error
    if row is None:
        raise StatusError("database has no manifest history; pass --manifest")
    path = Path(row["path"]).resolve()
    payload = str(row["payload_json"]).encode("utf-8")
    try:
        return path, payload, json.loads(payload)
    except json.JSONDecodeError as error:
        raise StatusError("newest stored manifest payload is invalid JSON") from error


def _strict_report_verified(
    row: sqlite3.Row,
    module: str,
    manifest_path: Path,
    manifest_bytes: bytes,
    manifest: dict[str, Any],
    overlay: manual_overlay.Overlay | None,
) -> bool:
    """Run the maintained evidence consumer for an exact-current report.

    ``result_cache`` stores a copy of the report alongside its artifact path.
    Bind those two copies before delegating to the worker's strict verifier;
    otherwise a forged cache JSON could point at a valid-looking evidence tree.
    Historical rows deliberately do not pay this current-evidence check.
    """
    artifact = Path(row["artifact_ref"]) if row["artifact_ref"] else None
    if artifact is None or not artifact.is_file():
        return False
    try:
        result = json.loads(row["result_json"])
        artifact_result = json.loads(artifact.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, ValueError, TypeError):
        return False
    if artifact_result != result:
        return False
    try:
        return campaign_worker._report_is_verified(
            result,
            module,
            manifest_path,
            manifest_bytes,
            manifest,
            artifact.resolve(),
            overlay=overlay,
        )
    except (TranslationIndexError, RuntimeError, OSError, ValueError, TypeError, KeyError, IndexError):
        return False


def _report_info(
    row: sqlite3.Row,
    required_schema: int,
    manifest_hash: str | None = None,
    *,
    strict_verified: bool = False,
) -> dict[str, Any]:
    artifact = Path(row["artifact_ref"]) if row["artifact_ref"] else None
    present = artifact is not None and artifact.is_file()
    report_schema = replay_schema = oracle_replay_schema = report_manifest_hash = None
    try:
        result = json.loads(row["result_json"])
        module = result.get("modules", [{}])[0] if isinstance(result, dict) else {}
        oracle = module.get("declarationOracle", {}) if isinstance(module, dict) else {}
        report_schema = result.get("reportSchema") if isinstance(result, dict) else None
        report_manifest_hash = result.get("manifestHash") if isinstance(result, dict) else None
        replay_schema = module.get("replayGuard", {}).get("schema") if isinstance(module, dict) else None
        oracle_replay_schema = oracle.get("replayGuard", {}).get("schema") if isinstance(oracle, dict) else None
        calls = result.get("aggregate", {}).get("materializeCount", 0) if isinstance(result, dict) else 0
        calls = int(calls or 0)
    except (ValueError, TypeError, AttributeError, IndexError):
        calls = 0
    guarded = bool(
        present and report_schema == required_schema and replay_schema == 1
        and oracle_replay_schema == 1
        and (manifest_hash is None or report_manifest_hash == manifest_hash)
        and strict_verified
    )
    return {
        "artifact": str(artifact) if artifact else None,
        "artifactPresent": present,
        "reportSchema": report_schema,
        "manifestHash": report_manifest_hash,
        "replaySchema": replay_schema,
        "oracleReplaySchema": oracle_replay_schema,
        "calls": calls,
        "guarded": guarded,
    }


def _storage(path: Path, minimum_free_bytes: int) -> dict[str, Any]:
    try:
        free = shutil.disk_usage(path.parent).free
    except OSError as error:
        return {"canDispatch": False, "freeBytes": None, "minimumFreeBytes": minimum_free_bytes, "error": str(error)}
    return {"canDispatch": free >= minimum_free_bytes, "freeBytes": free, "minimumFreeBytes": minimum_free_bytes}


def snapshot(
    database: Path,
    manifest: Path | None = None,
    *,
    dependency_digests: Mapping[str, str] | None = None,
    manual_overrides: Path | None = None,
    source_root: Path | None = None,
    minimum_free_bytes: int = DEFAULT_MINIMUM_FREE_BYTES,
) -> dict[str, object]:
    path = database.resolve()
    connection = sqlite3.connect(f"file:{quote(str(path))}?mode=ro", uri=True)
    connection.row_factory = sqlite3.Row
    try:
        connection.execute("BEGIN")
        manifest_path, manifest_bytes, manifest_value = _manifest_input(connection, manifest)
        value, records, manifest_hash, validated_root = _complete_manifest(
            manifest_path, manifest_bytes, manifest_value, connection, source_root
        )
        # Campaign manifests authenticate the manual table used by the
        # worker. Derive that part of the identity by default; callers can
        # still pass a different path to diagnose an explicitly chosen table.
        if manual_overrides is None and isinstance(value.get("manualOverrides"), dict):
            manual_overrides = manual_overlay.DEFAULT_DATABASE
        overlay = None
        overlay_identity = None
        if manual_overrides is not None:
            if not manual_overrides.is_file():
                raise StatusError(f"manual override database is missing: {manual_overrides}")
            try:
                overlay = manual_overlay._load_overlay_projected(
                    manifest_path, manual_overrides.resolve(), source_root=validated_root,
                    manifest_value=value, manifest_bytes=manifest_bytes,
                    module_records={
                        str(raw["module"]): raw
                        for raw in value["modules"]
                        if isinstance(raw, dict) and isinstance(raw.get("module"), str)
                    },
                )
                overlay_identity = overlay.identity()
            except (RuntimeError, OSError, ValueError) as error:
                raise StatusError(f"invalid manual override identity: {error}") from error
        try:
            implementation, toolchain = campaign_worker._identities(value, overlay_identity)
        except (RuntimeError, OSError, ValueError, KeyError) as error:
            raise StatusError(f"cannot derive current implementation identity: {error}") from error
        try:
            campaign = json.loads((ROOT / "tracking/campaign.json").read_text(encoding="utf-8"))
            coverage = campaign.get("coverage", {})
            campaign_schema = int(coverage.get("minimumAcceptedReportSchema", REPORT_SCHEMA))
            validation_hold = coverage.get("validationHold")
        except (OSError, json.JSONDecodeError, TypeError, ValueError, AttributeError) as error:
            raise StatusError(f"cannot read campaign acceptance policy: {error}") from error
        required_schema = max(REPORT_SCHEMA, campaign_schema, int(value.get("minimumAcceptedReportSchema", REPORT_SCHEMA)))
        expected = {record["module"]: record for record in records}
        module_rows = connection.execute("SELECT * FROM modules ORDER BY module").fetchall()
        queue_states = dict(connection.execute(
            "SELECT COALESCE(q.state,'unplanned'),COUNT(*) FROM modules m LEFT JOIN work_queue q ON q.module=m.module GROUP BY COALESCE(q.state,'unplanned')"
        ).fetchall())
        active = [dict(row) for row in connection.execute("SELECT module,worker,lease_expires_at FROM work_queue WHERE state='running' ORDER BY module")]
        failures = [dict(row) for row in connection.execute(
            "SELECT q.module,r.status,r.translation_status,r.failure,r.log_ref FROM work_queue q JOIN result_cache r ON r.cache_key=q.cache_key WHERE q.state='failed' OR r.translation_status='candidate_translated' ORDER BY q.module LIMIT 30"
        )]
        exact: list[dict[str, Any]] = []
        historical: list[dict[str, Any]] = []
        historical_keys: set[str] = set()
        identity_mismatches: list[str] = []
        missing_index_modules: list[str] = []
        cache_identity_mismatches: list[str] = []
        stale_queue: list[str] = []
        missing_reports = 0
        current_keys: dict[str, str] = {}
        identity_memo: dict[str, str] = {}
        source_memo: dict[str, str] = {}
        indexed_modules: set[str] = set()
        for row in module_rows:
            module = row["module"]
            record = expected.get(module)
            if record is None:
                continue
            indexed_modules.add(module)
            if (row["source_hash"], row["module_hash"], row["analysis_identity"]) != (record["source_hash"], record["module_hash"], record["analysis_identity"]):
                identity_mismatches.append(module)
                continue
            try:
                key, dependencies = cache_key(
                    connection, module, implementation, toolchain, dependency_digests,
                    identity_memo=identity_memo, source_memo=source_memo,
                )
            except (TranslationIndexError, OSError, ValueError) as error:
                raise StatusError(f"cannot derive current cache identity for {module}: {error}") from error
            current_keys[module] = key
            queue = connection.execute("SELECT * FROM work_queue WHERE module=?", (module,)).fetchone()
            current = connection.execute("SELECT * FROM result_cache WHERE cache_key=?", (key,)).fetchone()
            if queue is not None and queue["cache_key"] != key:
                stale_queue.append(module)
            if current is not None:
                expected_cache_fields = {
                    "module": module,
                    "source_hash": row["source_hash"],
                    "analysis_identity": row["analysis_identity"],
                    "implementation_identity": canonical(implementation),
                    "toolchain_identity": canonical(toolchain),
                    "dependency_identity": dependencies,
                }
                if any(current[field] != expected_value for field, expected_value in expected_cache_fields.items()):
                    # The cache key is an index lookup aid, not a substitute
                    # for validating the denormalized fields it represents.
                    # Keep this row as historical evidence, but never let a
                    # forged key/row combination count as current coverage.
                    cache_identity_mismatches.append(module)
                    info = _report_info(current, required_schema)
                    historical.append({"module": module, "cacheKey": key, **info, "verified": current["status"] == "success" and current["translation_status"] == "verified_translated"})
                    historical_keys.add(key)
                else:
                    strict_verified = (
                        current["status"] == "success"
                        and current["translation_status"] == "verified_translated"
                        and _strict_report_verified(
                            current, module, manifest_path, manifest_bytes, value, overlay
                        )
                    )
                    info = _report_info(
                        current, required_schema, manifest_hash,
                        strict_verified=strict_verified,
                    )
                    item = {"module": module, "cacheKey": key, "dependencyIdentity": dependencies, **info}
                    item["verified"] = current["status"] == "success" and current["translation_status"] == "verified_translated"
                    item["queueCurrent"] = queue is not None and queue["cache_key"] == key and queue["state"] == "succeeded"
                    item["exactCurrent"] = True
                    exact.append(item)
                    if item["verified"] and not info["artifactPresent"]:
                        missing_reports += 1
            all_results = connection.execute(
                "SELECT * FROM result_cache WHERE module=? AND cache_key<>? ORDER BY recorded_at DESC", (module, key)
            ).fetchall()
            for old in all_results:
                info = _report_info(old, required_schema)
                historical.append({"module": module, "cacheKey": old["cache_key"], **info, "verified": old["status"] == "success" and old["translation_status"] == "verified_translated"})
                historical_keys.add(old["cache_key"])
        # Keep historical evidence for modules removed from the supplied
        # manifest, and for rows whose indexed source identity no longer
        # matches it. Only a cache row equal to the recomputed current key is
        # eligible for exact-current coverage.
        missing_index_modules = sorted(set(expected) - indexed_modules)
        identity_mismatches.extend(module for module in missing_index_modules if module not in identity_mismatches)
        for old in connection.execute("SELECT * FROM result_cache ORDER BY recorded_at DESC"):
            if old["cache_key"] in historical_keys:
                continue
            if old["module"] in current_keys and old["cache_key"] == current_keys[old["module"]]:
                continue
            info = _report_info(old, required_schema)
            historical.append({"module": old["module"], "cacheKey": old["cache_key"], **info, "verified": old["status"] == "success" and old["translation_status"] == "verified_translated"})
            historical_keys.add(old["cache_key"])
        exact_verified = [item for item in exact if item["verified"] and item["queueCurrent"] and item["guarded"]]
        historical_verified = [item for item in historical if item["verified"]]
        accepted = [] if validation_hold else exact_verified
        unresolved = sum(int(row["unresolved_count"]) for row in module_rows)
        open_backlog = connection.execute(
            "SELECT COUNT(*),COUNT(DISTINCT b.module) FROM unresolved_backlog b JOIN modules m ON m.module=b.module AND m.source_hash=b.source_hash AND m.analysis_identity=b.analysis_identity WHERE b.status='open'"
        ).fetchone()
        return {
            "updatedAt": datetime.now(timezone.utc).isoformat(),
            "database": str(path),
            "manifest": {"path": str(manifest_path), "sha256": manifest_hash, "modules": len(records), "occurrences": int(value["occurrenceCount"]), "identityMatchedModules": len(records) - len(identity_mismatches), "identityMismatchedModules": identity_mismatches},
            "currentIdentity": {"implementation": implementation, "toolchain": toolchain},
            "indexedModules": len(module_rows),
            "indexedSourceCalls": connection.execute("SELECT COUNT(*) FROM occurrences").fetchone()[0],
            "unresolvedCalls": unresolved,
            "queueStates": queue_states,
            "exactCurrentVerifiedModules": len(exact_verified),
            "exactCurrentVerifiedCalls": sum(item["calls"] for item in exact_verified),
            "exactCurrentCacheRows": len(exact),
            "historicalVerifiedModules": len({item["module"] for item in historical_verified}),
            "historicalVerifiedResults": len(historical_verified),
            "historicalVerifiedCalls": sum(item["calls"] for item in historical_verified),
            "staleQueueModules": len(stale_queue),
            "identityMismatchedModules": len(identity_mismatches),
            "missingIndexedModules": missing_index_modules,
            "cacheIdentityMismatches": sorted(set(cache_identity_mismatches)),
            "cachedVerifiedModules": len(accepted),
            "cachedVerifiedCalls": sum(item["calls"] for item in accepted),
            "provisionalCachedModules": len(exact) - len(accepted),
            "provisionalCachedCalls": sum(item["calls"] for item in exact if item not in accepted),
            "missingVerifiedReportFiles": missing_reports,
            "backlog": {"currentUnresolvedCalls": unresolved, "openUnresolvedRows": int(open_backlog[0]), "openUnresolvedModules": int(open_backlog[1])},
            "storage": _storage(path, minimum_free_bytes),
            "verificationScope": (f"Acceptance on hold: {validation_hold} " if validation_hold else "") + f"Exact current cache identity uses manifest {manifest_hash} plus campaign worker identities and translation_index.cache_key; historical rows are retained for triage and excluded from current coverage. Accepted counts require report schema {required_schema}, replay-error checks, declaration comparison and boundary state guards.",
            "active": active,
            "failuresAndPartialResults": failures,
        }
    finally:
        connection.close()


def markdown(status: dict[str, object]) -> str:
    missing_indexed = status["missingIndexedModules"]
    missing_names = ", ".join(f"`{module}`" for module in missing_indexed) or "none"
    lines = [
        "# Search-free Mathlib campaign", "", f"Updated {status['updatedAt']}", "",
        f"- Indexed: {status['indexedSourceCalls']:,} calls in {status['indexedModules']:,} modules.",
        f"- Exact current verified cache: {status['exactCurrentVerifiedCalls']:,} translated calls in {status['exactCurrentVerifiedModules']:,} modules.",
        f"- Historical verified cache: {status['historicalVerifiedCalls']:,} calls across {status['historicalVerifiedResults']:,} result rows ({status['historicalVerifiedModules']:,} modules).",
        f"- Accepted per-module verification: {status['cachedVerifiedCalls']:,} calls in {status['cachedVerifiedModules']:,} modules.",
        f"- Unresolved source classifications: {status['unresolvedCalls']}.",
        f"- Stale queue identities: {status['staleQueueModules']}; missing exact-current reports: {status['missingVerifiedReportFiles']}.", "",
        f"Manifest: `{status['manifest']['sha256']}` ({status['manifest']['identityMatchedModules']} modules match the indexed source/analysis identity).", "",
        f"Manifest modules absent from index ({len(missing_indexed)}): {missing_names}; cache identity mismatches: {len(status['cacheIdentityMismatches'])}.", "",
        str(status["verificationScope"]), "",
        "Queue: " + ", ".join(f"{key}={value}" for key, value in sorted(status["queueStates"].items())),
        f"Backlog: {status['backlog']['openUnresolvedRows']} open unresolved rows.",
        f"Storage: {status['storage'].get('freeBytes')} free bytes; dispatch threshold {status['storage']['minimumFreeBytes']}.", "",
        "## Active modules", "",
    ]
    lines.extend(f"- `{row['module']}` ({row['worker']})" for row in status["active"])
    if not status["active"]:
        lines.append("No active module lease.")
    lines.extend(["", "## Failures and partial results", ""])
    for row in status["failuresAndPartialResults"]:
        detail = str(row["failure"] or row["translation_status"]).replace("\n", " ").replace("`", "'")
        lines.append(f"- `{row['module']}`: {detail}")
    if not status["failuresAndPartialResults"]:
        lines.append("None recorded for the current queue.")
    lines.extend(["", "Regenerate with `python3 Experiment/campaign_status.py --manifest PATH --markdown`.", ""])
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", type=Path, default=DEFAULT_DATABASE)
    parser.add_argument("--manifest", type=Path, help="complete closed schema-2 manifest; defaults to newest stored manifest")
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--dependency-digests", type=Path)
    parser.add_argument("--manual-overrides", type=Path)
    parser.add_argument("--minimum-free-bytes", type=int, default=DEFAULT_MINIMUM_FREE_BYTES)
    parser.add_argument("--markdown", action="store_true")
    args = parser.parse_args(argv)
    try:
        result = snapshot(args.database, args.manifest, dependency_digests=_read_json_map(args.dependency_digests), manual_overrides=args.manual_overrides, source_root=args.source_root, minimum_free_bytes=args.minimum_free_bytes)
    except (StatusError, TranslationIndexError, OSError, ValueError, sqlite3.Error) as error:
        print(f"campaign-status: {error}", file=sys.stderr)
        return 2
    print(markdown(result) if args.markdown else json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
