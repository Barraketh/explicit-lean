#!/usr/bin/env python3
"""Check deterministic boundary-manifest construction on three pinned modules."""

from __future__ import annotations

import copy
import io
import json
from pathlib import Path
import tempfile

import simp_engine_boundary_corpus as corpus
import simp_engine_inventory as inventory
import check_simp_engine_boundary_scope as scope
import boundary_materialize_shard as materialize
from boundary_protocol import (
    artifact_protocol,
    ARTIFACT_SCHEMA,
    SELECTOR_SCHEMA,
    RECORDING_ABORT_MARKER,
    make_occurrence_result,
    occurrence_classification_counts,
    validate_artifact_protocol,
    validate_report,
    validate_occurrence_result,
    validate_occurrence_summary,
    check_recording_abort_markers,
    marker_prefix,
    parse_framed_json_lines,
    reject_forbidden_generated_text,
)


ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "Mathlib/CategoryTheory/EqToHom.lean",
    "Mathlib/Data/Fintype/List.lean",
    "Mathlib/Analysis/CStarAlgebra/SpecialFunctions/PosPart.lean",
)


def encoded_constant(name: str) -> str:
    return json.dumps(["expr_dag_v2", 0, [["c", [["s", part] for part in name.split(".")], []]], 0])


def expect_join_rejection(
    entries: list[dict[str, object]],
    occurrences: list[dict[str, object]],
    label: str,
) -> None:
    try:
        corpus.join_scope_records(label, entries, occurrences, [])
    except RuntimeError as error:
        if "scope/inventory join is not one-to-one" not in str(error):
            raise
    else:
        raise RuntimeError(f"{label} scope mutation was accepted")


def validate_execution_join() -> None:
    def report(
        occurrence_id: str,
        caller: str | None,
        proof: bool | None,
        *,
        count: int = 1,
        status: str = "complete",
    ) -> dict[str, object]:
        return {
            "occurrenceId": occurrence_id,
            "module": "Test.Module",
            "caller": caller,
            "executionCount": count,
            "isProofDeclaration": proof,
            "evidenceStatus": status,
        }

    complete = scope._execution_evidence(
        {"proof"}, [report("proof", "Test.Module.proof", True)], "Test.Module"
    )
    if complete["proof"]["status"] != "complete_proof_declaration":
        raise RuntimeError(f"complete execution evidence was not accepted: {complete}")
    mixed = scope._execution_evidence(
        {"mixed"},
        [
            report("mixed", "Test.Module.proof", True),
            report("mixed", "Test.Module.data", False),
        ],
        "Test.Module",
    )
    if mixed["mixed"]["status"] != "mixed_execution_classification":
        raise RuntimeError(f"mixed execution evidence did not fail closed: {mixed}")
    missing = scope._execution_evidence({"missing"}, [], "Test.Module")
    if missing["missing"]["status"] != "missing_execution":
        raise RuntimeError(f"missing execution evidence did not fail closed: {missing}")
    incomplete = scope._execution_evidence(
        {"incomplete"}, [report("incomplete", None, None)], "Test.Module"
    )
    if incomplete["incomplete"]["status"] != "incomplete_execution_evidence":
        raise RuntimeError(
            f"missing caller/type evidence did not fail closed: {incomplete}"
        )
    empty_caller = report("empty-caller", "", True)
    try:
        scope._execution_evidence(
            {"empty-caller"}, [empty_caller], "Test.Module"
        )
    except RuntimeError as error:
        if "invalid caller" not in str(error):
            raise
    else:
        raise RuntimeError("empty scope execution caller was accepted")
    wrong_module = report("wrong-module", "Test.Module.proof", True)
    wrong_module["module"] = "Other.Module"
    try:
        scope._execution_evidence(
            {"wrong-module"}, [wrong_module], "Test.Module"
        )
    except RuntimeError as error:
        if "wrong module" not in str(error):
            raise
    else:
        raise RuntimeError("execution evidence from the wrong module was accepted")

    occurrence = {
        "startByte": 1,
        "endByte": 5,
        "kind": "simp",
        "source": "simp",
    }
    if scope._result_occurrence(occurrence) is not occurrence:
        raise RuntimeError("flattened manifest occurrence was not accepted")
    nested = {"occurrence": occurrence}
    if scope._result_occurrence(nested) is not occurrence:
        raise RuntimeError("nested classifier occurrence was not accepted")
    for label, reports in (
        ("extra", [report("unexpected", "Test.Module.proof", True)]),
        (
            "duplicate",
            [
                report("duplicate", "Test.Module.proof", True),
                report("duplicate", "Test.Module.proof", True),
            ],
        ),
    ):
        try:
            scope._execution_evidence({"duplicate"}, reports, "Test.Module")
        except RuntimeError:
            pass
        else:
            raise RuntimeError(f"{label} execution join mutation was accepted")


def validate_declaration_oracle_protocol() -> None:
    base: dict[str, object] = {
        "kind": materialize.DECLARATION_ORACLE_KIND,
        "schema": materialize.DECLARATION_ORACLE_SCHEMA,
        "module": "Test.Module",
        "status": "success",
        "failureCategory": None,
        "failureDetail": None,
        "stockDeclarationCount": 5,
        "appliedDeclarationCount": 4,
        "commonPublicDeclarationCount": 3,
        "stockOnlyPrivateProofCount": 1,
        "appliedOnlyPrivateProofCount": 0,
        "stockExtensionCount": 2,
        "appliedExtensionCount": 2,
        "checkedDeclarationCount": 4,
    }

    def parse(report: dict[str, object]) -> dict[str, object]:
        marker = materialize.DECLARATION_ORACLE_MARKER + json.dumps(report)
        return materialize._parse_declaration_oracle(marker, "Test.Module")

    if parse(base) != base:
        raise RuntimeError("valid declaration-oracle protocol report changed")

    mutations = (
        ("boolean schema", "unexpected schema", {"schema": True}),
        (
            "inconsistent stock counts",
            "inconsistent stock counts",
            {"stockDeclarationCount": 6},
        ),
        (
            "inconsistent applied counts",
            "inconsistent applied counts",
            {"appliedDeclarationCount": 5},
        ),
        (
            "inconsistent public count",
            "inconsistent public count",
            {"commonPublicDeclarationCount": 5},
        ),
    )
    for label, expected, changes in mutations:
        forged = dict(base)
        forged.update(changes)
        try:
            parse(forged)
        except RuntimeError as error:
            if expected not in str(error):
                raise
        else:
            raise RuntimeError(f"materializer accepted {label}")

    failure = dict(base)
    failure.update(
        status="failure",
        failureCategory="test_failure",
        failureDetail="test detail",
    )
    for field in materialize.DECLARATION_ORACLE_COUNT_FIELDS:
        failure[field] = 0
    parse(failure)
    failure["checkedDeclarationCount"] = 1
    try:
        parse(failure)
    except RuntimeError as error:
        if "nonzero counts" not in str(error):
            raise
    else:
        raise RuntimeError("materializer accepted nonzero failure counts")


def validate_occurrence_protocol() -> None:
    """Exercise schema-5 occurrence taxonomy and fail-closed validation."""
    ids = ["materialized", "expected-failure", "unobserved", "retained"]
    actions = ["materialize", "materialize", "materialize", "retain"]
    results = [
        make_occurrence_result("materialized", "materialize", 1, [{"status": "success"}]),
        make_occurrence_result("expected-failure", "materialize", 2, [{"status": "failure"}]),
        make_occurrence_result("unobserved", "materialize", 0, []),
        make_occurrence_result("retained", "retain", 0, []),
    ]
    counts = occurrence_classification_counts(results)
    if set(counts) != {
        "materialized",
        "expected_failure",
        "unobserved_executable",
        "covered_by_ancestor",
        "retained_syntax_data",
    }:
        raise RuntimeError(f"occurrence taxonomy is incomplete: {counts}")
    validate_occurrence_summary(results, ids, actions, counts)

    def expect_rejection(
        value: object,
        expected_id: str,
        message: str,
    ) -> None:
        try:
            validate_occurrence_result(value, expected_id)
        except RuntimeError as error:
            if message not in str(error):
                raise RuntimeError(
                    f"occurrence mutation expected {message!r}, got {error}"
                ) from error
        else:
            raise RuntimeError(f"occurrence mutation was accepted: {message}")

    bad_count = dict(results[0])
    bad_count["executionCount"] = -1
    expect_rejection(bad_count, ids[0], "must be nonnegative")
    bad_type = dict(results[0])
    bad_type["executionCount"] = "one"
    expect_rejection(bad_type, ids[0], "must be an integer")
    bad_bool = dict(results[0])
    bad_bool["variantCount"] = True
    expect_rejection(bad_bool, ids[0], "must be an integer")
    bad_action = dict(results[0])
    bad_action["action"] = "unresolved"
    expect_rejection(bad_action, ids[0], "invalid occurrence result")
    bad_classification = dict(results[0])
    bad_classification["classification"] = "printer_failure"
    expect_rejection(bad_classification, ids[0], "invalid occurrence result classification")
    bad_id = dict(results[0])
    bad_id["occurrence"] = "other"
    expect_rejection(bad_id, ids[0], "occurrence result ID mismatch")
    bad_observation = dict(results[0])
    bad_observation["variantCount"] = 0
    bad_observation["successVariantCount"] = 0
    expect_rejection(bad_observation, ids[0], "observed occurrence has invalid counts")
    bad_status_count = dict(results[0])
    bad_status_count["successVariantCount"] = 0
    bad_status_count["failureVariantCount"] = 1
    expect_rejection(
        bad_status_count,
        ids[0],
        "materialized occurrence has no successful variant",
    )
    bad_status_sum = dict(results[0])
    bad_status_sum["failureVariantCount"] = 1
    expect_rejection(
        bad_status_sum,
        ids[0],
        "status counts do not match variantCount",
    )

    inconsistent_counts = dict(counts)
    inconsistent_counts["materialized"] += 1
    try:
        validate_occurrence_summary(results, ids, actions, inconsistent_counts)
    except RuntimeError as error:
        if "do not match occurrenceResults" not in str(error):
            raise
    else:
        raise RuntimeError("inconsistent occurrence classification counts were accepted")

    bad_aggregate_type = dict(counts)
    bad_aggregate_type["materialized"] = True
    try:
        validate_occurrence_summary(results, ids, actions, bad_aggregate_type)
    except RuntimeError as error:
        if "must be an integer" not in str(error):
            raise
    else:
        raise RuntimeError("boolean occurrence classification count was accepted")

    try:
        validate_occurrence_summary(
            results,
            ids,
            ["retain", *actions[1:]],
            counts,
        )
    except RuntimeError as error:
        if "action mismatch" not in str(error):
            raise
    else:
        raise RuntimeError("inconsistent occurrence action partition was accepted")

    identity = artifact_protocol()
    validate_artifact_protocol(identity)
    shard_identity = {
        "kind": materialize.REPORT_KIND,
        "reportSchema": materialize.REPORT_SCHEMA,
        "reportIdentity": {
            "kind": materialize.REPORT_KIND,
            "reportSchema": materialize.REPORT_SCHEMA,
        },
        "artifactProtocol": identity,
    }
    materialize.validate_shard_identity(shard_identity)
    bad_schema = dict(shard_identity)
    bad_schema["reportSchema"] = 4
    try:
        materialize.validate_shard_identity(bad_schema)
    except RuntimeError as error:
        if f"must be {materialize.REPORT_SCHEMA}" not in str(error):
            raise
    else:
        raise RuntimeError("schema-4 shard report was accepted")
    bad_identity = dict(shard_identity)
    bad_identity["artifactProtocol"] = dict(identity)
    bad_identity["artifactProtocol"]["encoding"] = dict(identity["encoding"])
    bad_identity["artifactProtocol"]["encoding"]["locals"] = "wrong"
    try:
        materialize.validate_shard_identity(bad_identity)
    except RuntimeError as error:
        if "unsupported encoding" not in str(error):
            raise
    else:
        raise RuntimeError("forged artifact protocol encoding was accepted")

    abort_cases = {
        "boundary_comparison_unsupported_environment_delta:foo": "external_effect_failure",
        "boundary_state_delta_unsupported:foo": "external_effect_failure",
        "boundary_comparison_extra_module_uses_not_stock_subset": "external_effect_failure",
        "boundary_comparison_missing_stock_extension:test": "external_effect_failure",
        "boundary_comparison_missing_applied_extension:test": "external_effect_failure",
        "boundary_comparison_nondeterministic_extension_serialization:test": "external_effect_failure",
        "boundary_comparison_extension_state:test": "external_effect_failure",
        "ambiguous_boundary_variant:foo": "ambiguous_boundary_variant",
        "declaration oracle failed: declaration_value_mismatch:foo": "declaration_value_mismatch",
        "declaration oracle failed: environment_delta_mismatch:foo": "environment_delta_mismatch",
        "artifact contains unstable printer output": "printer_failure",
    }
    for message, expected in abort_cases.items():
        if materialize.abort_category(RuntimeError(message)) != expected:
            raise RuntimeError(f"abort category mapping changed for {message!r}")

    marker = {
        "kind": "simp_engine_boundary_recording_abort",
        "schema": 1,
        "occurrence": "recording-abort-test",
        "module": "Test.Module",
        "stage": "artifact_capture",
        "detail": "test detail",
    }
    nonce = "test-recording-nonce"
    marker_line = marker_prefix(RECORDING_ABORT_MARKER, nonce) + json.dumps(marker)
    try:
        check_recording_abort_markers(
            marker_line, expected_nonce=nonce, expected_module="Test.Module"
        )
    except RuntimeError as error:
        if "boundary recording abort" not in str(error):
            raise
    else:
        raise RuntimeError("valid recording-abort marker was ignored")
    for forged in (
        marker_line[:-1] + ",",
        marker_prefix(RECORDING_ABORT_MARKER, nonce)
        + json.dumps({**marker, "schema": True}),
        marker_prefix(RECORDING_ABORT_MARKER, nonce)
        + json.dumps({key: value for key, value in marker.items() if key != "detail"}),
    ):
        try:
            check_recording_abort_markers(
                forged, expected_nonce=nonce, expected_module="Test.Module"
            )
        except RuntimeError as error:
            if "recording-abort marker" not in str(error):
                raise
        else:
            raise RuntimeError("malformed recording-abort marker was accepted")

    # Authored diagnostics can reproduce the legacy marker or guess a nonce,
    # but neither must be accepted as a durable recorder abort.  The same
    # framing check protects artifact reports from forged diagnostics.
    for forged in (
        RECORDING_ABORT_MARKER + json.dumps(marker),
        marker_prefix(RECORDING_ABORT_MARKER, "wrong-nonce") + json.dumps(marker),
    ):
        try:
            check_recording_abort_markers(forged, expected_nonce=nonce)
        except RuntimeError as error:
            if "wrong nonce or framing" not in str(error):
                raise
        else:
            raise RuntimeError("forged recording-abort marker was accepted")
    for forged in (
        "SIMP_ENGINE_BOUNDARY_ARTIFACT " + json.dumps({"kind": "forged"}),
        marker_prefix("SIMP_ENGINE_BOUNDARY_ARTIFACT ", "wrong-nonce")
        + json.dumps({"kind": "forged"}),
    ):
        try:
            parse_framed_json_lines(
                forged,
                marker="SIMP_ENGINE_BOUNDARY_ARTIFACT ",
                expected_nonce=nonce,
                label="boundary artifact",
            )
        except RuntimeError as error:
            if "wrong nonce or framing" not in str(error):
                raise
        else:
            raise RuntimeError("forged artifact marker was accepted")
    for forbidden in ("sorryAx", "sorry", "admit"):
        try:
            reject_forbidden_generated_text(
                {"term": f"generated {forbidden}"}, "forbidden-term test"
            )
        except RuntimeError:
            pass
        else:
            raise RuntimeError(f"forbidden generated token was accepted: {forbidden}")

    def artifact(
        terminal: str,
        *,
        local_result: str | None,
        target_result: str | None,
    ) -> dict[str, object]:
        transformation = lambda result: {
            "input": encoded_constant("P"),
            "result": encoded_constant(result),
            "proof": encoded_constant("Test.proof"),
        }
        locals_value = [] if local_result is None else [
            {
                "reference": {"kind": "local_decl_index", "index": 0},
                "userName": "h",
                "transformation": transformation(local_result),
            }
        ]
        return {
            "kind": "simp_engine_boundary_artifact",
            "schema": ARTIFACT_SCHEMA,
            "semanticContract": "boundary-observable-v1",
            "occurrence": "terminal-test",
            "selector": {
                "selectorSchema": SELECTOR_SCHEMA,
                "occurrence": "terminal-test",
                "preState": {
                    "targetFingerprint": "target",
                    "localContextFingerprint": "locals",
                    "metavariableContextFingerprint": "mvars",
                    "goalCount": 1,
                },
                "options": "options",
                "module": "Test.Module",
                "caller": None,
            },
            "status": "success",
            "terminal": terminal,
            "encoding": {
                "terms": "lean_expr_dag_v2",
                "locals": "local_decl_index_v1",
                "universes": "pre_boundary_universe_reference_v1",
                "instances": "explicit_terms_v1",
            },
            "stateDeltas": [],
            "environmentActions": [],
            "locals": locals_value,
            "target": None if target_result is None else transformation(target_result),
        }

    validate_report(
        artifact("closed_from_local_false", local_result="False", target_result=None),
        "terminal-test",
        "Test.Module",
    )
    validate_report(
        artifact("closed_from_target_true", local_result=None, target_result="True"),
        "terminal-test",
        "Test.Module",
    )
    for forged in (
        artifact("closed_from_local_false", local_result="P", target_result=None),
        artifact("closed_from_local_false", local_result="False", target_result="P"),
        artifact("closed_from_target_true", local_result=None, target_result="P"),
        artifact("closed_from_target_true", local_result="False", target_result="True"),
        artifact("open", local_result="False", target_result=None),
        artifact("open", local_result=None, target_result="True"),
    ):
        try:
            validate_report(forged, "terminal-test", "Test.Module")
        except RuntimeError:
            pass
        else:
            raise RuntimeError(f"terminal/evidence contradiction was accepted: {forged}")

    with tempfile.TemporaryDirectory(prefix="classification-evidence-") as raw_dir:
        source = b"example : True := by\n  simp\n"
        start = source.index(b"simp")
        end = start + len(b"simp")
        module_name = "Mathlib/Test.lean"
        compiled_module = "Mathlib.Test"
        occurrence_id = inventory.occurrence_id(module_name, start, end)
        source_path = Path(raw_dir) / "Test.lean"
        source_path.write_bytes(source)
        inventory_entry = {
            "id": occurrence_id,
            "module": module_name,
            "kind": "simp",
            "source": "simp",
            "startByte": start,
            "endByte": end,
            "line": 2,
            "column": 3,
            "syntaxKind": "Lean.Parser.Tactic.simp",
        }
        recorded = {
            **inventory_entry,
            "executionRole": "direct_executable",
            "declarationKind": "proof",
            "action": "materialize",
        }
        selected = materialize.SelectedModule(
            module_name,
            compiled_module,
            source_path,
            source,
            (recorded,),
            (recorded,),
            (),
        )
        scope_occurrence = {
            "startByte": start,
            "endByte": end,
            "kind": "simp",
            "source": "simp",
            "ancestors": [],
            "commandKind": "Lean.Parser.Command.theorem",
            "commandStartByte": 0,
            "commandEndByte": len(source),
        }
        declaration = {
            "name": "Mathlib.Test.test",
            "startByte": 0,
            "endByte": len(source),
            "isProof": True,
        }
        original_inventory_paths = materialize.corpus.inventory_paths
        original_load_records = materialize.scope.load_records_with_fallbacks
        materialize.corpus.inventory_paths = (
            lambda _paths, batch_size, timeout: ({module_name: [inventory_entry]}, [])
        )
        materialize.scope.load_records_with_fallbacks = (
            lambda _specs, batch_size, timeout: (
                {compiled_module: [scope_occurrence]},
                {compiled_module: [declaration]},
                [],
            )
        )
        try:
            materialize.verify_selected_classifications([selected], 1)
            for field, forged_value in (
                ("action", "retain"),
                ("executionRole", "retained_syntax_data"),
                ("declarationKind", "computational"),
                ("kind", "simp_only"),
            ):
                forged_record = dict(recorded)
                forged_record[field] = forged_value
                forged_selected = materialize.SelectedModule(
                    module_name,
                    compiled_module,
                    source_path,
                    source,
                    (forged_record,),
                    (forged_record,),
                    (),
                )
                try:
                    materialize.verify_selected_classifications([forged_selected], 1)
                except RuntimeError as error:
                    if f".{field}" not in str(error):
                        raise
                else:
                    raise RuntimeError(
                        f"forged source-backed classification {field} was accepted"
                    )
        finally:
            materialize.corpus.inventory_paths = original_inventory_paths
            materialize.scope.load_records_with_fallbacks = original_load_records


def shard_report_fixture() -> dict[str, object]:
    """Return a complete tiny schema-5 report for validator mutation tests."""
    occurrence = make_occurrence_result(
        "occurrence", "materialize", 1, [{"status": "success"}]
    )
    retained = make_occurrence_result("retained", "retain", 0, [])
    occurrence_results = [occurrence, retained]
    classification_counts = occurrence_classification_counts(occurrence_results)
    oracle = {
        "kind": materialize.DECLARATION_ORACLE_KIND,
        "schema": materialize.DECLARATION_ORACLE_SCHEMA,
        "module": "Mathlib.Test",
        "status": "success",
        "failureCategory": None,
        "failureDetail": None,
        "stockDeclarationCount": 1,
        "appliedDeclarationCount": 1,
        "commonPublicDeclarationCount": 1,
        "stockOnlyPrivateProofCount": 0,
        "appliedOnlyPrivateProofCount": 0,
        "stockExtensionCount": 0,
        "appliedExtensionCount": 0,
        "checkedDeclarationCount": 1,
    }
    module = {
        "module": "Mathlib/Test.lean",
        "compiledModule": "Mathlib.Test",
        "sourcePath": "/tmp/source.lean",
        "originalPath": "/tmp/original.lean",
        "instrumentedPath": "/tmp/instrumented.lean",
        "materializedPath": "/tmp/materialized.lean",
        "reportPath": "/tmp/artifacts.jsonl",
        "originalHash": "original-hash",
        "instrumentedHash": "instrumented-hash",
        "materializedHash": "materialized-hash",
        "reportHash": "report-hash",
        "original": {"path": "/tmp/original.lean", "sha256": "original-hash"},
        "instrumented": {
            "path": "/tmp/instrumented.lean",
            "sha256": "instrumented-hash",
            "compileSuccess": True,
            "seconds": 0,
        },
        "materialized": {
            "path": "/tmp/materialized.lean",
            "sha256": "materialized-hash",
            "compileSuccess": True,
            "seconds": 0,
        },
        "artifactReport": {"path": "/tmp/artifacts.jsonl", "sha256": "report-hash"},
        "replayGuard": {
            "kind": materialize.REPLAY_GUARD_KIND,
            "schema": materialize.REPLAY_GUARD_SCHEMA,
            "nonce": "a" * 43,
            "path": "/tmp/materialized.log",
            "sha256": "replay-log-hash",
        },
        "declarationOracle": {
            "path": "/tmp/oracle.log",
            "reportPath": "/tmp/oracle-report.json",
            "sha256": "oracle-hash",
            "reportSha256": "oracle-report-hash",
            "compileSuccess": True,
            "seconds": 0,
            "status": "success",
            "report": oracle,
            "replayGuard": {
                "kind": materialize.REPLAY_GUARD_KIND,
                "schema": materialize.REPLAY_GUARD_SCHEMA,
                "nonce": "b" * 43,
                "path": "/tmp/oracle.log",
                "sha256": "oracle-hash",
            },
        },
        "totalCount": 2,
        "materializeCount": 1,
        "retainCount": 1,
        "occurrenceResults": occurrence_results,
        "occurrenceClassificationCounts": classification_counts,
        "materializeIds": ["occurrence"],
        "replacementRootIds": ["occurrence"],
        "retainIds": ["retained"],
        "observedIds": ["occurrence"],
        "unobservedIds": [],
        "executionReportCount": 1,
        "variantCount": 1,
        "variantCounts": {"occurrence": 1},
        "executionStatusCounts": {"success": 1},
        "variantStatusCounts": {"success": 1},
        "remainingRetainedCount": 0,
        "remainingRetainedMultiset": {},
        "exactSourcePreservation": {
            "verified": True,
            "materializeRangesReplaced": True,
            "outsideMaterializeRanges": "byte-identical",
            "authoredBindersPreserved": True,
            "alphaRenaming": False,
            "statement": "test",
        },
        "compileSuccess": True,
    }
    provenance = {
        "repositoryCommit": "repository",
        "mathlibCommit": "mathlib",
        "lean": {"version": "4.32.2", "commit": "lean"},
        "manifestRepositoryCommit": "repository",
        "manifestMathlibCommit": "mathlib",
    }
    top = {
        "kind": materialize.REPORT_KIND,
        "reportSchema": materialize.REPORT_SCHEMA,
        "reportIdentity": {
            "kind": materialize.REPORT_KIND,
            "reportSchema": materialize.REPORT_SCHEMA,
        },
        "artifactProtocol": artifact_protocol(),
        "manifestPath": "/tmp/manifest.json",
        "manifestHash": "manifest-hash",
        "manifest": {"path": "/tmp/manifest.json", "sha256": "manifest-hash"},
        "manifestPolicy": {"allowDirty": False, "allowUnresolved": False},
        "provenance": provenance,
        "repositoryCommit": "repository",
        "mathlibCommit": "mathlib",
        "lean": provenance["lean"],
        "runnerPath": "/tmp/runner.py",
        "runnerHash": "runner-hash",
        "runner": {"path": "/tmp/runner.py", "sha256": "runner-hash"},
        "selectedModules": ["Mathlib/Test.lean"],
        "modules": [module],
        "totalCount": 2,
        "materializeCount": 1,
        "retainCount": 1,
        "occurrenceResults": occurrence_results,
        "occurrenceClassificationCounts": classification_counts,
        "observedIds": ["occurrence"],
        "unobservedIds": [],
        "executionReportCount": 1,
        "variantCount": 1,
        "executionStatusCounts": {"success": 1},
        "variantStatusCounts": {"success": 1},
        "remainingRetainedCount": 0,
        "exactSourcePreservation": {
            "verified": True,
            "alphaRenaming": False,
            "statement": "test",
        },
        "compileSuccess": True,
        "aggregate": {
            "selectedModuleCount": 1,
            "totalCount": 2,
            "materializeCount": 1,
            "retainCount": 1,
            "occurrenceClassificationCounts": classification_counts,
            "observedCount": 1,
            "unobservedCount": 0,
            "executionReportCount": 1,
            "variantCount": 1,
            "remainingRetainedCount": 0,
        },
    }
    return top


def validate_shard_report_protocol() -> None:
    base = shard_report_fixture()
    if materialize.validate_shard_protocol(base) != base:
        raise RuntimeError("valid guarded shard report changed during validation")

    for mutation in ("old-schema", "missing-apply-guard", "missing-oracle-guard",
                     "unauthenticated", "reused-nonce", "wrong-guard-schema"):
        changed = copy.deepcopy(base)
        module = changed["modules"][0]
        if mutation == "old-schema":
            changed["reportSchema"] = 6
            changed["reportIdentity"]["reportSchema"] = 6
        elif mutation == "missing-apply-guard":
            del module["replayGuard"]
        elif mutation == "missing-oracle-guard":
            del module["declarationOracle"]["replayGuard"]
        elif mutation == "unauthenticated":
            module["replayGuard"]["nonce"] = "unauthenticated"
        elif mutation == "reused-nonce":
            module["replayGuard"]["nonce"] = module["declarationOracle"]["replayGuard"]["nonce"]
        else:
            module["replayGuard"]["schema"] = True
        try:
            materialize.validate_shard_protocol(changed)
        except RuntimeError:
            pass
        else:
            raise RuntimeError(f"shard validator accepted replay guard mutation {mutation}")

    missing_result = copy.deepcopy(base)
    del missing_result["modules"][0]["occurrenceResults"][0]
    del missing_result["occurrenceResults"][0]
    try:
        materialize.validate_shard_protocol(missing_result)
    except RuntimeError as error:
        if "occurrenceResults IDs disagree" not in str(error):
            raise RuntimeError(
                f"missing occurrence result produced the wrong error: {error}"
            ) from error
    else:
        raise RuntimeError("shard validator accepted a missing occurrence result")

    aggregate_mismatch = copy.deepcopy(base)
    aggregate_mismatch["aggregate"]["totalCount"] += 1
    try:
        materialize.validate_shard_protocol(aggregate_mismatch)
    except RuntimeError as error:
        if "aggregate disagrees" not in str(error):
            raise RuntimeError(
                f"aggregate mutation produced the wrong error: {error}"
            ) from error
    else:
        raise RuntimeError("shard validator accepted an aggregate mismatch")

    aggregate_bool = copy.deepcopy(base)
    aggregate_bool["aggregate"]["selectedModuleCount"] = True
    try:
        materialize.validate_shard_protocol(aggregate_bool)
    except RuntimeError as error:
        if "must be an integer" not in str(error):
            raise
    else:
        raise RuntimeError("shard validator accepted a boolean aggregate count")

    for field in ("modules", "occurrenceResults", "aggregate"):
        forged = copy.deepcopy(base)
        if field == "modules":
            forged["modules"][0]["module"] = "Mathlib/Other.lean"
        elif field == "occurrenceResults":
            forged["occurrenceResults"].pop()
        else:
            forged["aggregate"]["variantCount"] += 1
        try:
            materialize.validate_shard_protocol(forged)
        except RuntimeError:
            pass
        else:
            raise RuntimeError(f"shard validator accepted forged {field}")

    for location in ("top", "module", "aggregate"):
        forged = copy.deepcopy(base)
        if location == "top":
            forged["unexpected"] = True
        elif location == "module":
            forged["modules"][0]["unexpected"] = True
        else:
            forged["aggregate"]["unexpected"] = True
        try:
            materialize.validate_shard_protocol(forged)
        except RuntimeError:
            pass
        else:
            raise RuntimeError(f"shard validator accepted an extra {location} field")

    stream = io.StringIO()
    if not materialize.emit_failure_marker(
        RuntimeError("ambiguous_boundary_variant: test"), stream
    ):
        raise RuntimeError("known boundary failure did not emit a marker")
    marker_lines = stream.getvalue().splitlines()
    if len(marker_lines) != 1 or not marker_lines[0].startswith(materialize.FAILURE_MARKER):
        raise RuntimeError(f"failure marker has unexpected framing: {stream.getvalue()!r}")
    marker_payload = json.loads(
        marker_lines[0].split(materialize.FAILURE_MARKER, 1)[1]
    )
    if set(marker_payload) != {"kind", "schema", "category", "detail"}:
        raise RuntimeError(f"failure marker fields changed: {marker_payload!r}")
    if marker_payload != {
        "kind": materialize.FAILURE_KIND,
        "schema": materialize.FAILURE_SCHEMA,
        "category": "ambiguous_boundary_variant",
        "detail": "ambiguous_boundary_variant: test",
    }:
        raise RuntimeError(f"failure marker payload changed: {marker_payload!r}")
    unknown_stream = io.StringIO()
    if materialize.emit_failure_marker(RuntimeError("ordinary failure"), unknown_stream):
        raise RuntimeError("ordinary failure unexpectedly emitted an abort marker")
    if unknown_stream.getvalue():
        raise RuntimeError("unknown failure wrote a marker")

    output_root = materialize.BOUNDARY_DEBUG_ROOT
    output_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="protocol-output-", dir=output_root) as raw_dir:
        output_dir = Path(raw_dir)
        output = output_dir / "report.json"
        temporary = output.with_name(output.name + ".tmp")
        output.write_text("old report", encoding="utf-8")
        temporary.write_text("old temporary", encoding="utf-8")
        materialize.invalidate_output(output)
        if output.exists() or temporary.exists():
            raise RuntimeError("exact stale report output was not invalidated")
        missing_manifest = output_dir / "missing-manifest.json"
        args = materialize.parser().parse_args(
            [
                "--manifest",
                str(missing_manifest),
                "--output",
                str(output),
                "--module",
                "Mathlib/Test.lean",
            ]
        )
        output.write_text("old report", encoding="utf-8")
        temporary.write_text("old temporary", encoding="utf-8")
        try:
            materialize.run_shard(args)
        except RuntimeError as error:
            if "manifest does not exist" not in str(error):
                raise
        else:
            raise RuntimeError("missing-manifest shard unexpectedly succeeded")
        if output.exists() or temporary.exists():
            raise RuntimeError("failed shard left a stale success report")
        run_root = materialize.debug_root_for(output)
        stale = run_root / "module" / "stale.txt"
        sibling = output_dir / "sibling.txt"
        stale.parent.mkdir(parents=True, exist_ok=True)
        stale.write_text("stale", encoding="utf-8")
        sibling.write_text("preserve", encoding="utf-8")
        materialize.clear_debug_root(run_root)
        if stale.exists() or not run_root.is_dir():
            raise RuntimeError("debug run subtree was not cleared exactly")
        if sibling.read_text(encoding="utf-8") != "preserve":
            raise RuntimeError("debug run subtree clearing removed a sibling")
        run_root.rmdir()
        symlink_target = output_dir / "symlink-target"
        symlink_target.mkdir()
        target_file = symlink_target / "preserve.txt"
        target_file.write_text("preserve", encoding="utf-8")
        run_root.symlink_to(symlink_target, target_is_directory=True)
        materialize.clear_debug_root(run_root)
        if run_root.is_symlink() or not run_root.is_dir():
            raise RuntimeError("debug run symlink was not replaced by an exact directory")
        if target_file.read_text(encoding="utf-8") != "preserve":
            raise RuntimeError("debug clearing followed and removed a stale symlink target")

    original = b"module\nexample : True := by\n  simp\n"
    entries = [{"id": "test", "startByte": 30, "endByte": 34}]
    expected = b"module\nexample : True := by\n  exact True.intro\n"
    generated = b"module\n\nimport Test.Generated\nexample : True := by\n  exact True.intro\n"
    materialize.assert_exact_source_preservation(
        original,
        generated,
        entries,
        imported="Test.Generated",
        label="gap fixture",
        expected_without_import=expected,
    )
    try:
        materialize.assert_exact_source_preservation(
            original,
            b"module\n\nimport Test.Generated\n-- inserted authored byte\nexample : True := by\n  exact True.intro\n",
            entries,
            imported="Test.Generated",
            label="gap fixture",
            expected_without_import=expected,
        )
    except RuntimeError:
        pass
    else:
        raise RuntimeError("authored bytes inserted into a source gap were accepted")
    for label, corrupted in (
        (
            "deletion",
            b"module\n\nimport Test.Generated\nexample : True := by\n exact True.intro\n",
        ),
        (
            "corruption",
            b"module\n\nimport Test.Generated\nexample : False := by\n  exact True.intro\n",
        ),
        (
            "insertion",
            b"module\n\nimport Test.Generated\nexample /* forged */ : True := by\n  exact True.intro\n",
        ),
    ):
        try:
            materialize.assert_exact_source_preservation(
                original,
                corrupted,
                entries,
                imported="Test.Generated",
                label=f"gap fixture {label}",
                expected_without_import=corrupted.replace(
                    b"\nimport Test.Generated\n", b"", 1
                ),
            )
        except RuntimeError:
            pass
        else:
            raise RuntimeError(f"source-gap {label} was accepted")

    # Build a complete, file-backed one-occurrence report.  Shape-only fixture
    # tests above intentionally use /tmp placeholders; publication evidence
    # must instead be reproducible from the selected manifest and real files.
    with tempfile.TemporaryDirectory(prefix="boundary-evidence-") as raw_dir:
        work = Path(raw_dir)
        debug_root = work / "run"
        module_name = "Mathlib/Test.lean"
        compiled_module = "Mathlib.Test"
        source = b"module\nexample (P : Prop) (h : P) : P := by\n  simp\n"
        start = source.index(b"simp")
        end = start + len(b"simp")
        occurrence_id = inventory.occurrence_id(module_name, start, end)
        occurrence_entry = {
            "id": occurrence_id,
            "kind": "simp",
            "source": "simp",
            "startByte": start,
            "endByte": end,
            "syntaxKind": "Lean.Parser.Tactic.simp",
            "executionRole": "direct_executable",
            "declarationKind": "proof",
            "action": "materialize",
        }
        source_path = work / "source.lean"
        source_path.write_bytes(source)
        selected = materialize.SelectedModule(
            module=module_name,
            compiled_module=compiled_module,
            source_path=source_path,
            source=source,
            occurrences=(occurrence_entry,),
            materialize=(occurrence_entry,),
            retain=(),
        )
        artifact = {
            "kind": "simp_engine_boundary_artifact",
            "schema": ARTIFACT_SCHEMA,
            "semanticContract": "boundary-observable-v1",
            "occurrence": occurrence_id,
            "selector": {
                "selectorSchema": SELECTOR_SCHEMA,
                "occurrence": occurrence_id,
                "preState": {
                    "targetFingerprint": "target",
                    "localContextFingerprint": "locals",
                    "metavariableContextFingerprint": "mvars",
                    "goalCount": 1,
                },
                "options": "options",
                "module": compiled_module,
                "caller": None,
            },
            "status": "success",
            "terminal": "open",
            "encoding": artifact_protocol()["encoding"],
            "stateDeltas": [],
            "environmentActions": [],
            "locals": [],
            "target": {"input": encoded_constant("P"), "result": encoded_constant("P"),
                       "proof": encoded_constant("Test.proof")},
        }
        variants = {occurrence_id: [artifact]}
        module_root = debug_root / "Test"
        paths = {
            "original": module_root / "original" / "Mathlib" / "Test.lean",
            "instrumented": module_root / "instrumented" / "Mathlib" / "Test.lean",
            "materialized": module_root / "materialized" / "Mathlib" / "Test.lean",
            "materializedLog": module_root / "materialized.log",
            "artifacts": module_root / "artifact-reports.jsonl",
            "oracleLog": module_root / "declaration-oracle.log",
            "oracleReport": module_root / "declaration-oracle-report.json",
        }
        for path in paths.values():
            path.parent.mkdir(parents=True, exist_ok=True)
        paths["original"].write_bytes(source)
        instrumented = materialize.instrumented_source(source, [occurrence_entry])
        paths["instrumented"].write_bytes(instrumented)
        materialized_source = materialize._inject_import(
            materialize.replace_all_occurrences(source, [occurrence_entry], variants),
            "ExplicitLean.SimpEngine.Boundary.Tactic",
        )
        paths["materialized"].write_bytes(materialized_source)
        artifact_bytes = (materialize._canonical_json_line(artifact) + "\n").encode()
        paths["artifacts"].write_bytes(artifact_bytes)
        oracle = shard_report_fixture()["modules"][0]["declarationOracle"]["report"]
        oracle_bytes = (
            json.dumps(oracle, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
        ).encode()
        paths["materializedLog"].write_text("", encoding="utf-8")
        paths["oracleLog"].write_text(
            materialize.DECLARATION_ORACLE_MARKER + json.dumps(oracle) + "\n",
            encoding="utf-8",
        )
        paths["oracleReport"].write_bytes(oracle_bytes)
        manifest = {
            "repositoryCommit": "repository",
            "mathlibCommit": "mathlib",
            "lean": {"version": "4.32.2", "commit": "lean"},
        }
        manifest_path = work / "manifest.json"
        manifest_bytes = (json.dumps(manifest, sort_keys=True) + "\n").encode()
        manifest_path.write_bytes(manifest_bytes)

        result = make_occurrence_result(
            occurrence_id, "materialize", 1, [artifact]
        )
        classification_counts = occurrence_classification_counts([result])
        report = shard_report_fixture()
        module_report = report["modules"][0]
        module_report.update(
            sourcePath=str(source_path.resolve()),
            originalPath=str(paths["original"].resolve()),
            instrumentedPath=str(paths["instrumented"].resolve()),
            materializedPath=str(paths["materialized"].resolve()),
            reportPath=str(paths["artifacts"].resolve()),
            originalHash=materialize.sha256(source),
            instrumentedHash=materialize.sha256(instrumented),
            materializedHash=materialize.sha256(materialized_source),
            reportHash=materialize.sha256(artifact_bytes),
            totalCount=1,
            materializeCount=1,
            retainCount=0,
            occurrenceResults=[result],
            occurrenceClassificationCounts=classification_counts,
            materializeIds=[occurrence_id],
            replacementRootIds=[occurrence_id],
            retainIds=[],
            observedIds=[occurrence_id],
            unobservedIds=[],
            executionReportCount=1,
            variantCount=1,
            variantCounts={occurrence_id: 1},
            executionStatusCounts={"success": 1},
            variantStatusCounts={"success": 1},
            remainingRetainedCount=0,
            remainingRetainedMultiset={},
        )
        module_report["original"] = {
            "path": str(paths["original"].resolve()),
            "sha256": materialize.sha256(source),
        }
        module_report["instrumented"] = {
            "path": str(paths["instrumented"].resolve()),
            "sha256": materialize.sha256(instrumented),
            "compileSuccess": True,
            "seconds": 0,
        }
        module_report["materialized"] = {
            "path": str(paths["materialized"].resolve()),
            "sha256": materialize.sha256(materialized_source),
            "compileSuccess": True,
            "seconds": 0,
        }
        module_report["artifactReport"] = {
            "path": str(paths["artifacts"].resolve()),
            "sha256": materialize.sha256(artifact_bytes),
        }
        module_report["replayGuard"] = materialize.replay_guard_evidence(
            "", "a" * 43, paths["materializedLog"], compiled_module
        )
        module_report["declarationOracle"] = {
            "path": str(paths["oracleLog"].resolve()),
            "reportPath": str(paths["oracleReport"].resolve()),
            "sha256": materialize.sha256(paths["oracleLog"].read_bytes()),
            "reportSha256": materialize.sha256(oracle_bytes),
            "compileSuccess": True,
            "seconds": 0,
            "status": "success",
            "report": oracle,
            "replayGuard": materialize.replay_guard_evidence(
                paths["oracleLog"].read_text(), "b" * 43,
                paths["oracleLog"], compiled_module,
            ),
        }
        report.update(
            manifestPath=str(manifest_path.resolve()),
            manifestHash=materialize.sha256(manifest_bytes),
            manifest={
                "path": str(manifest_path.resolve()),
                "sha256": materialize.sha256(manifest_bytes),
            },
            repositoryCommit="repository",
            mathlibCommit="mathlib",
            lean=manifest["lean"],
            selectedModules=[module_name],
            totalCount=1,
            materializeCount=1,
            retainCount=0,
            occurrenceResults=[result],
            occurrenceClassificationCounts=classification_counts,
            observedIds=[occurrence_id],
            unobservedIds=[],
            executionReportCount=1,
            variantCount=1,
            executionStatusCounts={"success": 1},
            variantStatusCounts={"success": 1},
            remainingRetainedCount=0,
        )
        report["provenance"] = {
            "repositoryCommit": "repository",
            "mathlibCommit": "mathlib",
            "lean": manifest["lean"],
            "manifestRepositoryCommit": "repository",
            "manifestMathlibCommit": "mathlib",
        }
        runner_path = Path(materialize.__file__).resolve()
        runner_hash = materialize.sha256(runner_path.read_bytes())
        report["runnerPath"] = str(runner_path)
        report["runnerHash"] = runner_hash
        report["runner"] = {"path": str(runner_path), "sha256": runner_hash}
        report["aggregate"] = {
            "selectedModuleCount": 1,
            "totalCount": 1,
            "materializeCount": 1,
            "retainCount": 0,
            "occurrenceClassificationCounts": classification_counts,
            "observedCount": 1,
            "unobservedCount": 0,
            "executionReportCount": 1,
            "variantCount": 1,
            "remainingRetainedCount": 0,
        }

        original_inventory = materialize.inventory.syntax_inventory_file
        materialize.inventory.syntax_inventory_file = lambda *_args, **_kwargs: []
        try:
            materialize.verify_shard_evidence(
                report,
                manifest=manifest,
                manifest_path=manifest_path,
                manifest_bytes=manifest_bytes,
                selected=[selected],
                debug_root=debug_root,
                timeout=1,
            )
            # Rehashing an abort-bearing log must not turn a caught replay
            # failure into acceptable durable evidence in either process.
            for oracle_process in (False, True):
                changed = copy.deepcopy(report)
                changed_module = changed["modules"][0]
                wrapper = changed_module["declarationOracle"] if oracle_process else changed_module
                guard = wrapper["replayGuard"]
                path = paths["oracleLog" if oracle_process else "materializedLog"]
                original_log = path.read_bytes()
                payload = {
                    "kind": "simp_engine_boundary_replay_abort", "schema": 1,
                    "occurrence": occurrence_id, "module": compiled_module,
                    "stage": "apply", "detail": "caught invalid evidence",
                }
                contaminated = original_log + (
                    "SIMP_ENGINE_BOUNDARY_REPLAY_ABORT " + guard["nonce"] + " "
                    + json.dumps(payload) + "\n"
                ).encode()
                path.write_bytes(contaminated)
                guard["sha256"] = materialize.sha256(contaminated)
                if oracle_process:
                    wrapper["sha256"] = guard["sha256"]
                try:
                    materialize.verify_shard_evidence(
                        changed, manifest=manifest, manifest_path=manifest_path,
                        manifest_bytes=manifest_bytes, selected=[selected],
                        debug_root=debug_root, timeout=1,
                    )
                except RuntimeError as error:
                    if "boundary replay abort" not in str(error):
                        raise
                else:
                    raise RuntimeError("rehashed replay-abort evidence was accepted")
                finally:
                    path.write_bytes(original_log)
            nonexistent = copy.deepcopy(report)
            missing_path = work / "missing.lean"
            nonexistent["modules"][0]["originalPath"] = str(missing_path)
            nonexistent["modules"][0]["original"]["path"] = str(missing_path)
            try:
                materialize.verify_shard_evidence(
                    nonexistent,
                    manifest=manifest,
                    manifest_path=manifest_path,
                    manifest_bytes=manifest_bytes,
                    selected=[selected],
                    debug_root=debug_root,
                    timeout=1,
                )
            except RuntimeError:
                pass
            else:
                raise RuntimeError("nonexistent evidence path was accepted")

            paths["artifacts"].write_bytes(artifact_bytes + b"{}\n")
            try:
                materialize.verify_shard_evidence(
                    report,
                    manifest=manifest,
                    manifest_path=manifest_path,
                    manifest_bytes=manifest_bytes,
                    selected=[selected],
                    debug_root=debug_root,
                    timeout=1,
                )
            except RuntimeError as error:
                if "hash mismatch" not in str(error):
                    raise
            else:
                raise RuntimeError("tampered evidence file was accepted")
            paths["artifacts"].write_bytes(artifact_bytes)

            forged_identity = copy.deepcopy(report)
            alternate_manifest = work / "alternate-manifest.json"
            alternate_manifest.write_bytes(manifest_bytes)
            forged_identity["manifestPath"] = str(alternate_manifest.resolve())
            forged_identity["manifest"]["path"] = str(alternate_manifest.resolve())
            try:
                materialize.verify_shard_evidence(
                    forged_identity,
                    manifest=manifest,
                    manifest_path=manifest_path,
                    manifest_bytes=manifest_bytes,
                    selected=[selected],
                    debug_root=debug_root,
                    timeout=1,
                )
            except RuntimeError:
                pass
            else:
                raise RuntimeError("forged manifest path identity was accepted")

            forged_retained = copy.deepcopy(report)
            forged_retained["modules"][0]["remainingRetainedCount"] = 1
            forged_retained["modules"][0]["remainingRetainedMultiset"] = {
                "simp\u0000simp": 1
            }
            forged_retained["remainingRetainedCount"] = 1
            forged_retained["aggregate"]["remainingRetainedCount"] = 1
            try:
                materialize.verify_shard_evidence(
                    forged_retained,
                    manifest=manifest,
                    manifest_path=manifest_path,
                    manifest_bytes=manifest_bytes,
                    selected=[selected],
                    debug_root=debug_root,
                    timeout=1,
                )
            except RuntimeError as error:
                if "remaining retained evidence" not in str(error):
                    raise
            else:
                raise RuntimeError("forged retained inventory evidence was accepted")
        finally:
            materialize.inventory.syntax_inventory_file = original_inventory


def validate_manifest(manifest: dict[str, object]) -> None:
    if manifest.get("reportSchema") != 2 or manifest.get("kind") != (
        "simp_engine_boundary_manifest"
    ):
        raise RuntimeError(f"unexpected manifest identity: {manifest}")
    if manifest.get("allowDirty") is not True:
        raise RuntimeError("diagnostic smoke manifest did not disclose dirty allowance")
    if manifest.get("moduleFileCount") != 3:
        raise RuntimeError(f"expected three modules: {manifest.get('moduleFileCount')}")
    if manifest.get("occurrenceCount") != 42:
        raise RuntimeError(
            f"expected 42 occurrences: {manifest.get('occurrenceCount')}"
        )
    if manifest.get("duplicateSyntaxRecords") != 0:
        raise RuntimeError(
            "representative manifest unexpectedly contains duplicate syntax records"
        )
    if manifest.get("scopeFrontendFallbacks"):
        raise RuntimeError("representative manifest unexpectedly needed scope fallback")
    if manifest.get("duplicateScopeSyntaxRecords") != 0:
        raise RuntimeError(
            "representative manifest unexpectedly contains duplicate scope records"
        )
    if manifest.get("scopeProbe") != {
        "module": "ExplicitLean.SimpEngine.Boundary.ScopeProbe",
        "scheduling": "set_option Elab.async false",
        "temporaryCopyOnly": True,
        "reportCommand": "simp_engine_boundary_scope_report",
    }:
        raise RuntimeError("manifest scope-probe metadata is missing or unstable")
    implementation_hashes = manifest.get("implementationHashes")
    if not isinstance(implementation_hashes, dict):
        raise RuntimeError("manifest has no implementation hash mapping")
    required_hashes = {
        "ExplicitLean/SimpEngine/Inventory.lean",
        "ExplicitLean/SimpEngine/Boundary.lean",
        "ExplicitLean/SimpEngine/Boundary/Apply.lean",
        "ExplicitLean/SimpEngine/Boundary/Selector.lean",
        "ExplicitLean/SimpEngine/Boundary/Tactic.lean",
        "ExplicitLean/SimpEngine/Boundary/ScopeProbe.lean",
        "Experiment/SimpEngineInventory.lean",
        "Experiment/SimpEngineBoundaryScope.lean",
        "Experiment/SimpEngineDeclarationOracle.lean",
        "Experiment/boundary_materialize_shard.py",
        "Experiment/check_simp_engine_boundary_scope.py",
        "Experiment/check_simp_engine_declaration_oracle.py",
        "Experiment/simp_engine_boundary_corpus.py",
        "Experiment/boundary_protocol.py",
    }
    missing_hashes = required_hashes - set(implementation_hashes)
    if missing_hashes:
        raise RuntimeError(
            f"manifest omitted active implementation sources: {sorted(missing_hashes)}"
        )
    expected_roles = {"direct_executable": 42}
    if manifest.get("countsByExecutionRole") != expected_roles:
        raise RuntimeError(
            f"unexpected execution-role partition: {manifest.get('countsByExecutionRole')}"
        )
    expected_kinds = {"computational": 12, "proof": 30}
    if manifest.get("countsByDeclarationKind") != expected_kinds:
        raise RuntimeError(
            "unexpected declaration-kind partition: "
            f"{manifest.get('countsByDeclarationKind')}"
        )
    expected_actions = {"materialize": 42}
    if manifest.get("countsByAction") != expected_actions:
        raise RuntimeError(
            f"unexpected action partition: {manifest.get('countsByAction')}"
        )
    modules = manifest.get("modules")
    if not isinstance(modules, list) or [module.get("module") for module in modules] != (
        sorted(MODULES)
    ):
        raise RuntimeError("manifest module ordering or coverage changed")
    seen: set[str] = set()
    action_count = 0
    for module in modules:
        module_name = str(module["module"])
        source = (corpus.MATHLIB / module_name).read_bytes()
        occurrences = module.get("occurrences")
        if not isinstance(occurrences, list):
            raise RuntimeError(f"module occurrence list is invalid: {module_name}")
        for occurrence in occurrences:
            occurrence_id = str(occurrence["id"])
            if occurrence_id in seen:
                raise RuntimeError(f"duplicate occurrence id: {occurrence_id}")
            seen.add(occurrence_id)
            checked = dict(occurrence)
            checked["module"] = module_name
            inventory.validate_occurrence(source, checked)
            if occurrence["action"] != "materialize":
                raise RuntimeError(f"non-materialize occurrence: {occurrence}")
            action_count += 1
    if len(seen) != 42 or action_count != 42:
        raise RuntimeError("manifest occurrences do not form a total partition")


def main() -> None:
    validate_execution_join()
    validate_declaration_oracle_protocol()
    validate_occurrence_protocol()
    validate_shard_report_protocol()
    paths = [corpus.MATHLIB / module for module in MODULES]
    temporary_parent = ROOT / ".lake"
    temporary_parent.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="boundary-manifest-smoke-", dir=temporary_parent
    ) as raw_directory:
        directory = Path(raw_directory)
        encoded: list[bytes] = []
        manifests: list[dict[str, object]] = []
        for ordinal in range(2):
            manifest = corpus.build_manifest(
                paths,
                module_prefix="explicit-representative-list",
                allow_dirty=True,
                inventory_batch_size=3,
                scope_batch_size=3,
                timeout=600,
            )
            path = directory / f"manifest-{ordinal}.json"
            corpus.publish_manifest(path, manifest)
            encoded.append(path.read_bytes())
            manifests.append(json.loads(path.read_text(encoding="utf-8")))
        if manifests[0] != manifests[1] or encoded[0] != encoded[1]:
            raise RuntimeError("boundary manifest is not byte-for-byte deterministic")

        validate_manifest(manifests[0])
        materialize.verify_implementation_hashes(manifests[0])

        legacy_field = copy.deepcopy(manifests[0])
        legacy_field["allowUnclassified"] = False
        try:
            corpus.enforce_manifest_policy(legacy_field)
        except RuntimeError as error:
            if "top-level fields changed" not in str(error):
                raise
        else:
            raise RuntimeError("schema-2 policy accepted a legacy manifest field")

        noninteger_count = copy.deepcopy(manifests[0])
        noninteger_count["moduleFileCount"] = float(
            noninteger_count["moduleFileCount"]
        )
        try:
            corpus.enforce_manifest_policy(noninteger_count)
        except RuntimeError as error:
            if "moduleFileCount must be a nonnegative integer" not in str(error):
                raise
        else:
            raise RuntimeError("schema-2 policy accepted a non-integer count")

        stale_nested_count = copy.deepcopy(manifests[0])
        stale_nested_count["nestedOccurrenceCount"] += 1
        try:
            corpus.enforce_manifest_policy(stale_nested_count)
        except RuntimeError as error:
            if "nestedOccurrenceCount does not match" not in str(error):
                raise
        else:
            raise RuntimeError("schema-2 policy accepted a stale nested count")

        stale_duplicate_count = copy.deepcopy(manifests[0])
        stale_duplicate_count["duplicateSyntaxRecords"] += 1
        try:
            corpus.enforce_manifest_policy(stale_duplicate_count)
        except RuntimeError as error:
            if "duplicateSyntaxRecords does not match" not in str(error):
                raise
        else:
            raise RuntimeError("schema-2 policy accepted a stale duplicate count")

        malformed_unselected = copy.deepcopy(manifests[0])
        malformed_unselected["allowDirty"] = False
        selected_module = str(malformed_unselected["modules"][0]["module"])
        try:
            materialize.validate_manifest_selection(
                manifests[0],
                [selected_module],
                expect_total=None,
                expect_materialize=None,
            )
        except RuntimeError as error:
            if "requires allowDirty=false" not in str(error):
                raise
        else:
            raise RuntimeError("materializer accepted an allowDirty manifest")
        try:
            materialize.validate_manifest_selection(
                malformed_unselected,
                [selected_module, selected_module],
                expect_total=None,
                expect_materialize=None,
            )
        except RuntimeError as error:
            if "selected modules must be unique" not in str(error):
                raise
        else:
            raise RuntimeError("duplicate materializer module selection was accepted")

        del malformed_unselected["modules"][1]["occurrences"][0]["kind"]
        try:
            materialize.validate_manifest_selection(
                malformed_unselected,
                [selected_module],
                expect_total=None,
                expect_materialize=None,
            )
        except RuntimeError as error:
            if "occurrence in" not in str(error) or "missing=['kind']" not in str(error):
                raise
        else:
            raise RuntimeError(
                "materializer accepted a malformed occurrence in an unselected module"
            )

        forged_unselected_source = copy.deepcopy(manifests[0])
        forged_unselected_source["allowDirty"] = False
        forged_unselected_source["modules"][1]["occurrences"][0]["source"] = ""
        try:
            materialize.validate_manifest_selection(
                forged_unselected_source,
                [selected_module],
                expect_total=None,
                expect_materialize=None,
            )
        except RuntimeError as error:
            if "stale inventory" not in str(error):
                raise
        else:
            raise RuntimeError(
                "materializer accepted forged source in an unselected module"
            )

        malformed_scope_path = copy.deepcopy(manifests[0])
        malformed_scope_path["modules"][1]["occurrences"][0]["scopePaths"][0] = "bad"
        try:
            corpus.enforce_manifest_policy(malformed_scope_path)
        except RuntimeError as error:
            if "scopePaths[0] must be an object" not in str(error):
                raise
        else:
            raise RuntimeError("schema-2 policy accepted a malformed scope path")

        malformed_declaration = copy.deepcopy(manifests[0])
        declaration_occurrence = next(
            occurrence
            for module in malformed_declaration["modules"]
            for occurrence in module["occurrences"]
            if occurrence["declarations"]
        )
        del declaration_occurrence["declarations"][0]["name"]
        try:
            corpus.enforce_manifest_policy(malformed_declaration)
        except RuntimeError as error:
            if "declarations[0] fields changed" not in str(error):
                raise
        else:
            raise RuntimeError("schema-2 policy accepted a malformed declaration")

        missing_inventory_executable = copy.deepcopy(manifests[0])
        del missing_inventory_executable["implementationHashes"][
            "Experiment/SimpEngineInventory.lean"
        ]
        try:
            materialize.verify_implementation_hashes(missing_inventory_executable)
        except RuntimeError as error:
            if "implementation source set is not current" not in str(error):
                raise
        else:
            raise RuntimeError("materializer accepted an incomplete implementation hash set")

        missing_runner = copy.deepcopy(manifests[0])
        del missing_runner["implementationHashes"][
            "Experiment/boundary_materialize_shard.py"
        ]
        try:
            materialize.verify_implementation_hashes(missing_runner)
        except RuntimeError as error:
            if "implementation source set is not current" not in str(error):
                raise
        else:
            raise RuntimeError("materializer accepted a manifest without its runner hash")

        safe_output = materialize.resolve_output_path(
            ".lake/boundary-materialization/smoke/report.json",
            directory / "manifest-0.json",
        )
        if safe_output != (
            ROOT / ".lake" / "boundary-materialization" / "smoke" / "report.json"
        ).resolve():
            raise RuntimeError(f"materializer resolved the wrong output path: {safe_output}")
        for unsafe_output in (
            ".lake/packages/mathlib/Mathlib/Overwrite.lean",
            "Experiment/Overwrite.py",
        ):
            try:
                materialize.resolve_output_path(
                    unsafe_output, directory / "manifest-0.json"
                )
            except RuntimeError as error:
                if "must stay under .lake/boundary-materialization" not in str(error):
                    raise
            else:
                raise RuntimeError(
                    f"materializer accepted an unsafe output path: {unsafe_output}"
                )
        first_module = manifests[0]["modules"][0]
        first = dict(first_module["occurrences"][0])
        first["module"] = str(first_module["module"])
        first_source = (corpus.MATHLIB / first["module"]).read_bytes()
        collapsed, nested, duplicate_records = corpus.validate_module_inventory(
            first["module"], first_source, [first, dict(first)]
        )
        if len(collapsed) != 1 or nested != 0 or duplicate_records != 1:
            raise RuntimeError("identical syntax traversal records were not counted")
        conflicting = dict(first)
        conflicting["line"] = int(conflicting["line"]) + 1
        try:
            corpus.validate_module_inventory(
                first["module"], first_source, [first, conflicting]
            )
        except RuntimeError as error:
            if "conflicting inventory records" not in str(error):
                raise
        else:
            raise RuntimeError("conflicting syntax traversal records were accepted")
        expect_join_rejection([first], [], "missing-scope-record")
        collapsed_scope, scope_duplicates = corpus.join_scope_records(
            "identical-scope-record", [first], [first, dict(first)], []
        )
        if len(collapsed_scope) != 1 or scope_duplicates != 1:
            raise RuntimeError("identical scope traversal records were not counted")
        conflicting_scope = dict(first)
        conflicting_scope["ancestors"] = [
            "Lean.Parser.Command.macro",
            "Lean.Parser.Term.quot",
        ]
        try:
            corpus.join_scope_records(
                "conflicting-scope-record",
                [first],
                [first, conflicting_scope],
                [],
            )
        except RuntimeError as error:
            if "ambiguous scope classification" not in str(error):
                raise
        else:
            raise RuntimeError("conflicting scope classifications were accepted")

        rejected_path = directory / "policy-rejected.json"
        sentinel = b"existing manifest must survive policy rejection\n"
        rejected_path.write_bytes(sentinel)

        summary_tampered = copy.deepcopy(manifests[0])
        summary_tampered["countsByAction"]["unresolved"] = 1
        try:
            corpus.publish_manifest(rejected_path, summary_tampered)
        except RuntimeError as error:
            if "countsByAction does not match occurrence records" not in str(error):
                raise
        else:
            raise RuntimeError("manifest policy trusted a tampered action summary")
        if rejected_path.read_bytes() != sentinel:
            raise RuntimeError("policy rejection replaced the existing manifest")

        occurrence_tampered = copy.deepcopy(manifests[0])
        changed_occurrence = occurrence_tampered["modules"][0]["occurrences"][0]
        original_role = changed_occurrence["executionRole"]
        original_kind = changed_occurrence["declarationKind"]
        changed_occurrence["action"] = "unresolved"
        try:
            corpus.publish_manifest(rejected_path, occurrence_tampered)
        except RuntimeError as error:
            if "invalid boundary manifest scope dimensions" not in str(error):
                raise
        else:
            raise RuntimeError("manifest policy accepted inconsistent scope dimensions")

        changed_occurrence["executionRole"] = "direct_executable"
        changed_occurrence["declarationKind"] = "unknown"
        roles = occurrence_tampered["countsByExecutionRole"]
        roles[original_role] -= 1
        if roles[original_role] == 0:
            del roles[original_role]
        roles["direct_executable"] = roles.get("direct_executable", 0) + 1
        kinds = occurrence_tampered["countsByDeclarationKind"]
        kinds[original_kind] -= 1
        if kinds[original_kind] == 0:
            del kinds[original_kind]
        kinds["unknown"] = 1
        actions = occurrence_tampered["countsByAction"]
        actions["materialize"] -= 1
        if actions["materialize"] == 0:
            del actions["materialize"]
        actions["unresolved"] = 1
        try:
            corpus.publish_manifest(rejected_path, occurrence_tampered)
        except RuntimeError as error:
            if "unresolved occurrences" not in str(error):
                raise
        else:
            raise RuntimeError("default manifest policy accepted an unresolved call")
        if rejected_path.read_bytes() != sentinel:
            raise RuntimeError("policy rejection replaced the existing manifest")
        occurrence_tampered["allowUnresolved"] = True
        corpus.publish_manifest(rejected_path, occurrence_tampered)

        try:
            corpus.require_unchanged_hashes(
                "test_implementation",
                {"a": "one", "b": "two"},
                {"a": "changed", "b": "two"},
            )
        except RuntimeError as error:
            if "test_implementation_changed_during_run:['a']" not in str(error):
                raise
        else:
            raise RuntimeError("manifest accepted implementation drift")

    print(
        "boundary corpus manifest: three modules, 42 occurrences, "
        "materialize=42, retain=0, deterministic and fail-closed: ok"
    )


if __name__ == "__main__":
    main()
