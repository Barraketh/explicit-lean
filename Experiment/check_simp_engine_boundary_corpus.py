#!/usr/bin/env python3
"""Check deterministic boundary-manifest construction on three pinned modules."""

from __future__ import annotations

import copy
import json
from pathlib import Path
import tempfile

import simp_engine_boundary_corpus as corpus
import simp_engine_inventory as inventory
import check_simp_engine_boundary_scope as scope
import boundary_materialize_shard as materialize


ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "Mathlib/CategoryTheory/EqToHom.lean",
    "Mathlib/Data/Fintype/List.lean",
    "Mathlib/Analysis/CStarAlgebra/SpecialFunctions/PosPart.lean",
)


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


def validate_manifest(manifest: dict[str, object]) -> None:
    if manifest.get("reportSchema") != 1 or manifest.get("kind") != (
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
        "Experiment/check_simp_engine_boundary_scope.py",
        "Experiment/simp_engine_boundary_corpus.py",
    }
    missing_hashes = required_hashes - set(implementation_hashes)
    if missing_hashes:
        raise RuntimeError(
            f"manifest omitted active implementation sources: {sorted(missing_hashes)}"
        )
    expected_dispositions = {"eligible": 30, "excluded": 12}
    if manifest.get("countsByDisposition") != expected_dispositions:
        raise RuntimeError(
            f"unexpected scope partition: {manifest.get('countsByDisposition')}"
        )
    modules = manifest.get("modules")
    if not isinstance(modules, list) or [module.get("module") for module in modules] != (
        sorted(MODULES)
    ):
        raise RuntimeError("manifest module ordering or coverage changed")
    seen: set[str] = set()
    disposition_count = 0
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
            if occurrence["disposition"] not in {"eligible", "excluded"}:
                raise RuntimeError(f"non-actionable occurrence: {occurrence}")
            disposition_count += 1
    if len(seen) != 42 or disposition_count != 42:
        raise RuntimeError("manifest occurrences do not form a total partition")


def main() -> None:
    validate_execution_join()
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
        summary_tampered["countsByDisposition"]["unclassified"] = 1
        try:
            corpus.publish_manifest(rejected_path, summary_tampered)
        except RuntimeError as error:
            if "countsByDisposition does not match occurrence records" not in str(error):
                raise
        else:
            raise RuntimeError("manifest policy trusted a tampered disposition summary")
        if rejected_path.read_bytes() != sentinel:
            raise RuntimeError("policy rejection replaced the existing manifest")

        occurrence_tampered = copy.deepcopy(manifests[0])
        changed_occurrence = occurrence_tampered["modules"][0]["occurrences"][0]
        original_classification = changed_occurrence["classification"]
        original_disposition = changed_occurrence["disposition"]
        changed_occurrence["classification"] = "unclassified"
        changed_occurrence["disposition"] = "unclassified"
        try:
            corpus.publish_manifest(rejected_path, occurrence_tampered)
        except RuntimeError as error:
            if "countsByClassification does not match occurrence records" not in str(error):
                raise
        else:
            raise RuntimeError("manifest policy trusted stale summary counts")

        classifications = occurrence_tampered["countsByClassification"]
        classifications[original_classification] -= 1
        if classifications[original_classification] == 0:
            del classifications[original_classification]
        classifications["unclassified"] = 1
        dispositions = occurrence_tampered["countsByDisposition"]
        dispositions[original_disposition] -= 1
        if dispositions[original_disposition] == 0:
            del dispositions[original_disposition]
        dispositions["unclassified"] = 1
        try:
            corpus.publish_manifest(rejected_path, occurrence_tampered)
        except RuntimeError as error:
            if "unclassified occurrences" not in str(error):
                raise
        else:
            raise RuntimeError("default manifest policy accepted an unclassified call")
        if rejected_path.read_bytes() != sentinel:
            raise RuntimeError("policy rejection replaced the existing manifest")
        occurrence_tampered["allowUnclassified"] = True
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
        "eligible=30, excluded=12, deterministic and fail-closed: ok"
    )


if __name__ == "__main__":
    main()
