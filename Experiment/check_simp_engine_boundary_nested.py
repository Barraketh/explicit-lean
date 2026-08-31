#!/usr/bin/env python3
"""Check whole-call coverage of nested simp ranges, including semantic gates."""

from __future__ import annotations

import copy
import itertools
import json
from pathlib import Path
import tempfile

import boundary_materialize_shard as shard
import check_simp_engine_boundary_corpus as protocol_tests
import simp_engine_boundary_corpus as corpus
import simp_engine_inventory as inventory
from boundary_protocol import (
    assert_exact_source_preservation,
    make_occurrence_result,
    occurrence_classification_counts,
    replacement_plan,
    validate_occurrence_summary,
)


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Experiment" / "SimpEngineBoundaryNestedInput.lean"
MODULE = "Mathlib/BoundaryNestedFixture.lean"
TIMEOUT = 600


def expect_rejection(action, detail: str) -> None:
    try:
        action()
    except RuntimeError as error:
        if detail not in str(error):
            raise RuntimeError(f"expected {detail!r}, got {error}") from error
    else:
        raise RuntimeError(f"expected rejection: {detail}")


def check_range_protocol() -> None:
    def entry(name, start, end, action="materialize"):
        return {"id": name, "startByte": start, "endByte": end, "action": action}

    source = bytes(range(64))
    entries = [entry("outer", 0, 40), entry("child", 10, 20),
               entry("deep", 12, 18), entry("sibling", 24, 32), entry("next", 40, 48)]
    for permutation in itertools.permutations(entries):
        roots, covered = replacement_plan(source, permutation, "test")
        if [value["id"] for value in roots] != ["outer", "next"] or covered != {
            "child": "outer", "deep": "outer", "sibling": "outer"
        }:
            raise RuntimeError("nested coverage is order-dependent or not outermost")
    for bad, message in (
        ([entry("a", 0, 40), entry("b", 10, 20), entry("c", 15, 30)], "crossing"),
        ([entry("a", 0, 40), entry("b", 0, 20)], "duplicate-start"),
        ([entry("a", 0, 20), entry("b", 0, 20)], "duplicate-start"),
        ([entry("a", 0, 20), entry("a", 30, 40)], "duplicate occurrence ID"),
        ([entry("a", True, 20)], "must be an integer"),
        ([entry("a", 0, 65)], "invalid source range"),
        ([entry("a", -1, 20)], "invalid source range"),
        ([entry("a", 20, 20)], "invalid source range"),
        ([entry("a", 0, 40), entry("b", 10, 20, "retain")], "mixed retained/executable"),
        ([entry("a", 0, 40, "retain"), entry("b", 10, 20)], "mixed retained/executable"),
    ):
        expect_rejection(lambda: replacement_plan(source, bad, "test"), message)

    # The independent source-gap proof must accept the union of nested ranges
    # but still reject an insertion in the untouched continuation.
    original = b"before simp [by simp] after\n"
    entries = [entry("a", 7, 21), entry("b", 16, 20)]
    expected = b"before replacement after\n"
    generated = b"import Test.Generated\n" + expected
    assert_exact_source_preservation(
        original, generated, entries, imported="Test.Generated", label="nested gaps",
        expected_without_import=expected,
    )
    corrupted = expected.replace(b"after", b"wrong")
    expect_rejection(lambda: assert_exact_source_preservation(
        original, b"import Test.Generated\n" + corrupted, entries,
        imported="Test.Generated", label="nested gaps",
        expected_without_import=corrupted,
    ), "outside selected ranges")
    expect_rejection(lambda: shard.replace_all_occurrences(
        original, entries, {"a": [], "b": []}
    ), "exactly to replacement roots")

    root = make_occurrence_result("root", "materialize", 1, [{"status": "success"}])
    child = make_occurrence_result("child", "materialize", 0, [], covered_by="root")

    def summary(values):
        return validate_occurrence_summary(
            values, [value["occurrence"] for value in values],
            [value["action"] for value in values], occurrence_classification_counts(values),
        )

    summary([root, child])
    for ancestor in ("missing", "child"):
        mutated = dict(child, coveredBy=ancestor)
        expect_rejection(lambda: summary([root, mutated]),
                         "invalid result" if ancestor == "child" else "replacement root")
    retained = make_occurrence_result("root", "retain", 0, [])
    expect_rejection(lambda: summary([retained, child]), "replacement root")
    cycle = make_occurrence_result("root", "materialize", 0, [], covered_by="child")
    expect_rejection(lambda: summary([cycle, child]), "replacement root")
    expect_rejection(lambda: make_occurrence_result(
        "child", "materialize", 1, [{"status": "success"}], covered_by="root"
    ), "invalid result")
    expect_rejection(lambda: summary([dict(root, coveredBy="child"), child]),
                     "non-covered occurrence")


def check_fixture(work: Path, dylib: str) -> dict:
    source = SOURCE.read_bytes()
    entries = inventory.syntax_inventory_file(SOURCE, MODULE, TIMEOUT)
    entries = [dict(entry, action="materialize") for entry in entries]
    roots, covered = replacement_plan(source, entries, "nested fixture")
    if (len(entries), len(roots), len(covered)) != (16, 7, 9):
        raise RuntimeError(f"nested fixture inventory changed: {len(entries)}, {len(roots)}, {len(covered)}")
    selected = shard.SelectedModule(
        module=MODULE, compiled_module=corpus.compiled_module_name(MODULE),
        source_path=SOURCE, source=source, occurrences=tuple(entries),
        materialize=tuple(entries), retain=(),
    )
    result = shard._module_result(selected, work, dylib, TIMEOUT)
    shard._validate_module_report(result, 0)
    counts = result["occurrenceClassificationCounts"]
    if counts != {"materialized": 5, "expected_failure": 1,
                  "unobserved_executable": 1, "covered_by_ancestor": 9,
                  "retained_syntax_data": 0}:
        raise RuntimeError(f"unexpected nested fixture outcomes: {counts}")
    artifacts = [json.loads(line) for line in Path(result["reportPath"]).read_text().splitlines()]
    if any(artifact["occurrence"] in covered for artifact in artifacts):
        raise RuntimeError("covered child was independently instrumented")
    materialized = Path(result["materializedPath"]).read_text()
    if any(f"occurrence_id := {json.dumps(child)}" in materialized for child in covered):
        raise RuntimeError("covered child has an independent dispatcher")
    if result["executionReportCount"] != 6 or result["remainingRetainedCount"] != 0:
        raise RuntimeError("nested fixture did not record exactly six outer executions")
    oracle = result["declarationOracle"]["report"]
    if oracle["commonPublicDeclarationCount"] != 7:
        raise RuntimeError(f"nested fixture declaration coverage changed: {oracle}")

    for field, value, error in (
        ("replacementRootIds", [str(entry["id"]) for entry in entries], "coverage"),
        ("unobservedIds", result["unobservedIds"] + [next(iter(covered))], "partition"),
    ):
        mutated = copy.deepcopy(result)
        mutated[field] = value
        expect_rejection(lambda: shard._validate_module_report(mutated, 0), error)
    check_coverage_evidence(work, selected, result)
    print("boundary nested fixture: 7 roots, 9 covered calls, semantic oracle and zero remaining: ok", flush=True)
    return result


def check_coverage_evidence(
    work: Path, selected: shard.SelectedModule, result: dict,
) -> None:
    """A shape-valid but wrong ancestor must fail file-backed verification.

    The small manifest wrapper is test-only metadata; this is not a publishable
    corpus run. All compiler, source, inventory, and artifact files are real.
    """
    report = protocol_tests.shard_report_fixture()
    manifest = {"repositoryCommit": "repository", "mathlibCommit": "mathlib",
                "lean": report["lean"]}
    manifest_path = work / "test-evidence-manifest.json"
    manifest_bytes = json.dumps(manifest, sort_keys=True).encode()
    manifest_path.write_bytes(manifest_bytes)
    report.update(manifestPath=str(manifest_path), manifestHash=shard.sha256(manifest_bytes),
                  manifest={"path": str(manifest_path), "sha256": shard.sha256(manifest_bytes)},
                  selectedModules=[selected.module], modules=[result])
    runner = Path(shard.__file__).resolve()
    runner_hash = shard.sha256(runner.read_bytes())
    report.update(runnerPath=str(runner), runnerHash=runner_hash,
                  runner={"path": str(runner), "sha256": runner_hash})
    for field in ("totalCount", "materializeCount", "retainCount", "occurrenceResults",
                  "occurrenceClassificationCounts", "observedIds", "unobservedIds",
                  "executionReportCount", "variantCount", "executionStatusCounts",
                  "variantStatusCounts", "remainingRetainedCount"):
        report[field] = result[field]
    for field in report["aggregate"]:
        if field in report:
            report["aggregate"][field] = report[field]
    report["aggregate"].update(observedCount=len(result["observedIds"]),
                               unobservedCount=len(result["unobservedIds"]))

    def verify(value):
        return shard.verify_shard_evidence(
            value, manifest=manifest, manifest_path=manifest_path,
            manifest_bytes=manifest_bytes, selected=[selected], debug_root=work,
            timeout=TIMEOUT,
        )

    verify(report)
    forged = copy.deepcopy(report)
    child = next(value for value in forged["occurrenceResults"] if value["coveredBy"] is not None)
    child["coveredBy"] = next(value for value in result["replacementRootIds"]
                             if value != child["coveredBy"])
    # deepcopy preserves the shared occurrenceResults between top and module.
    shard.validate_shard_shape(forged)
    expect_rejection(lambda: verify(forged), "not derived from artifact evidence")
    missing = copy.deepcopy(report)
    missing["modules"][0]["replacementRootIds"].pop()
    expect_rejection(lambda: verify(missing), "coverage")


def check_mathlib(work: Path, dylib: str) -> dict:
    module = "Mathlib/Algebra/BigOperators/GroupWithZero/Action.lean"
    manifest = corpus.build_manifest(
        [corpus.MATHLIB / module], module_prefix=module, allow_dirty=True,
        inventory_batch_size=1, scope_batch_size=1, timeout=TIMEOUT,
    )
    # This diagnostic gate also runs while implementation edits are uncommitted.
    # Do not forge allowDirty=false or weaken the publication guard to select
    # it through the public shard CLI. Reuse the builder's source-backed scope
    # records, then independently verify them before exercising the module path.
    source_path = corpus.MATHLIB / module
    source = source_path.read_bytes()
    entries = tuple(shard._validate_occurrence(module, source, entry)
                    for entry in manifest["modules"][0]["occurrences"])
    if len(entries) != 10 or any(entry["action"] != "materialize" or
                                entry["executionRole"] != "direct_executable"
                                for entry in entries):
        raise RuntimeError("Mathlib nested fixture classification changed")
    selected = shard.SelectedModule(
        module=module, compiled_module=corpus.compiled_module_name(module),
        source_path=source_path, source=source, occurrences=entries,
        materialize=entries, retain=(),
    )
    shard.verify_selected_classifications([selected], TIMEOUT)
    result = shard._module_result(selected, work, dylib, TIMEOUT)
    shard._validate_module_report(result, 0)
    if len(result["replacementRootIds"]) != 9 or result["occurrenceClassificationCounts"] != {
        "materialized": 9, "expected_failure": 0, "unobserved_executable": 0,
        "covered_by_ancestor": 1, "retained_syntax_data": 0,
    }:
        raise RuntimeError(f"Mathlib nested coverage changed: {result['occurrenceClassificationCounts']}")
    oracle = result["declarationOracle"]["report"]
    coverage = tuple(oracle[field] for field in (
        "stockDeclarationCount", "appliedDeclarationCount", "commonPublicDeclarationCount",
        "stockOnlyPrivateProofCount", "appliedOnlyPrivateProofCount", "checkedDeclarationCount",
    ))
    if coverage != (16, 16, 16, 0, 0, 16):
        raise RuntimeError(f"Mathlib nested declaration coverage changed: {coverage}")
    corpus.require_unchanged_hashes(
        "nested Mathlib source", {module: manifest["modules"][0]["sourceHash"]},
        {module: corpus.sha256(selected.source_path.read_bytes())},
    )
    print("boundary nested Mathlib Action: 9 roots, 1 covered call, semantic oracle and zero remaining: ok", flush=True)
    return result


def main() -> None:
    check_range_protocol()
    protocol_tests.validate_occurrence_protocol()
    protocol_tests.validate_shard_report_protocol()
    initial_environment = corpus.verify_environment()
    initial_hashes = corpus.implementation_hashes()
    with tempfile.TemporaryDirectory(prefix="boundary-nested-", dir=ROOT / ".lake") as raw_dir:
        work = Path(raw_dir)
        dylib = shard._query_dynamic_library(TIMEOUT, work)
        check_fixture(work, dylib)
        check_mathlib(work, dylib)
    if corpus.verify_environment() != initial_environment or corpus.implementation_hashes() != initial_hashes:
        raise RuntimeError("nested gate inputs changed during run")
    print("boundary nested range/coverage protocol: ok")


if __name__ == "__main__":
    main()
