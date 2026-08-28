#!/usr/bin/env python3
"""Require the cloud reducer to accept total reports and reject coverage drift."""

from __future__ import annotations

from contextlib import redirect_stdout
import copy
import io
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile

import simp_engine_cloud as cloud
import simp_engine_inventory as inventory_helpers


MODULE = "Mathlib/Data/List/DropRight.lean"
OCCURRENCE = {
    "id": "cloud-reducer-fixture",
    "kind": "simp",
    "line": 1,
    "column": 0,
}


def write(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value), encoding="utf-8")


def reducer_args(root: Path, *, histogram_only: bool = False) -> SimpleNamespace:
    return SimpleNamespace(
        inventory=str(root / "inventory.json"),
        reports_dir=str(root / "reports"),
        output_dir=str(root / "final"),
        shard_count=2,
        histogram_only=histogram_only,
        allow_dirty=True,
    )


def main() -> None:
    compile_command = inventory_helpers.lean_command(
        inventory_helpers.MATHLIB / MODULE
    )
    for option in ("-DautoImplicit=false", "-DmaxSynthPendingDepth=3"):
        if option not in compile_command:
            raise RuntimeError(f"copied Mathlib compile omitted package option: {option}")
    for option in (
        "-Dweak.linter.unusedVariables=false",
        "-Dweak.linter.unusedSimpArgs=false",
        "-Dweak.linter.unreachableTactic=false",
    ):
        if option not in compile_command:
            raise RuntimeError(f"copied Mathlib compile used a strict linter option: {option}")
    if cloud.module_shard(MODULE, 64) != 50:
        raise RuntimeError("stable shard assignment changed")
    combined_deferred = {
        "subjects": [{
            "deferred": {"simprocAndCustomDischarger": {
                "name": [["str", "test"]], "phase": "post"
            }},
            "simprocs": {"dictionary": [{}], "order": [0]},
        }]
    }
    if cloud.deferred_reasons(combined_deferred) != {
        "simproc", "custom_discharger"
    }:
        raise RuntimeError("combined deferred reasons were not preserved")
    simproc_certificate = {
        "subjects": [{
            "simprocs": {
                "dictionary": [{
                    "name": [["str", "Nat"], ["str", "reduceAdd"]],
                    "phase": "post",
                    "stepDisposition": "continueSome",
                    "definitional": False,
                    "procedureKind": "dsimp",
                    "numExtraArgs": 1,
                    "executed": True,
                    "proofPresent": False,
                    "cache": True,
                    "inputFingerprint": "input",
                    "outputFingerprint": "output",
                    "outputChanged": True,
                    "outputSize": {
                        "treeNodes": 9,
                        "treeNodesCapped": False,
                        "dagNodes": 6,
                    },
                }, {
                    "name": [["str", "unusedSimproc"]],
                    "phase": "post",
                    "stepDisposition": "continueNone",
                    "definitional": False,
                    "procedureKind": "simp",
                    "numExtraArgs": 0,
                    "executed": True,
                    "proofPresent": False,
                    "cache": None,
                    "inputFingerprint": "unused-input",
                    "outputFingerprint": "unused-input",
                    "outputChanged": False,
                    "outputSize": None,
                }],
                "order": [0, 0, 1],
            },
        }],
    }
    simproc_summary = cloud.certificate_simproc_summary(simproc_certificate)
    if len(simproc_summary) != 1 or simproc_summary[0]["usedInvocations"] != 2 \
            or simproc_summary[0]["executionCount"] != 1 \
            or simproc_summary[0]["resultTreeSizeCounts"] != {"9": 2}:
        raise RuntimeError(f"simproc trace histogram changed: {simproc_summary!r}")
    size_summary = cloud.size_statistics({"3": 1, "9": 2})
    if size_summary["mean"] != 7 or size_summary["p50"] != 9 \
            or size_summary["p90"] != 9:
        raise RuntimeError(f"simproc result-size statistics changed: {size_summary!r}")
    mixed_executions = [
        {"deferredReasons": []},
        {"deferredReasons": ["simproc"]},
    ]
    if cloud.classify_occurrence_executions(mixed_executions, 0) != "deferred_simproc":
        raise RuntimeError("mixed replayable/simproc executions were not deferred as one occurrence")
    if cloud.classify_occurrence_executions(
        [{"deferredReasons": []}, {"deferredReasons": []}], 0
    ) is not None:
        raise RuntimeError("fully replayable executions were not selected for materialization")
    if cloud.module_has_failure({"errors": [], "occurrences": [{
        "terminal": "materialized"
    }]}):
        raise RuntimeError("accepted terminal was classified as a module failure")
    if not cloud.module_has_failure({"errors": ["recording_failure"]}):
        raise RuntimeError("module error did not stop the diagnostic batch")
    if not cloud.compile_exhausted_capacity(137) or not cloud.compile_exhausted_capacity(-9):
        raise RuntimeError("worker memory exhaustion was not classified as capacity")
    if cloud.compile_exhausted_capacity(1):
        raise RuntimeError("semantic compile failure was misclassified as capacity")
    nested_source = b"by\n  simp [show True from by simp]\n"
    outer_start = nested_source.index(b"simp")
    inner_start = nested_source.index(b"simp", outer_start + 4)
    nested_entries = [
        {
            "id": "outer",
            "module": "Nested.lean",
            "line": 2,
            "startByte": outer_start,
            "endByte": len(nested_source) - 1,
            "source": nested_source[outer_start:-1].decode(),
        },
        {
            "id": "inner",
            "module": "Nested.lean",
            "line": 2,
            "startByte": inner_start,
            "endByte": inner_start + 4,
            "source": "simp",
        },
    ]
    rewritten = inventory_helpers.rewrite_simp_heads(
        nested_source,
        nested_entries,
        lambda entry: f"record-{entry['id']}",
    )
    if rewritten != b"by\n  record-outer [show True from by record-inner]\n":
        raise RuntimeError(f"nested occurrence rewrite did not compose: {rewritten!r}")
    quoted_source = b"`(tactic| simp%$s only [example])"
    quoted_start = quoted_source.index(b"simp")
    quoted_entry = {
        "id": "quoted",
        "module": "Quoted.lean",
        "line": 1,
        "startByte": quoted_start,
        "endByte": len(quoted_source) - 1,
        "source": quoted_source[quoted_start:-1].decode(),
    }
    quoted_rewritten = inventory_helpers.rewrite_simp_heads(
        quoted_source,
        [quoted_entry],
        lambda _entry: 'simp_engine_source_recording "id" "directory"',
    )
    expected_quoted = (
        b'`(tactic| simp_engine_source_recording%$s "id" "directory" only [example])'
    )
    if quoted_rewritten != expected_quoted:
        raise RuntimeError(
            "quoted tactic-head antiquotation was not preserved: "
            f"{quoted_rewritten!r}"
        )
    non_bmp = inventory_helpers.lean_string_array_source(
        ['{"scalar":"𝕜"}'], parent_column=2
    )
    if "𝕜" not in non_bmp or "\\ud835" in non_bmp.lower():
        raise RuntimeError(f"Lean string source used a UTF-16 surrogate escape: {non_bmp!r}")
    if "#[" in non_bmp or "Array.empty" not in non_bmp or "|>.push" not in non_bmp:
        raise RuntimeError(f"Lean string source depends on local list notation: {non_bmp!r}")
    commit = cloud.current_commit()
    mathlib_commit = cloud.mathlib_commit()
    inventory = {
        "reportSchema": cloud.REPORT_SCHEMA,
        "kind": "simp_engine_inventory",
        "commit": commit,
        "mathlibCommit": mathlib_commit,
        "engine": cloud.ENGINE_ID,
        "moduleFileCount": 1,
        "inventoriedModuleCount": 1,
        "occurrenceCount": 1,
        "modules": [{
            "module": MODULE,
            "sourceHash": "source-hash",
            "occurrences": [OCCURRENCE],
        }],
    }
    occurrence = {
        **OCCURRENCE,
        "successfulExecutions": 1,
        "unsuccessfulExecutions": 0,
        "replayedExecutions": 1,
        "deferredReasons": [],
        "certificates": [{
            "sha256": "certificate-hash",
            "initialState": {"goalCount": 1},
            "finalState": {"goalCount": 0},
            "deferredReasons": [],
        }],
        "terminal": "materialized",
    }
    assigned = cloud.module_shard(MODULE, 2)
    reports = []
    for index in range(2):
        reports.append({
            "reportSchema": cloud.REPORT_SCHEMA,
            "kind": "simp_engine_shard",
            "commit": commit,
            "mathlibCommit": mathlib_commit,
            "engine": cloud.ENGINE_ID,
            "shardIndex": index,
            "shardCount": 2,
            "complete": True,
            "assignedModuleCount": 1 if index == assigned else 0,
            "harnessErrors": [],
            "simprocHistogram": [],
            "modules": [] if index != assigned else [{
                "module": MODULE,
                "sourceHash": "source-hash",
                "recording": {
                    "exitCode": 0,
                    "successfulExecutions": 1,
                    "unsuccessfulExecutions": 0,
                },
                "materialization": {
                    "exitCode": 0,
                    "expectedExecutions": 1,
                    "actualExecutions": 1,
                },
                "occurrences": [occurrence],
                "errors": [],
            }],
        })
    with tempfile.TemporaryDirectory(prefix="simp-engine-cloud-") as temporary:
        root = Path(temporary)
        write(root / "inventory.json", inventory)
        for report in reports:
            write(root / "reports" / f"shard-{report['shardIndex']:04d}.json", report)
        with redirect_stdout(io.StringIO()):
            if cloud.reduce_reports(reducer_args(root)) != 0:
                raise RuntimeError("total synthetic cloud report was rejected")

        committed_simproc = copy.deepcopy(reports[assigned])
        committed_simproc["modules"][0]["occurrences"][0]["simprocs"] = simproc_summary
        committed_simproc["simprocHistogram"] = cloud.simproc_histogram_for_modules(
            committed_simproc["modules"]
        )
        write(root / "reports" / f"shard-{assigned:04d}.json", committed_simproc)
        with redirect_stdout(io.StringIO()):
            if cloud.reduce_reports(reducer_args(root)) != 0:
                raise RuntimeError("committed simproc histogram without deferral was rejected")
        summary = json.loads(
            (root / "final" / "simp-engine-closure.json").read_text(encoding="utf-8")
        )
        if summary["failureCount"] != 0 \
                or summary["simprocHistogram"][0]["usedInvocations"] != 2:
            raise RuntimeError("committed simproc histogram was not preserved")

        histogram_reports = copy.deepcopy(reports)
        for report in histogram_reports:
            report["kind"] = "simp_engine_histogram_shard"
        histogram_module = histogram_reports[assigned]["modules"][0]
        histogram_module["materialization"] = None
        histogram_occurrence = histogram_module["occurrences"][0]
        histogram_occurrence["terminal"] = "recorded"
        histogram_occurrence["replayedExecutions"] = 0
        histogram_occurrence["simprocs"] = simproc_summary
        histogram_reports[assigned]["simprocHistogram"] = cloud.simproc_histogram_for_modules(
            histogram_reports[assigned]["modules"]
        )
        for report in histogram_reports:
            write(root / "reports" / f"shard-{report['shardIndex']:04d}.json", report)
        with redirect_stdout(io.StringIO()):
            if cloud.reduce_reports(
                reducer_args(root, histogram_only=True)
            ) != 0:
                raise RuntimeError("record-only histogram report was rejected")
        summary = json.loads(
            (root / "final" / "simp-engine-closure.json").read_text(encoding="utf-8")
        )
        if summary["failureCount"] != 0 \
                or summary["kind"] != "simp_engine_histogram_closure" \
                or not summary.get("histogramOnly") \
                or summary["terminalCounts"] != {"recorded": 1} \
                or summary["simprocHistogram"][0]["usedInvocations"] != 2:
            raise RuntimeError("record-only histogram closure was not preserved")

        mixed_histogram_reports = copy.deepcopy(histogram_reports)
        mixed_module = mixed_histogram_reports[assigned]["modules"][0]
        mixed_occurrence = mixed_module["occurrences"][0]
        mixed_occurrence["unsuccessfulExecutions"] = 2
        mixed_module["recording"]["unsuccessfulExecutions"] = 2
        write(
            root / "reports" / f"shard-{assigned:04d}.json",
            mixed_histogram_reports[assigned],
        )
        with redirect_stdout(io.StringIO()):
            if cloud.reduce_reports(
                reducer_args(root, histogram_only=True)
            ) != 0:
                raise RuntimeError(
                    "record-only histogram rejected a successfully recorded occurrence "
                    "with additional unsuccessful attempts"
                )
        summary = json.loads(
            (root / "final" / "simp-engine-closure.json").read_text(encoding="utf-8")
        )
        if summary["failureCount"] != 0 \
                or summary["successfulExecutions"] != 1 \
                or summary["unsuccessfulExecutions"] != 2:
            raise RuntimeError("mixed-attempt histogram counts were not preserved")
        write(
            root / "reports" / f"shard-{assigned:04d}.json",
            histogram_reports[assigned],
        )
        with redirect_stdout(io.StringIO()):
            if cloud.reduce_reports(reducer_args(root)) == 0:
                raise RuntimeError("normal reducer accepted record-only reports")

        for report in reports:
            write(root / "reports" / f"shard-{report['shardIndex']:04d}.json", report)
        mutated = copy.deepcopy(reports[assigned])
        mutated["modules"][0]["occurrences"][0]["replayedExecutions"] = 0
        write(root / "reports" / f"shard-{assigned:04d}.json", mutated)
        with redirect_stdout(io.StringIO()):
            if cloud.reduce_reports(reducer_args(root)) == 0:
                raise RuntimeError("replay-count mutation was accepted")
        summary = json.loads(
            (root / "final" / "simp-engine-closure.json").read_text(encoding="utf-8")
        )
        if not any(
            failure.startswith("materialized_execution_mismatch:")
            for failure in summary["failures"]
        ):
            raise RuntimeError("replay-count mutation had the wrong diagnostic")

        (root / "reports" / "shard-0001.json").unlink()
        with redirect_stdout(io.StringIO()):
            if cloud.reduce_reports(reducer_args(root)) == 0:
                raise RuntimeError("missing shard was accepted")
    print(
        "schema-27 cloud harness: package options, simproc histograms, and "
        "nested/quoted rewrites preserved, "
        "total report accepted, mutations rejected: ok"
    )


if __name__ == "__main__":
    main()
