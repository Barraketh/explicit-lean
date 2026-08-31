#!/usr/bin/env python3
"""Focused regressions for the August 31 boundary review findings."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import tempfile

import boundary_materialize_shard as shard
import check_simp_engine_boundary_scope as scope


ROOT = Path(__file__).resolve().parents[1]


def _expect_runtime_error(action, expected: str) -> None:
    try:
        action()
    except RuntimeError as error:
        if expected not in str(error):
            raise AssertionError(f"unexpected error: {error}") from error
    else:
        raise AssertionError(f"expected RuntimeError containing {expected!r}")


def check_manifest_cleanup_protection() -> None:
    """An input under the run subtree survives the preflight rejection."""
    shard.BOUNDARY_DEBUG_ROOT.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="review-fix-input-", dir=shard.BOUNDARY_DEBUG_ROOT
    ) as raw_directory:
        work = Path(raw_directory)
        manifest = work / "report-run" / "manifest.json"
        manifest.parent.mkdir(parents=True)
        manifest_bytes = b"{}\n"
        manifest.write_bytes(manifest_bytes)
        output = work / "report.json"
        output.write_bytes(b"previous report\n")
        output_tmp = output.with_name(output.name + ".tmp")
        output_tmp.write_bytes(b"previous temporary report\n")
        args = argparse.Namespace(
            manifest=str(manifest),
            output=str(output),
            module=[],
            expect_total=None,
            expect_materialize=None,
            timeout=5,
        )
        _expect_runtime_error(
            lambda: shard.run_shard(args), "input manifest overlaps a cleanup target"
        )
        assert manifest.read_bytes() == manifest_bytes
        assert output.read_bytes() == b"previous report\n"
        assert output_tmp.read_bytes() == b"previous temporary report\n"

    with tempfile.TemporaryDirectory(
        prefix="review-fix-temporary-", dir=shard.BOUNDARY_DEBUG_ROOT
    ) as raw_directory:
        work = Path(raw_directory)
        output = work / "report.json"
        manifest = output.with_name(output.name + ".tmp")
        manifest.write_bytes(b"{}\n")
        debug_root = shard.debug_root_for(output)
        _expect_runtime_error(
            lambda: shard.validate_cleanup_targets(manifest, output, debug_root),
            "input manifest overlaps a cleanup target",
        )
        assert manifest.exists()


def _scope_occurrence() -> dict[str, object]:
    """Compile and inspect a disposable copy of the antiquotation reproducer."""
    source = """module

import Mathlib

#check `(tactic| exact $(show Lean.TSyntax `term from by
  simp (config := { failIfUnchanged := false }) only
  trace \"ANTIQUOTED_TACTIC_EXECUTED\"
  exact ⟨Lean.Syntax.missing⟩))
"""
    with tempfile.TemporaryDirectory(prefix="review-fix-scope-", dir=ROOT / ".lake") as raw:
        fixture = Path(raw) / "QuotedAntiquotation.lean"
        fixture.write_text(source, encoding="utf-8")
        compiled = subprocess.run(
            ["lake", "env", "lean", str(fixture)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=180,
            check=True,
        )
        if "ANTIQUOTED_TACTIC_EXECUTED" not in compiled.stdout:
            raise AssertionError("antiquotation fixture did not execute its tactic")
        parsed = subprocess.run(
            [
                "lake",
                "env",
                "lean",
                "--run",
                "Experiment/SimpEngineBoundaryScope.lean",
                "Mathlib",
                str(fixture),
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=180,
            check=True,
        )
    records = [
        json.loads(line[len(scope.OCCURRENCE_MARKER) :])
        for line in parsed.stdout.splitlines()
        if line.startswith(scope.OCCURRENCE_MARKER)
    ]
    if len(records) != 1:
        raise AssertionError(f"expected one antiquotation occurrence, found {records}")
    return records[0]


def check_manifest_symlink_parent_resolution() -> None:
    """`link/..` must follow the link before resolving its parent directory."""
    with tempfile.TemporaryDirectory(prefix="review-fix-parent-", dir=shard.BOUNDARY_DEBUG_ROOT) as raw:
        work = Path(raw)
        nested = work / "real" / "nested"
        nested.mkdir(parents=True)
        (work / "link").symlink_to(nested, target_is_directory=True)
        (work / "real" / "manifest.json").write_text("[]")
        (work / "manifest.json").write_text("wrong lexical target")
        args = argparse.Namespace(
            manifest=str(work / "link" / ".." / "manifest.json"),
            output=str(work / "result.json"), module=[],
            expect_total=None, expect_materialize=None, timeout=5,
        )
        _expect_runtime_error(lambda: shard.run_shard(args), "manifest root must be an object")


def check_antiquotation_scope() -> None:
    occurrence = _scope_occurrence()
    result = scope.classify(occurrence, [])
    if result["action"] != "unresolved":
        raise AssertionError(
            "an executed antiquotation must require execution evidence, "
            f"found {result['executionRole']}/{result['declarationKind']}/{result['action']}"
        )
    ancestors = occurrence["ancestors"]
    assert isinstance(ancestors, list)
    if scope._quotation_context(ancestors) != "antiquotation":
        raise AssertionError(f"failed to identify antiquotation boundary: {ancestors}")
    nested_quotation = [
        "Lean.Parser.Tactic.quot",
        "term.pseudo.antiquot",
        "antiquotNestedExpr",
        "Lean.Parser.Tactic.quot",
        "Lean.Parser.Tactic.simp",
    ]
    if scope._quotation_context(nested_quotation) != "quotation":
        raise AssertionError("nested quotation inside an antiquotation was misclassified")
    nested_antiquotation = nested_quotation[:-1] + [
        "term.pseudo.antiquot",
        "antiquotNestedExpr",
        "Lean.Parser.Tactic.simp",
    ]
    if scope._quotation_context(nested_antiquotation) != "antiquotation":
        raise AssertionError("nested antiquotation boundary was misclassified")
    retained = dict(occurrence)
    retained["ancestors"] = ["Lean.Parser.Tactic.quot", "Lean.Parser.Tactic.simp"]
    retained_result = scope.classify(retained, [])
    if retained_result["action"] != "retain":
        raise AssertionError("a plain #check quotation should remain retained syntax")


def main() -> None:
    check_manifest_cleanup_protection()
    check_manifest_symlink_parent_resolution()
    check_antiquotation_scope()
    print("PASS: boundary review regressions")


if __name__ == "__main__":
    main()
