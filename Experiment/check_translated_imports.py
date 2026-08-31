#!/usr/bin/env python3
"""Regression test for strict translated Mathlib import resolution.

The fixture builds two tiny modules with the pinned Lean binary.  It then
removes the translated dependency while leaving a deliberately conflicting
stock ``Mathlib.A.olean`` available.  The strict environment must reject both
the pre-compilation audit and the compiler fallback.
"""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch

import translated_imports
from translated_imports import build_import_environment, run_pinned_lean


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_ROOT = ROOT / ".lake" / "week-2026-08-31" / "translated-imports-check"


def write_fixture(root: Path, *, marker: int, include_a: bool = True) -> None:
    mathlib = root / "Mathlib"
    mathlib.mkdir(parents=True, exist_ok=True)
    if include_a:
        (mathlib / "A.lean").write_text(
            "module\npublic import Std\n\npublic def translatedMarker : Nat := "
            + str(marker)
            + "\npublic theorem translatedMarkerProof : translatedMarker = "
            + str(marker)
            + " := by rfl\n",
            encoding="utf-8",
        )
    (root / "Mathlib.lean").write_text(
        "module\npublic import Mathlib.A\n",
        encoding="utf-8",
    )
    # A compiled `def` is opaque across module boundaries here, so export a
    # proof made by `rfl`; B's theorem type then rejects the marker-99 stock A.
    (mathlib / "B.lean").write_text(
        "module\npublic import Std\nimport Mathlib.A\n\n"
        "theorem translatedProof : translatedMarker = 1 := translatedMarkerProof\n",
        encoding="utf-8",
    )


def compile_module(imports, source_root: Path, module: str) -> object:
    relative = Path(*module.split(".")).with_suffix(".lean")
    output = imports.translated_olean_root / relative.with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    return run_pinned_lean(
        imports,
        [
            "-R",
            str(source_root),
            "-o",
            str(output),
            str(source_root / relative),
        ],
    )


def adversarial_checks(work: Path, initial) -> None:
    def reject(action, detail: str) -> None:
        try:
            action()
        except RuntimeError as error:
            if detail not in str(error):
                raise RuntimeError(f"expected {detail!r}, got {error}") from error
        else:
            raise RuntimeError(f"expected rejection: {detail}")

    translated = work / "escape-oleans"
    translated.mkdir()
    stock = work / "aggregate-only-stock"
    stock.mkdir()
    (stock / "Mathlib.olean").write_bytes(b"must never be imported")
    values = {"LEAN_PATH": str(stock), "LEAN_SYSROOT": str(initial.lean_sysroot)}
    imports = build_import_environment(initial.source_root, translated, lake_env=values)
    if stock not in imports.excluded_roots or stock in imports.search_path:
        raise RuntimeError("aggregate-only stock root was retained")
    outside = work / "outside"
    outside.mkdir()
    (outside / "A.olean").write_bytes(b"must never be imported")
    (translated / "Mathlib").symlink_to(outside, target_is_directory=True)
    reject(lambda: imports.resolve_mathlib(["Mathlib.A"]), "escapes translated root")
    (translated / "Mathlib").unlink()
    (translated / "Mathlib").mkdir()
    (translated / "Mathlib" / "A.olean").symlink_to(outside / "A.olean")
    reject(lambda: imports.resolve_mathlib(["Mathlib.A"]), "escapes translated root")
    for version, commit in (
        (translated_imports.LEAN_VERSION + "0", translated_imports.LEAN_COMMIT),
        (translated_imports.LEAN_VERSION, translated_imports.LEAN_COMMIT + "a"),
    ):
        output = f"Lean (version {version}, test, commit {commit}, Release)"
        with patch.object(translated_imports, "run_process",
                          return_value=subprocess.CompletedProcess([], 0, output)):
            reject(lambda: build_import_environment(initial.source_root, translated, lake_env=values),
                   "unexpected pinned Lean binary identity")


def main() -> int:
    ARTIFACT_ROOT.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="translated-imports-", dir=ARTIFACT_ROOT) as raw:
        work = Path(raw)
        source = work / "source"
        translated = work / "translated-oleans"
        stock = work / "stock-oleans"
        write_fixture(source, marker=1)
        translated.mkdir()
        stock.mkdir()

        initial = build_import_environment(source, translated)
        adversarial_checks(work, initial)
        a_result = compile_module(initial, source, "Mathlib.A")
        if a_result.returncode != 0:
            raise RuntimeError(f"translated A failed:\n{a_result.stdout}")

        translated_imports = build_import_environment(source, translated)
        aggregate_result = compile_module(translated_imports, source, "Mathlib")
        if aggregate_result.returncode != 0:
            raise RuntimeError(f"translated Mathlib aggregate failed:\n{aggregate_result.stdout}")
        a_resolution = translated_imports.resolve_mathlib(["Mathlib.A", "Mathlib"])
        if not a_resolution["Mathlib.A"]["resolvedFromTranslatedRoot"]:
            raise RuntimeError(f"translated A did not resolve from translated root: {a_resolution}")
        if not a_resolution["Mathlib"]["resolvedFromTranslatedRoot"]:
            raise RuntimeError(f"translated Mathlib aggregate did not resolve from translated root: {a_resolution}")
        b_result = compile_module(translated_imports, source, "Mathlib.B")
        if b_result.returncode != 0:
            raise RuntimeError(f"translated B failed:\n{b_result.stdout}")
        deps_result = run_pinned_lean(
            translated_imports,
            [
                "--deps",
                "-R",
                str(source),
                str(source / "Mathlib" / "B.lean"),
            ],
        )
        translated_a_path = str(translated / "Mathlib" / "A.olean")
        if deps_result.returncode != 0 or translated_a_path not in deps_result.stdout:
            raise RuntimeError(
                "--deps did not report the translated dependency:\n"
                + deps_result.stdout
            )

        # Compile a conflicting stock A in a root that is intentionally fed to
        # the helper as if it were a Lake search root.  It must be excluded
        # solely because it contains Mathlib/, regardless of its position.
        write_fixture(source / "stock-source", marker=99, include_a=True)
        stock_source = source / "stock-source"
        stock_environment = build_import_environment(stock_source, stock)
        stock_result = compile_module(stock_environment, stock_source, "Mathlib.A")
        if stock_result.returncode != 0:
            raise RuntimeError(f"conflicting stock A fixture failed:\n{stock_result.stdout}")
        stock_b_result = compile_module(stock_environment, stock_source, "Mathlib.B")
        if stock_b_result.returncode == 0:
            raise RuntimeError(
                "B unexpectedly accepted the conflicting stock marker; translated proof was not checked"
            )
        lake_env = {
            "LEAN_PATH": str(stock) + ":" + ":".join(str(path) for path in initial.search_path),
            "LEAN_SYSROOT": str(initial.lean_sysroot),
        }
        missing_source = work / "missing-source"
        write_fixture(missing_source, marker=1, include_a=False)
        missing = build_import_environment(
            missing_source,
            translated,
            lake_env=lake_env,
        )
        if stock not in missing.excluded_roots:
            raise RuntimeError(f"conflicting stock root was not excluded: {missing.result()}")
        translated_a = translated / "Mathlib" / "A.olean"
        translated_a.unlink()
        try:
            missing.resolve_mathlib(["Mathlib.A"])
        except RuntimeError as error:
            if "translated olean is missing" not in str(error):
                raise RuntimeError(f"missing translated audit failed with wrong error: {error}") from error
        else:
            raise RuntimeError("missing translated A passed the pre-compilation audit")
        failed_b = compile_module(missing, missing_source, "Mathlib.B")
        if failed_b.returncode == 0:
            raise RuntimeError("B compiled through a stock Mathlib.A fallback")
        if not any(
            marker in failed_b.stdout
            for marker in (
                "unknown module prefix 'Mathlib.A'",
                "of module Mathlib.A does not exist",
            )
        ):
            raise RuntimeError(
                "missing translated A did not fail at import resolution; possible fallback:\n"
                + failed_b.stdout
            )
        report = {
            "kind": "translated_imports_check",
            "schema": 1,
            "status": "passed",
            "source": missing.result(),
            "translatedResolution": a_resolution,
            "excludedStockRoot": str(stock),
            "conflictingStockCompiler": {
                "returnCode": stock_b_result.returncode,
                "diagnosticTail": stock_b_result.stdout[-1000:],
            },
            "missingAudit": "rejected",
            "missingCompiler": {
                "returnCode": failed_b.returncode,
                "diagnosticTail": failed_b.stdout[-1000:],
            },
            "commands": [
                "pinned lean -R source -o translated-oleans/Mathlib/A.olean source/Mathlib/A.lean",
                "pinned lean -R source -o translated-oleans/Mathlib/B.olean source/Mathlib/B.lean",
                "pinned lean --deps -R source source/Mathlib/B.lean (reports imported oleans, including translated A)",
                "pinned lean -R stock-source -o stock-oleans/Mathlib/B.olean stock-source/Mathlib/B.lean (expected marker mismatch)",
                "pinned lean -R missing-source -o translated-oleans/Mathlib/B.olean missing-source/Mathlib/B.lean (expected failure)",
            ],
            "deps": deps_result.stdout.splitlines(),
        }
        print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
