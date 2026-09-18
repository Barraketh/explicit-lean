#!/usr/bin/env python3
"""Focused checks for the readable cone runner.

These checks exercise the source lexer, closure walk and artifact staging with
temporary files.  They intentionally do not require generated Mathlib source,
a Lake cache or a completed cone build.
"""

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

import run_readable_cone as cone


class ConeRunnerChecks(unittest.TestCase):
    def test_all_header_forms_and_comments(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            path = root / "Mathlib" / "A.lean"
            path.parent.mkdir(parents=True)
            path.write_text(
                """module
-- import Mathlib.Commented
/- nested /- public import Mathlib.AlsoCommented -/ -/
import Mathlib.Plain
meta import Mathlib.Meta
public import Mathlib.Public
public meta import Mathlib.PublicMeta
private import Mathlib.Private
private meta import Mathlib.PrivateMeta
@[doc \"public import Mathlib.InString\"] def x := 1
""",
                encoding="utf-8",
            )
            entries = cone.imports_in_source(root, "Mathlib.A")
            self.assertEqual(
                entries,
                [
                    ("import", "Mathlib.Plain"),
                    ("meta import", "Mathlib.Meta"),
                    ("public import", "Mathlib.Public"),
                    ("public meta import", "Mathlib.PublicMeta"),
                    ("private import", "Mathlib.Private"),
                    ("private meta import", "Mathlib.PrivateMeta"),
                ],
            )

    def test_stage_copies_only_module_families_and_rejects_missing(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            work = Path(raw)
            stock = work / "stock"
            translated = work / "translated"
            module = "Mathlib.A"
            source = stock / cone.module_relative(module)
            source.parent.mkdir(parents=True)
            source.with_suffix(".olean").write_bytes(b"olean")
            source.with_suffix(".ir").write_bytes(b"ir")
            (source.parent / "A.olean.server").write_bytes(b"server")
            (source.parent / "A.olean.private").write_bytes(b"private")
            (source.parent / "unrelated.olean").write_bytes(b"unrelated")
            report = cone.stage_artifacts(stock, translated, [module])
            self.assertEqual(len(report["files"]), 4)
            self.assertTrue((translated / "Mathlib" / "A.olean").is_file())
            self.assertFalse((translated / "Mathlib" / "unrelated.olean").exists())
            with self.assertRaises(cone.ConeFailure):
                cone.stage_artifacts(stock, translated / "second", ["Mathlib.Missing"])

    def test_reviewed_order_places_bridge_before_dependents(self) -> None:
        self.assertEqual(cone.BUILD_ORDER[:4], cone.TARGETS[:4])
        self.assertLess(cone.BUILD_ORDER.index(cone.BRIDGE), cone.BUILD_ORDER.index("Mathlib.Logic.IsEmpty.Basic"))
        self.assertEqual(cone.BUILD_ORDER[-1], "Mathlib.Data.Option.Basic")

    def test_stale_family_needs_fresh_compiler_output(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            work = Path(raw)
            source_root = work / "source"
            translated = work / "translated"
            run_dir = work / "run"
            source = source_root / cone.module_relative("Mathlib.A")
            source.parent.mkdir(parents=True)
            source.write_text("module\n", encoding="utf-8")
            translated.mkdir()
            output = translated / cone.module_relative("Mathlib.A", ".olean")
            output.parent.mkdir(parents=True)
            output.write_bytes(b"stale")
            output.with_suffix(".ir").write_bytes(b"stale-ir")
            output.parent.joinpath("A.olean.server").write_bytes(b"stale-server")
            imports = cone.ImportEnvironment(
                source_root, translated, work / "lean", work, (translated,), (), (), "", ""
            )

            with patch.object(
                cone, "run_pinned_lean", return_value=SimpleNamespace(returncode=0, stdout="noop")
            ):
                failed = cone._compile_module(imports, run_dir, "Mathlib.A")
            self.assertEqual(failed["status"], "failed")
            self.assertFalse(output.exists())
            self.assertEqual(len(failed["freshness"]["removedFamily"]), 3)

            output.write_bytes(b"stale-again")
            output.parent.joinpath("A.olean.server").write_bytes(b"stale-server-again")

            def write_output(*_args, **_kwargs):
                output.write_bytes(b"fresh")
                output.parent.joinpath("A.olean.server").write_bytes(b"fresh-server")
                return SimpleNamespace(returncode=0, stdout="wrote")

            with patch.object(cone, "run_pinned_lean", side_effect=write_output):
                passed = cone._compile_module(imports, run_dir, "Mathlib.A")
            self.assertEqual(passed["status"], "passed")
            self.assertTrue(passed["freshness"]["freshOlean"])
            self.assertEqual(len(passed["freshness"]["afterFamily"]), 2)

    def test_lint_can_account_for_unchanged_baseline_calls(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            work = Path(raw)
            generated = work / "generated"
            baseline = work / "baseline"
            for module in cone.TARGETS:
                generated_path = cone.source_path(generated, module)
                baseline_path = cone.source_path(baseline, module)
                generated_path.parent.mkdir(parents=True, exist_ok=True)
                baseline_path.parent.mkdir(parents=True, exist_ok=True)
                baseline_path.write_text("module\ndef unchanged := by simpa\n", encoding="utf-8")
                generated_path.write_text("module\ndef unchanged := by simpa\n", encoding="utf-8")
            result = cone.lint_targets(generated, baseline)
            self.assertEqual(result["status"], "passed")
            self.assertEqual(result["baselineFindings"], len(cone.TARGETS))
            self.assertEqual(result["introducedFindings"], 0)

            changed = cone.source_path(generated, cone.TARGETS[0])
            changed.write_text("module\ndef unchanged := by simpa\ndef added := by simp\n", encoding="utf-8")
            with self.assertRaisesRegex(cone.ConeFailure, "generated target source retains"):
                cone.lint_targets(generated, baseline)


if __name__ == "__main__":
    unittest.main()
