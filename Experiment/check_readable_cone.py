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


if __name__ == "__main__":
    unittest.main()

