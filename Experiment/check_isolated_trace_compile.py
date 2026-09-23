#!/usr/bin/env python3
"""Focused tests for the stopped-trace isolated-compile harness."""

from __future__ import annotations

import json
import pathlib
import tempfile
import unittest

import isolated_trace_compile as isolated


class IsolatedTraceCompileTests(unittest.TestCase):
    def test_masks_theorem_and_lemma_bodies_but_not_computational_declarations(self) -> None:
        source = "lemma foo : True := by trivial\ntheorem baz : True := by trivial\n"
        raw = source.encode()
        lemma_end = raw.index(b"\n")
        lemma = {"kind": "lemma", "body": "by trivial", "start": 0,
                 "end": lemma_end, "command_source": source[:lemma_end]}
        theorem_start = lemma_end + 1
        theorem = {"kind": "Lean.Parser.Command.declaration", "body": "by trivial",
                   "start": theorem_start, "end": len(raw) - 1,
                   "command_source": source[theorem_start:].strip()}
        self.assertEqual(isolated._mask_body(source, lemma),
                         "lemma foo : True := by sorry")
        self.assertEqual(isolated._mask_body(source, theorem),
                         "theorem baz : True := by sorry")
        for command_source in (
            "def value : Nat := 2", "instance : Inhabited Unit := ⟨()⟩",
            "abbrev Alias := Nat", "example : True := by trivial",
        ):
            command = {"kind": "Lean.Parser.Command.declaration", "body": "by trivial",
                       "start": 0, "end": len(command_source),
                       "command_source": command_source}
            self.assertFalse(isolated._is_theorem_or_lemma(command))

    def test_doc_comment_and_attribute_do_not_hide_theorem_head(self) -> None:
        source = "/-- documentation -/\n@[simp]\ntheorem baz : True := by trivial"
        command = {"kind": "Lean.Parser.Command.declaration", "body": "by trivial",
                   "start": 0, "end": len(source), "command_source": source}
        self.assertTrue(isolated._is_theorem_or_lemma(command))
        self.assertEqual(isolated._mask_body(source, command),
                         "/-- documentation -/\n@[simp]\ntheorem baz : True := by sorry")

    def test_attribute_assignment_is_not_mistaken_for_proof_body(self) -> None:
        source = ("@[to_additive (attr := simp)]\n/-- docs -/\n"
                  "lemma baz : True := by trivial")
        body = source[source.index("simp)"):]
        command = {"kind": "lemma", "body": body, "start": 0,
                   "end": len(source), "command_source": source}
        self.assertIsNone(isolated._mask_body(source, command))

    def test_non_suffix_body_is_not_masked(self) -> None:
        source = "lemma foo : True := by trivial -- note\n"
        command = {"kind": "lemma", "body": "by trivial", "start": 0,
                   "end": len(source.encode()), "command_source": source}
        self.assertIsNone(isolated._mask_body(source, command))

    def test_embedded_raw_paths_are_authenticated_as_one_root(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "Trace_01.json").write_text(json.dumps({
                "call": 'simp_trace =>trace "/home/ubuntu/job/trace/raw/Trace_01.json"'}),
                encoding="utf-8")
            self.assertEqual(isolated._trace_root(root, "Trace"),
                "/home/ubuntu/job/trace/raw")

    def test_retry_filename_uses_global_site_ordinal_and_base_clause_path(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "Trace_12.1.json").write_text(json.dumps({
                "call": 'simp_trace =>trace "/home/ubuntu/job/trace/raw/Trace_12.json"'}),
                encoding="utf-8")
            self.assertEqual(isolated._trace_root(root, "Trace"),
                             "/home/ubuntu/job/trace/raw")

    def test_raw_filename_must_match_embedded_path(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "Trace_01.json").write_text(json.dumps({
                "call": 'simp_trace =>trace "/home/ubuntu/job/trace/raw/Other_01.json"'}),
                encoding="utf-8")
            with self.assertRaises(isolated.IsolatedError):
                isolated._trace_root(root, "Trace")

    def test_scratch_proof_holes_cannot_be_persisted(self) -> None:
        isolated._check_persisted_replacement("theorem safe : True := by trivial")
        isolated._check_persisted_replacement(None)
        for replacement in ("theorem bad : True := by sorry",
                            "lemma bad : True := by admit"):
            with self.assertRaises(isolated.IsolatedError):
                isolated._check_persisted_replacement(replacement)


if __name__ == "__main__":
    unittest.main()
