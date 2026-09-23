#!/usr/bin/env python3
"""Focused tests for the stopped-trace isolated-compile harness."""

from __future__ import annotations

import json
import os
import pathlib
import tempfile
import unittest

import isolated_trace_compile as isolated


class IsolatedTraceCompileTests(unittest.TestCase):
    def test_database_guard_accepts_only_single_link_private_worker_copies(self) -> None:
        with tempfile.TemporaryDirectory(dir=isolated.T77_RUN_ROOT) as directory:
            writable = pathlib.Path(directory) / "copy.sqlite3"
            writable.touch()
            self.assertEqual(isolated._writable_database(writable), writable.resolve())
            linked = pathlib.Path(directory) / "linked.sqlite3"
            try:
                os.link(writable, linked)
            except OSError as exc:
                self.skipTest(f"hard links unavailable: {exc}")
            with self.assertRaisesRegex(isolated.IsolatedError, "hard link"):
                isolated._writable_database(linked)
        with tempfile.NamedTemporaryFile() as outside:
            with self.assertRaisesRegex(isolated.IsolatedError, "approved private"):
                isolated._writable_database(pathlib.Path(outside.name))

    def test_empty_manifest_fails_before_database_open(self) -> None:
        import contextlib
        import io

        with tempfile.TemporaryDirectory(dir=isolated.T77_RUN_ROOT) as directory:
            root = pathlib.Path(directory)
            manifest = root / "empty.txt"
            manifest.write_text("", encoding="utf-8")
            database = root / "must-not-be-created.sqlite3"
            with contextlib.redirect_stderr(io.StringIO()):
                result = isolated.main([
                    "--database", str(database),
                    "--manifest", str(manifest),
                    "--artifacts-root", str(root / "missing-artifacts"),
                    "--scratch", str(root / "scratch"),
                ])
            self.assertEqual(result, 1)
            self.assertFalse(database.exists())

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

    def test_nested_named_argument_is_not_mistaken_for_theorem_body(self) -> None:
        source = ("@[simp]\nlemma eval_comp (f : σ → R) (i : σ) :\n"
                  "    (eval f).comp (toMvPolynomial (R := R) i) = expected := by trivial")
        body_start = source.index("(R := ") + len("(R := ")
        command = {"kind": "lemma", "body": source[body_start:], "start": 0,
                   "end": len(source.encode()), "command_source": source}
        self.assertIsNone(isolated._mask_body(source, command))

    def test_real_declaration_separator_after_named_argument_is_masked(self) -> None:
        source = ("lemma eval_comp (f : σ → R) (i : σ) :\n"
                  "    (eval f).comp (toMvPolynomial (R := R) i) = expected := by trivial")
        command = {"kind": "lemma", "body": "by trivial", "start": 0,
                   "end": len(source.encode()), "command_source": source}
        self.assertEqual(isolated._mask_body(source, command),
                         source[:-len("by trivial")] + "by sorry")

    def test_top_level_let_assignment_cannot_authenticate_a_wrong_body_span(self) -> None:
        source = "lemma foo : let x := Nat; x = x := by rfl"
        wrong_start = source.index("Nat")
        wrong_span = {"kind": "lemma", "body": source[wrong_start:], "start": 0,
                      "end": len(source), "command_source": source}
        self.assertIsNone(isolated._mask_body(source, wrong_span))

        correct_start = source.index("by rfl")
        correct_span = {"kind": "lemma", "body": source[correct_start:], "start": 0,
                        "end": len(source), "command_source": source}
        self.assertEqual(isolated._mask_body(source, correct_span),
                         source[:correct_start] + "by sorry")

    def test_declaration_separator_scan_ignores_nested_string_and_comment_assignments(self) -> None:
        source = ('lemma «foo:=bar» : (let s := "x := y"; True) '
                  '/- comment with := is not a separator -/ := by trivial')
        command = {"kind": "lemma", "body": "by trivial", "start": 0,
                   "end": len(source.encode()), "command_source": source}
        self.assertEqual(isolated._mask_body(source, command),
                         source.replace("by trivial", "by sorry"))

    def test_declaration_separator_scan_refuses_mismatched_delimiters(self) -> None:
        source = "lemma foo : (True] := by trivial"
        command = {"kind": "lemma", "body": "by trivial", "start": 0,
                   "end": len(source), "command_source": source}
        self.assertIsNone(isolated._mask_body(source, command))

    def test_empty_explicit_rw_path_has_separated_closer(self) -> None:
        source = ("lemma foo : True := by explicit_rw [eq_self at []] then exact True.intro\n"
                  "-- explicit_rw [ignored at []]\n"
                  "def note := \"explicit_rw [ignored at []]\"")
        expected = ("lemma foo : True := by explicit_rw [eq_self at [] ] then exact True.intro\n"
                    "-- explicit_rw [ignored at []]\n"
                    "def note := \"explicit_rw [ignored at []]\"")
        self.assertEqual(isolated._space_explicit_rw_empty_path_closers(source), expected)

    def test_explicit_retry_status_selection_is_manifest_and_audit_scoped(self) -> None:
        commands = [
            {"ordinal": 0, "status": "compile_failed"},
            {"ordinal": 1, "status": "compile_failed"},
            {"ordinal": 2, "status": "render_failed"},
            {"ordinal": 3, "status": "record_failed"},
            {"ordinal": 4, "status": "resource_failed"},
            {"ordinal": 5, "status": "success"},
        ]
        audited = {0, 2, 4, 5}
        self.assertEqual([row["ordinal"] for row in
                          isolated._select_target_rows(commands, audited)], [3])
        self.assertEqual([row["ordinal"] for row in isolated._select_target_rows(
            commands, audited, {"compile_failed", "render_failed", "resource_failed"})],
                         [0, 2, 4])

    def test_retry_archives_previous_audit_attempt(self) -> None:
        import sqlite3

        db = sqlite3.connect(":memory:")
        db.execute(isolated.AUDIT_SCHEMA)
        db.execute(isolated.AUDIT_HISTORY_SCHEMA)
        db.execute(
            "INSERT INTO isolated_trace_audit VALUES(?,?,?,?,?,?)",
            ("Mathlib.Test", 7, "compile_failed", "rendered", "old diagnostic", "old time"),
        )
        isolated._archive_prior_audit(db, "Mathlib.Test", 7)
        self.assertEqual(db.execute(
            "SELECT module_name,ordinal,result_status,trace_state,compile_detail,updated_at "
            "FROM isolated_trace_audit_history"
        ).fetchone(), ("Mathlib.Test", 7, "compile_failed", "rendered", "old diagnostic", "old time"))
        db.close()

    def test_term_extension_gate_refusal_is_persisted_without_success(self) -> None:
        import sqlite3

        db = sqlite3.connect(":memory:")
        db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,status TEXT,"
                   "replacement_text TEXT,error TEXT,PRIMARY KEY(module_name,ordinal))")
        db.execute("INSERT INTO simp_replacements VALUES('Mathlib.X',7,'record_failed',NULL,'old')")
        db.commit()
        command = {"ordinal": 7, "status": "record_failed"}
        result = isolated._persist_term_elaboration_gate_refusal(
            db, "Mathlib.X", [command], [command],
            'term-elaboration AST gate refused: [{"reason":"source_term_elab_attribute"}]',
        )
        self.assertEqual(result["termElaborationGate"], "refused")
        self.assertEqual(db.execute(
            "SELECT status,replacement_text,error FROM simp_replacements"
        ).fetchone(), ("render_failed", None,
                       'term-elaboration AST gate refused: [{"reason":"source_term_elab_attribute"}]'))
        self.assertEqual(db.execute(
            "SELECT result_status,trace_state FROM isolated_trace_audit"
        ).fetchone(), ("render_failed", "term_elab_gate_refused"))
        db.close()

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

    def test_existing_successes_are_validated_before_baseline_assembly(self) -> None:
        safe = {"ordinal": 2, "status": "success",
                "replacement": "theorem safe : True := by trivial"}
        self.assertEqual(isolated._existing_success_replacements([safe]),
                         {2: safe["replacement"]})
        for replacement in (None, "", " \n\t ",
                            "theorem bad : True := by sorry",
                            "lemma bad : True := by admit"):
            with self.subTest(replacement=replacement):
                row = {"ordinal": 9, "status": "success",
                       "replacement": replacement}
                with self.assertRaises(isolated.IsolatedError):
                    isolated._existing_success_replacements([row])


if __name__ == "__main__":
    unittest.main()
