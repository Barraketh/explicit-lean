#!/usr/bin/env python3
"""Focused regression checks for the module-scoped simp replacement worker."""

from __future__ import annotations

import hashlib
import pathlib
import sqlite3
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import simp_replacement_worker as W  # noqa: E402
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent / "pipeline"))
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "test" / "SimpTrace"))
import trace_identity as TI  # noqa: E402


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def test_manifest() -> None:
    with tempfile.TemporaryDirectory(prefix="simp-worker-manifest-") as directory:
        path = pathlib.Path(directory) / "modules.txt"
        path.write_text("Mathlib.A\n\nMathlib.B.C\n", encoding="utf-8")
        assert W.read_manifest(path) == ["Mathlib.A", "Mathlib.B.C"]
        for invalid in (" Mathlib.A\n", "Mathlib.A \n", "Mathlib.A\nMathlib.A\n",
                        "NotMathlib.A\n", "Mathlib...A\n"):
            path.write_text(invalid, encoding="utf-8")
            try:
                W.read_manifest(path)
            except W.WorkerError:
                pass
            else:
                raise AssertionError(f"accepted malformed module manifest: {invalid!r}")


def test_utf8_site_mapping() -> None:
    source = "-- λ before command\nexample : True := by simp [True.intro]\n"
    renderer_sites, trace_sites = W.align_sites(source)
    assert len(renderer_sites) == len(trace_sites) == 1
    command_start = len(source[:source.index("example")].encode("utf-8"))
    command_end = len(source.encode("utf-8"))
    command = {"ordinal": 7, "start": command_start, "end": command_end}
    assert W.command_for_site(source, [command], trace_sites[0]) == 7
    byte_start = len(source[:trace_sites[0].startChar].encode("utf-8"))
    assert byte_start > trace_sites[0].startChar
    assert W.byte_to_char(source, byte_start) == trace_sites[0].startChar
    assert source[trace_sites[0].startChar:trace_sites[0].endChar] == "simp [True.intro]"


def test_nested_tactic_contexts_and_non_targets() -> None:
    source = '''module
import Mathlib
@[simp] lemma attribute_only : True := True.intro
-- all_goals simp
/- any_goals simp -/
def quoted : String := "all_goals simp; try simp"
example : True := by all_goals simp
example : True → True := by
  intro
  simp
example : True := by
  all_goals
    simp
example : True := by any_goals
  simp only [True.intro]
example : True := by try simp
example : True := by repeat simp
example : True := by focus simp
example : True := by first | simp | exact True.intro
example : True := by
  first
  | any_goals
      simp
example : True ∧ True := by
  constructor
  case left => simp
  case right => exact True.intro
example : True ∧ True := by
  constructor
  · simp
  · exact True.intro
example : True := by simpa
example : (fun x : Nat => x) 0 = 0 := by dsimp
'''
    renderer_sites, trace_sites = W.align_sites(source)
    targets = [site for site in trace_sites if W.TARGET.match(site.callText)]
    assert len(targets) == 11, [site.callText for site in targets]
    assert [site.text for site in renderer_sites if W.TARGET.match(site.text)] == [
        site.callText for site in targets
    ]
    assert all("simpa" not in site.callText and not site.callText.startswith("dsimp")
               for site in targets)
    with tempfile.TemporaryDirectory(prefix="simp-context-syntax-",
                                     dir=W.ROOT / ".lake") as directory:
        scratch = pathlib.Path(directory)
        okay, detail, _ = W.compile_candidate(
            "Mathlib/Test/SimpContextSyntax.lean", source, scratch, 0,
        )
        assert okay, detail


def test_false_positive_is_atomic_noop() -> None:
    with tempfile.TemporaryDirectory(prefix="simp-worker-db-") as directory:
        root = pathlib.Path(directory)
        module = "Mathlib.Test.Noop"
        module_path = "Mathlib/Test/Noop.lean"
        source = "-- λ header\nlemma harmless : True := True.intro\n".encode("utf-8")
        command_start = len("-- λ header\n".encode("utf-8"))
        command_end = len(source)
        db_path = root / "worker.sqlite3"
        db = sqlite3.connect(db_path)
        db.executescript("""
            CREATE TABLE modules(name TEXT PRIMARY KEY,path TEXT NOT NULL UNIQUE,
                                 source BLOB NOT NULL,source_sha256 TEXT NOT NULL);
            CREATE TABLE commands(module_name TEXT NOT NULL,ordinal INTEGER NOT NULL,
                start_byte INTEGER NOT NULL,end_byte INTEGER NOT NULL,kind TEXT NOT NULL,
                source_sha256 TEXT NOT NULL,PRIMARY KEY(module_name,ordinal));
            CREATE TABLE simp_replacements(module_name TEXT NOT NULL,ordinal INTEGER NOT NULL,
                status TEXT NOT NULL DEFAULT 'pending',replacement_text TEXT,error TEXT,
                PRIMARY KEY(module_name,ordinal));
        """)
        db.execute("INSERT INTO modules VALUES (?,?,?,?)",
                   (module, module_path, source, digest(source)))
        db.execute("INSERT INTO commands VALUES (?,?,?,?,?,?)",
                   (module, 12, command_start, command_end, "lemma",
                    digest(source[command_start:command_end])))
        db.execute("INSERT INTO simp_replacements(module_name,ordinal) VALUES (?,?)",
                   (module, 12))
        db.commit()
        db.close()
        source_path = root / ".lake/packages/mathlib" / module_path
        source_path.parent.mkdir(parents=True)
        source_path.write_bytes(source)
        artifacts = root / "artifacts"
        artifacts.mkdir()
        old_root = W.ROOT
        W.ROOT = root
        try:
            connection = sqlite3.connect(db_path)
            result = W.process_module(connection, module, artifacts)
            assert result["status"] == "committed", result
            row = connection.execute(
                "SELECT status,replacement_text,error FROM simp_replacements "
                "WHERE module_name=? AND ordinal=?", (module, 12)
            ).fetchone()
            assert row == ("noop", None, None), row
            assert connection.execute("SELECT status FROM simp_replacements").fetchone()[0] == "noop"
            connection.close()
        finally:
            W.ROOT = old_root


def test_full_command_rewrite_omits_comment() -> None:
    source = "example : True := by simp [True.intro]; simp [True.intro]\n"
    renderer_sites, trace_sites = W.align_sites(source)
    assert len(trace_sites) == len(renderer_sites) == 2
    # This trace is sufficient to exercise the renderer's source output path;
    # source-site/trace authentication is independently tested by T9.
    traces = {site.siteOrdinal: [{"fixture": True}] for site in trace_sites}
    calls = iter(("explicit_rw [first at []]", "explicit_rw [second at []]"))
    original_renderer = W.replay.render_site
    W.replay.render_site = lambda *args, **kwargs: {
        "status": "rendered", "lines": [next(calls)],
    }
    try:
        rewritten, error = W.render_command(
            source, {"ordinal": 1, "start": 0, "end": len(source.encode("utf-8"))},
            list(zip(trace_sites, renderer_sites)), traces,
        )
    finally:
        W.replay.render_site = original_renderer
    assert error is None and rewritten is not None
    assert "explicit_rw [first at []]" in rewritten
    assert "explicit_rw [second at []]" in rewritten
    assert "simp" not in rewritten and "Original simp" not in rewritten


def test_selected_site_record_render_compile() -> None:
    W.ensure_prerequisites()
    source = "import Mathlib\nexample : True := by\n  all_goals simp\n"
    renderer_sites, trace_sites = W.align_sites(source)
    selected = [site for site in trace_sites if W.TARGET.match(site.callText)]
    assert len(selected) == 1
    with tempfile.TemporaryDirectory(prefix="simp-worker-e2e-",
                                     dir=W.ROOT / ".lake") as directory:
        scratch = pathlib.Path(directory)
        original = scratch / "Original.lean"
        original.write_text(source, encoding="utf-8")
        traces, _ = W.record_sites(source, "Mathlib/Test/SimpReplacementWorker.lean",
                                   original, selected, scratch)
        identity, grouped = W.replay.validate_identity(
            "Mathlib/Test/SimpReplacementWorker.lean", source, selected,
            [record for records in traces.values() for record in records],
        )
        assert identity["identity"] == "accepted"
        command = {"ordinal": 0, "start": 0, "end": len(source.encode("utf-8"))}
        rewritten, error = W.render_command(
            source, command, list(zip(selected,
                                      [W.as_renderer_site(s, renderer_sites) for s in selected])),
            grouped,
        )
        assert error is None and rewritten
        module_text = W.module_with_replacements(source, [command], {0: rewritten})
        okay, detail, _ = W.compile_candidate(
            "Mathlib/Test/SimpReplacementWorker.lean", module_text, scratch, 0,
        )
        assert okay, detail


def main() -> int:
    test_manifest()
    test_utf8_site_mapping()
    test_nested_tactic_contexts_and_non_targets()
    test_false_positive_is_atomic_noop()
    test_full_command_rewrite_omits_comment()
    test_selected_site_record_render_compile()
    print("check_simp_replacement_worker: PASS (6 focused checks)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
