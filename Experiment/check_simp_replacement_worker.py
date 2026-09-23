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
/- decoy @[ without a closing bracket
-/
example : True := by simp
/- lead -/ example : True := by simp
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
    assert len(targets) == 13, [site.callText for site in targets]
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
    canonical_sites = W._canonical_source_site_envelopes(source)
    traces = {site.siteOrdinal: [{"fixture": True,
                                  "site": canonical_sites[site.siteOrdinal] }]
              for site in trace_sites}
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


def _unicode_source_argument_fixture():
    source = "-- λ before command\nexample : True := by simp [← True.intro]\n"
    renderer_sites, trace_sites = W.align_sites(source)
    assert len(trace_sites) == len(renderer_sites) == 1
    ti_site, renderer_site = trace_sites[0], renderer_sites[0]
    command_start_char = source.index("example")
    command = {
        "ordinal": 4,
        "start": len(source[:command_start_char].encode("utf-8")),
        "end": len(source.encode("utf-8")),
    }
    canonical_site = W._canonical_source_site_envelopes(source)[ti_site.siteOrdinal]
    source_arg = dict(canonical_site["sourceArgs"][0])

    def invocation(ordinal: int = 0, total: int = 1) -> dict:
        return {
            "schema": "simp-trace-v2",
            "modulePath": "Mathlib/Test/UnicodeSourceArgs.lean",
            "site": {**canonical_site,
                     "sourceArgs": [dict(source_arg)]},
            "invocation": ordinal,
            "invocations": total,
            "locations": [{
                "loc": "goal",
                "steps": [{
                    "kind": "rw", "pos": [], "name": "True.intro", "dir": "rev",
                    "side": [], "args": [],
                    "derivation": {
                        "origin": "decl:lemma", "preprocess": ["direct_eq"],
                        "redex": [], "extraArgs": 0, "binders": [],
                        "discharge": [], "source": "simp-argument", "argId": 0,
                    },
                }],
            }],
        }

    return source, command, ti_site, renderer_site, source_arg, invocation


def test_render_command_rebases_unicode_source_arg_and_preserves_direction() -> None:
    source, command, ti_site, renderer_site, source_arg, invocation = \
        _unicode_source_argument_fixture()
    original = invocation()
    absolute_span = (source_arg["startChar"], source_arg["endChar"])
    command_start_char = W.byte_to_char(source, command["start"])
    command_end_char = W.byte_to_char(source, command["end"])
    command_text = source[command_start_char:command_end_char]
    # Recorder coordinates are authenticated module-relative Unicode scalar
    # offsets. Passing them straight to the command-local renderer reproduces
    # the historical failure instead of guessing an argument from its text.
    unrebased = W.replay.render_site(
        W.local_site(renderer_site, source, command_start_char, 0),
        original,
        command_text,
        include_original_comment=False,
        use_manual_overrides=False,
    )
    assert unrebased["status"] == "render_failed:bad_source_span", unrebased
    rewritten, error = W.render_command(
        source, command, [(ti_site, renderer_site)],
        {ti_site.siteOrdinal: [original]},
    )
    assert error is None and rewritten is not None, error
    assert "← True.intro at []" in rewritten, rewritten
    assert (source_arg["startChar"], source_arg["endChar"]) == absolute_span
    assert (original["site"]["sourceArgs"][0]["startChar"],
            original["site"]["sourceArgs"][0]["endChar"]) == absolute_span


def test_render_command_rebases_every_invocation_without_mutating_evidence() -> None:
    source, command, ti_site, renderer_site, source_arg, invocation = \
        _unicode_source_argument_fixture()
    original_records = [invocation(0, 2), invocation(1, 2)]
    absolute_span = (source_arg["startChar"], source_arg["endChar"])
    command_start_char = W.byte_to_char(source, command["start"])
    seen = []
    original_renderer = W.replay.render_site

    def capture_renderer(_site, trace, *_args, **_kwargs):
        seen.append(trace)
        return {"status": "rendered", "lines": ["explicit_rw [True.intro at []]"]}

    W.replay.render_site = capture_renderer
    try:
        rewritten, error = W.render_command(
            source, command, [(ti_site, renderer_site)],
            {ti_site.siteOrdinal: original_records},
        )
    finally:
        W.replay.render_site = original_renderer
    assert error is None and rewritten is not None, error
    assert len(seen) == 1 and len(seen[0]) == 2
    for ordinal, localized in enumerate(seen[0]):
        arg = localized["site"]["sourceArgs"][0]
        assert (arg["startChar"], arg["endChar"]) == (
            absolute_span[0] - command_start_char,
            absolute_span[1] - command_start_char,
        )
        assert (localized["invocation"], localized["invocations"]) == (ordinal, 2)
        assert (arg["direction"], arg["head"], arg["kind"]) == (
            "rev", "True.intro", "simp-lemma")
    for original in original_records:
        arg = original["site"]["sourceArgs"][0]
        assert (arg["startChar"], arg["endChar"]) == absolute_span

    wrong_second_invocation = invocation(1, 2)
    wrong_second_invocation["site"]["sourceArgs"][0]["startChar"] += 1
    rewritten, error = W.render_command(
        source, command, [(ti_site, renderer_site)],
        {ti_site.siteOrdinal: [invocation(0, 2), wrong_second_invocation]},
    )
    assert rewritten is None and error and "canonical T22" in error, (rewritten, error)


def test_render_command_rejects_inbounds_wrong_argument_identity() -> None:
    module_path = "Mathlib/Test/WrongSourceArg.lean"
    source = "-- λ before command\nexample : True := by simp [foo, bar]\n"
    renderer_sites, trace_sites = W.align_sites(source)
    assert len(trace_sites) == len(renderer_sites) == 1
    ti_site, renderer_site = trace_sites[0], renderer_sites[0]
    canonical_site = W._canonical_source_site_envelopes(source)[ti_site.siteOrdinal]
    assert len(canonical_site["sourceArgs"]) == 2
    wrong_site = {**canonical_site,
                  "sourceArgs": [dict(arg) for arg in canonical_site["sourceArgs"]]}
    second_arg = wrong_site["sourceArgs"][1]
    wrong_site["sourceArgs"][0]["startChar"] = second_arg["startChar"]
    wrong_site["sourceArgs"][0]["endChar"] = second_arg["endChar"]
    command_start_char = source.index("example")
    command = {
        "ordinal": 8,
        "start": len(source[:command_start_char].encode("utf-8")),
        "end": len(source.encode("utf-8")),
    }
    record = {
        "schema": "simp-trace-v2", "modulePath": module_path,
        "site": wrong_site, "occurrence": "fixture",
        "invocation": 0, "invocations": 1, "locations": [],
    }
    # This is precisely the gap: identity validates the site shell but ignores
    # sourceArgs, so the renderer's canonical T22 check must reject it.
    identity, _ = W.replay.validate_identity(module_path, source, [ti_site], [record])
    assert identity["identity"] == "accepted", identity
    rewritten, error = W.render_command(
        source, command, [(ti_site, renderer_site)], {ti_site.siteOrdinal: [record]}
    )
    assert rewritten is None and error and "canonical T22" in error, (rewritten, error)


def test_render_command_rejects_malformed_and_out_of_command_source_spans() -> None:
    source, command, ti_site, renderer_site, source_arg, invocation = \
        _unicode_source_argument_fixture()
    command_start_char = W.byte_to_char(source, command["start"])
    command_end_char = W.byte_to_char(source, command["end"])
    invalid_spans = [
        (True, source_arg["endChar"]),
        (source_arg["startChar"], "not-an-integer"),
        (command_start_char - 1, source_arg["endChar"]),
        (source_arg["startChar"], command_end_char + 1),
        (source_arg["endChar"], source_arg["startChar"]),
    ]
    for start, end in invalid_spans:
        record = invocation()
        record["site"]["sourceArgs"][0]["startChar"] = start
        record["site"]["sourceArgs"][0]["endChar"] = end
        rewritten, error = W.render_command(
            source, command, [(ti_site, renderer_site)],
            {ti_site.siteOrdinal: [record]},
        )
        assert (rewritten is None and error and
                ("sourceArgs[0]" in error or "canonical T22" in error)), (
                    start, end, rewritten, error)


def test_selected_site_record_render_compile() -> None:
    W.ensure_prerequisites()
    source = """import Mathlib
/- decoy @[ without a closing bracket
-/
/- lead -/ example : True := by simp
example (n : Nat) : n + 0 = n := by
  simp only [
    Nat.add_zero, /- [ decoy /- ] -/ -/
  ] <;> rfl
example (n : Nat) : n + 0 = n := by
  simp [
    Nat.add_zero
  ] <;> rfl
"""
    renderer_sites, trace_sites = W.align_sites(source)
    selected = [site for site in trace_sites if W.TARGET.match(site.callText)]
    assert len(selected) == 3
    assert [site.callText.splitlines()[0] for site in selected] == [
        "simp", "simp only [", "simp [",
    ]
    assert all("<;> rfl" not in site.callText for site in selected[1:])
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


def test_leading_block_comment_candidate_is_not_noop() -> None:
    """A comment before a declaration must not hide its queued simp site."""
    W.ensure_prerequisites()
    mathlib_root = W.ROOT / ".lake" / "packages" / "mathlib"
    mathlib_modules = mathlib_root / "Mathlib"
    source = b"import Mathlib\n/- lead -/ example : True := by simp\n"
    with tempfile.TemporaryDirectory(prefix="T62LeadingComment", dir=mathlib_modules) as module_dir:
        module_root = pathlib.Path(module_dir)
        module_path = pathlib.PurePosixPath(module_root.relative_to(mathlib_root)) / "Fixture.lean"
        module_name = "Mathlib." + ".".join(module_path.with_suffix("").parts[1:])
        source_path = module_root / "Fixture.lean"
        source_path.write_bytes(source)
        with tempfile.TemporaryDirectory(prefix="simp-leading-comment-db-") as tmp:
            root = pathlib.Path(tmp)
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
                       (module_name, str(module_path), source, digest(source)))
            db.execute("INSERT INTO commands VALUES (?,?,?,?,?,?)",
                       (module_name, 0, 0, len(source), "example", digest(source)))
            db.execute("INSERT INTO simp_replacements(module_name,ordinal) VALUES (?,?)",
                       (module_name, 0))
            db.commit()
            artifacts = root / "artifacts"
            artifacts.mkdir()
            result = W.process_module(db, module_name, artifacts)
            row = db.execute(
                "SELECT status,replacement_text,error FROM simp_replacements "
                "WHERE module_name=? AND ordinal=0", (module_name,),
            ).fetchone()
            assert result["status"] == "committed", result
            assert row[0] != "noop", row
            db.close()


def main() -> int:
    test_manifest()
    test_utf8_site_mapping()
    test_nested_tactic_contexts_and_non_targets()
    test_false_positive_is_atomic_noop()
    test_full_command_rewrite_omits_comment()
    test_render_command_rebases_unicode_source_arg_and_preserves_direction()
    test_render_command_rebases_every_invocation_without_mutating_evidence()
    test_render_command_rejects_inbounds_wrong_argument_identity()
    test_render_command_rejects_malformed_and_out_of_command_source_spans()
    test_selected_site_record_render_compile()
    test_leading_block_comment_candidate_is_not_noop()
    print("check_simp_replacement_worker: PASS (11 focused checks)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
