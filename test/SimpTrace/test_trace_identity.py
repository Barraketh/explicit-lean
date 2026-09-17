#!/usr/bin/env python3
"""Focused T9 producer regressions (run with ``python3 -B``)."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import tempfile

sys.path.insert(0, __import__("pathlib").Path(__file__).resolve().parent.as_posix())
from trace_identity import (find_sites, manifest, transform, transform_with_ledger,
                            validate_invocations, validate_source_args,
                            verify_transform)  # noqa: E402
from finalize_traces import finalize_paths  # noqa: E402


def rejects(records: list[dict]) -> None:
    try:
        validate_invocations(records)
    except ValueError:
        return
    raise AssertionError(f"accepted malformed invocation set: {records!r}")


def main() -> int:
    attributed = "@[simp] lemma p : True := by simp\n@[simp] lemma q : True := by simp\n"
    assert [s.callText for s in find_sites(attributed)] == ["simp", "simp"]
    same_line = "example : True := by simp [p]; simp [q]\n"
    sites = find_sites(same_line)
    assert [s.callText for s in sites] == ["simp [p]", "simp [q]"]
    assert sites[0].endChar < sites[1].startChar
    for source, call in (
        ("example : True := by simp -- TODO\n", "simp"),
        ("example : True := by simp only [p] -- TODO\n", "simp only [p]"),
        ("example : True := by simp /- block TODO -/\n", "simp"),
        ("example : True := by simp [p], -- trailing punctuation\n", "simp [p]"),
    ):
        found = find_sites(source)
        assert [s.callText for s in found] == [call]
        generated = transform(source, "CommentFixture")
        marker = '=>trace "test/SimpTrace/meas_out/CommentFixture_01.json"'
        assert marker in generated
        comment_word = "TODO" if "TODO" in source else "trailing"
        assert generated.index(marker) < generated.index(comment_word)
    quoted = 'example : True := by simp [show String from "-- not a comment"] -- TODO\n'
    assert find_sites(quoted)[0].callText.startswith("simp [show String")
    syntax_data = "example : True := by simp [show Syntax from `(foo -- data)] -- TODO\n"
    syntax_sites = find_sites(syntax_data)
    assert syntax_sites[0].callText.endswith("-- data)]")
    syntax_traced, syntax_ledger = transform_with_ledger(syntax_data, "BoundaryFixture")
    assert "=>trace \"test/SimpTrace/meas_out/BoundaryFixture_01.json\" -- TODO" in syntax_traced
    assert verify_transform(syntax_data, "BoundaryFixture", syntax_traced, syntax_sites) == syntax_ledger
    identical = "example : True := by simp [p]\nexample : True := by simp [p]\n"
    sites = find_sites(identical)
    assert len(sites) == 2 and sites[0].callText == sites[1].callText
    unicode = "-- λ header\nexample : True := by simp [p]\n"
    sites = find_sites(unicode)
    assert sites[0].startChar < sites[0].endChar
    traced, ledger = transform_with_ledger(unicode, "UnicodeFixture")
    assert "simp_trace" in traced
    assert verify_transform(unicode, "UnicodeFixture", traced, find_sites(unicode)) == ledger
    m = manifest("Mathlib/Test/UnicodeFixture.lean", unicode, sites)
    assert m["sites"][0]["callText"] == "simp [p]"
    validate_source_args(m, unicode)
    identity_source = "example : True := by simp [← foo, heq_comm (a := a), h]\n"
    identity_manifest = manifest("Mathlib/Test/Args.lean", identity_source,
                                 find_sites(identity_source))
    args = identity_manifest["sites"][0]["sourceArgs"]
    assert [a["argId"] for a in args] == [0, 1, 2]
    assert all(a["kind"] == "simp-lemma" for a in args)
    assert [a["head"] for a in args] == ["foo", "heq_comm", "h"]
    assert args[0]["direction"] == "rev"
    assert identity_source[args[1]["startChar"]:args[1]["endChar"]] == "heq_comm (a := a)"
    validate_source_args(identity_manifest, identity_source)
    unicode_source = "example : True := by simp [hα, ← «quoted lemma»]\n"
    unicode_args = manifest("Mathlib/Test/UnicodeArgs.lean", unicode_source,
                            find_sites(unicode_source))["sites"][0]["sourceArgs"]
    assert [a["head"] for a in unicode_args] == ["hα", "«quoted lemma»"]
    forged_manifest = json.loads(json.dumps(identity_manifest))
    forged_manifest["sites"][0]["sourceArgs"][1]["endChar"] += 1
    try:
        validate_source_args(forged_manifest, identity_source)
    except ValueError:
        pass
    else:
        raise AssertionError("accepted a source argument span outside its syntax")
    forged = traced.replace("=>trace", "-- =>trace", 1)
    try:
        verify_transform(unicode, "UnicodeFixture", forged, find_sites(unicode))
    except ValueError:
        pass
    else:
        raise AssertionError("accepted a commented-out trace clause")
    good = [{"invocation": 0, "invocations": 2},
            {"invocation": 1, "invocations": 2}]
    validate_invocations(good)
    rejects([{"invocation": 0, "invocations": 2}])
    rejects([{"invocation": 0, "invocations": 2},
             {"invocation": 0, "invocations": 2}])
    rejects([{"invocation": 2, "invocations": 2},
             {"invocation": 1, "invocations": 2}])
    with tempfile.TemporaryDirectory(prefix="trace-finalize-") as directory:
        root = pathlib.Path(directory)
        original = root / "source.lean"
        traced_path = root / "FixtureTraced.lean"
        manifest_path = root / "FixtureTraced.manifest.json"
        raw_dir, out_dir = root / "raw", root / "final"
        source = "example : True := by simp\n"
        original.write_text(source, encoding="utf-8")
        sites = find_sites(source)
        manifest_path.write_text(json.dumps(
            manifest("Fixture.lean", source, sites), sort_keys=True,
            separators=(",", ":")), encoding="utf-8")
        raw_dir.mkdir()
        # Explicit-path mode binds both the deterministic transform and raw
        # v1 call text to this run-local directory.
        traced_path.write_text(transform(source, "FixtureTraced", str(raw_dir)),
                                encoding="utf-8")
        raw = raw_dir / "FixtureTraced_01.json"
        raw.write_text(json.dumps({
                                   "schema": "simp-trace-v1",
                                   "call": f'simp_trace =>trace "{raw_dir}/FixtureTraced_01.json"',
                                   "occurrence": "7",
                                   "locations": []}, separators=(",", ":")), encoding="utf-8")
        before = raw.read_bytes()
        completed = subprocess.run(
            [sys.executable, str(pathlib.Path(__file__).with_name("finalize_traces.py")),
             "--traced-source", str(traced_path), "--manifest", str(manifest_path),
             "--source", str(original), "--raw-dir", str(raw_dir),
             "--out-dir", str(out_dir)], capture_output=True, text=True)
        assert completed.returncode == 0, completed.stderr
        assert raw.read_bytes() == before
        result = json.loads((out_dir / raw.name).read_text(encoding="utf-8"))
        assert result["schema"] == "simp-trace-v2"
        assert result["site"] == {"siteOrdinal": 0, "startChar": 21,
                                   "endChar": 25, "callText": "simp",
                                   "sourceArgs": []}
        assert result["invocation"] == 0 and result["invocations"] == 1
        wrong_stage = root / "wrong-stage"
        wrong_stage.mkdir()
        wrong_traced = wrong_stage / "FixtureTraced.lean"
        wrong_traced.write_text(transform(source, "FixtureTraced", str(root / "wrong-raw")),
                                 encoding="utf-8")
        try:
            finalize_paths(wrong_traced, manifest_path, original, raw_dir,
                           root / "wrong-final")
        except ValueError:
            pass
        else:
            raise AssertionError("accepted staged trace clauses rooted outside --raw-dir")
    print("OK: T9 attributes, comments, same-line, identical, Unicode, and ordinal regressions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
