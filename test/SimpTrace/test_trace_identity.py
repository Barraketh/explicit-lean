#!/usr/bin/env python3
"""Focused T9 producer regressions (run with ``python3 -B``)."""

from __future__ import annotations

import sys

sys.path.insert(0, __import__("pathlib").Path(__file__).resolve().parent.as_posix())
from trace_identity import (find_sites, manifest, trace_clause_ordinals,
                            transform, validate_invocations)  # noqa: E402


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
    assert find_sites(syntax_data)[0].callText.startswith("simp [show Syntax")
    fake = "-- =>trace \"test/SimpTrace/meas_out/CommentFixture_99.json\"\n"
    assert trace_clause_ordinals(fake, "CommentFixture") == []
    identical = "example : True := by simp [p]\nexample : True := by simp [p]\n"
    sites = find_sites(identical)
    assert len(sites) == 2 and sites[0].callText == sites[1].callText
    unicode = "-- λ header\nexample : True := by simp [p]\n"
    sites = find_sites(unicode)
    assert sites[0].startChar < sites[0].endChar
    traced = transform(unicode, "UnicodeFixture")
    assert "simp_trace" in traced
    m = manifest("Mathlib/Test/UnicodeFixture.lean", unicode, sites)
    assert m["sites"][0]["callText"] == "simp [p]"
    good = [{"invocation": 0, "invocations": 2},
            {"invocation": 1, "invocations": 2}]
    validate_invocations(good)
    rejects([{"invocation": 0, "invocations": 2}])
    rejects([{"invocation": 0, "invocations": 2},
             {"invocation": 0, "invocations": 2}])
    rejects([{"invocation": 2, "invocations": 2},
             {"invocation": 1, "invocations": 2}])
    print("OK: T9 attributes, comments, same-line, identical, Unicode, and ordinal regressions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
