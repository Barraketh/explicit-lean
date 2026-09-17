#!/usr/bin/env python3
"""Focused T9 producer regressions (run with ``python3 -B``)."""

from __future__ import annotations

import sys

sys.path.insert(0, __import__("pathlib").Path(__file__).resolve().parent.as_posix())
from trace_identity import find_sites, manifest, transform, validate_invocations  # noqa: E402


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
    print("OK: T9 attribute, same-line, identical, Unicode, and ordinal regressions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
