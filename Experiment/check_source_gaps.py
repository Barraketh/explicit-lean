#!/usr/bin/env python3
"""Regression checks for exact source preservation with repetitive output."""
from time import monotonic
from unittest.mock import patch

from boundary_protocol import assert_exact_source_preservation
import boundary_materialize_shard as materializer


def check(original, output, entries, lengths):
    # Passing the same corrupted bytes as expected is intentional: the gap
    # check must catch source corruption independently of renderer agreement.
    assert_exact_source_preservation(
        original, b"import Test.Generated\n" + output, entries,
        imported="Test.Generated", label="gap regression",
        expected_without_import=output, replacement_lengths=lengths,
    )


def rejected(original, output, entries, lengths):
    try:
        check(original, output, entries, lengths)
    except RuntimeError:
        return
    raise AssertionError("corrupted source or lengths accepted")


def instrumentation_checks():
    original = ("module\nprelude\n" + "-- repeated λ context\n" * 2000 +
                "def quoted := `(tactic| simp%$s only [show True from by simp])\n" +
                "-- middle α\nexample : True := by simp only [h]\n-- tail ω\n").encode()
    outer = b"simp%$s only [show True from by simp]"
    start = original.index(outer)
    inner = start + outer.rindex(b"simp")
    last = original.index(b"simp only [h]")
    entries = [
        dict(id=identifier, module="Test.lean", line=1, action="materialize",
             startByte=a, endByte=b, source=original[a:b].decode())
        for identifier, a, b in [("outer", start, start + len(outer)),
                                 ("inner", inner, inner + 4),
                                 ("last", last, last + len(b"simp only [h]"))]
    ]
    for mode in ("stock", "applied"):
        roots, _ = materializer.replacement_plan(original, entries, "test")
        tactic = materializer._recording_tactic(mode)
        output = materializer.inventory.rewrite_simp_heads(
            original, roots, lambda entry: f'{tactic} "{entry["id"]}"')
        generated = materializer.instrumented_source(original, roots, recording_mode=mode)
        lengths = materializer.instrumentation_replacement_lengths(
            original, list(reversed(entries)), recording_mode=mode)
        assert len(lengths) == 2
        assert f'{tactic}%$s "outer"'.encode() in output

        def verify(candidate, expected):
            materializer._assert_context_gaps(
                original, candidate, entries,
                imported="ExplicitLean.SimpEngine.Boundary", label="instrumentation",
                expected_without_import=expected, replacement_lengths=lengths)

        # The instrumentation path must not silently fall back to quadratic diff.
        with patch("boundary_protocol.difflib.SequenceMatcher",
                   side_effect=AssertionError("unexpected diff")):
            verify(generated, output)
            for marker in ("repeated λ", "middle α", "tail ω"):
                needle = marker.encode()
                bad_generated = generated.replace(needle, b"!" + needle[1:], 1)
                bad_expected = output.replace(needle, b"!" + needle[1:], 1)
                try:
                    verify(bad_generated, bad_expected)
                except RuntimeError:
                    pass
                else:
                    raise AssertionError("instrumentation accepted corrupted context")
    assert materializer.instrumentation_replacement_lengths(original, []) == []


def main():
    original = b"prefix simp middle simp suffix"
    entries = [dict(id="a", startByte=7, endByte=11),
               dict(id="b", startByte=19, endByte=23)]
    # The exact original source repeats inside a large replacement, which
    # defeats diff alignment and used to make validation take minutes.
    first = b"exact proof\n-- " + original * 40000
    second = b"skip\n-- Original simp: simp\n"
    output = b"prefix " + first + b" middle " + second + b" suffix"
    lengths = [len(first), len(second)]
    started = monotonic()
    check(original, output, entries, lengths)
    for position in (0, 7 + len(first) + 2, len(output) - 1):
        corrupted = output[:position] + b"!" + output[position + 1:]
        rejected(original, corrupted, entries, lengths)
    for bad_lengths in ([], [len(first)], [True, len(second)],
                        [-1, len(second)], [len(first) + 1, len(second)],
                        [len(first) + 1, len(second) - 1]):
        rejected(original, output, entries, bad_lengths)
    nested = [dict(id="outer", startByte=7, endByte=23),
              dict(id="inner", startByte=19, endByte=23)]
    check(original, b"prefix " + first + b" suffix", nested, [len(first)])
    check(original, original, [], [])
    rejected(original, original + b"!", [], [])
    instrumentation_checks()
    print(f"source gaps: repetition, independent corruption, lengths, nested roots: ok ({monotonic()-started:.3f}s)")


if __name__ == "__main__":
    main()
