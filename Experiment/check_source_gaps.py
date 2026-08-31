#!/usr/bin/env python3
"""Regression checks for exact source preservation with repetitive output."""
from time import monotonic

from boundary_protocol import assert_exact_source_preservation


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
    print(f"source gaps: repetition, independent corruption, lengths, nested roots: ok ({monotonic()-started:.3f}s)")


if __name__ == "__main__":
    main()
