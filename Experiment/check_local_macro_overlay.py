#!/usr/bin/env python3
"""Pure-Python fixtures for the authenticated local-macro lowering."""

from __future__ import annotations

import hashlib
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import local_macro_overlay as overlay
import simp_engine_inventory as inventory


MODULE = "Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean"


def _fixture(source: str, *, name: str = "tiny_simp") -> tuple[bytes, list[dict[str, object]]]:
    data = source.encode("utf-8")
    command_start = data.index(b"local macro")
    command_end = data.index(b"\n\n", command_start)
    body_start = data.index(b"simp only", command_start)
    body_end = data.index(b"])", body_start) + 1
    body = data[body_start:body_end]
    record = {
        "id": inventory.occurrence_id(MODULE, body_start, body_end),
        "kind": "simp_only",
        "source": body.decode(),
        "startByte": body_start,
        "endByte": body_end,
        "syntaxKind": "Lean.Parser.Tactic.simp",
        "commandKind": "Lean.Parser.Command.macro",
        "executionRole": "reusable_executable",
        "declarationKind": "caller_dependent",
        "action": "materialize",
        "commandStartByte": command_start,
        "commandEndByte": command_end,
    }
    return data, [record]


def _expect_failure(fn, fragment: str) -> None:
    try:
        fn()
    except RuntimeError as error:
        if fragment not in str(error):
            raise RuntimeError(f"expected {fragment!r}, got {error}") from error
    else:
        raise RuntimeError(f"fixture unexpectedly accepted: {fragment}")


def main() -> None:
    source, records = _fixture(
        """module

-- `tiny_simp` in a comment must stay inert.
def quoted : String := \"tiny_simp\"
local macro \"tiny_simp\" : tactic =>
  `(tactic| simp only [
    Nat.add_zero])

example : True := by
  tiny_simp
example : True := by first | tiny_simp
example : True := by tiny_simp <;> trivial
"""
    )
    lowered = overlay._module_lowering(
        MODULE, source, records, expected_definitions=1, expected_invocations=3
    )
    if len(lowered.definitions) != 1 or len(lowered.invocations) != 3:
        raise RuntimeError("fixture did not account for one definition and three calls")
    text = lowered.source.decode()
    if text.count("-- Original local macro definition:") != 1:
        raise RuntimeError("macro definition was not preserved as one comment")
    if text.count("Original local macro invocation: tiny_simp") != 3:
        raise RuntimeError("macro invocation comments were not preserved")
    if text.count("simp only [") != 4:  # three calls plus the preserved definition comment
        raise RuntimeError("lowering did not preserve the definition and produce three bodies")
    if "local macro \"tiny_simp\"" not in text:
        raise RuntimeError("original macro text was not retained in the comment")
    if len(lowered.generated_ranges) != 3:
        raise RuntimeError("generated occurrence ranges are incomplete")
    for start, end, body in lowered.generated_ranges:
        if lowered.source[start:end].decode() != body or not body.startswith("simp only ["):
            raise RuntimeError("generated range does not cover exactly the fixed body")

    argument_source, argument_records = _fixture(
        source.decode().replace("tiny_simp <;> trivial", "tiny_simp extra <;> trivial")
    )
    _expect_failure(
        lambda: overlay._module_lowering(
            MODULE, argument_source, argument_records,
            expected_definitions=1, expected_invocations=3,
        ),
        "macro name collision",
    )

    collision_source, collision_records = _fixture(
        source.decode() + "\ndef tiny_simp := 1\n"
    )
    _expect_failure(
        lambda: overlay._module_lowering(
            MODULE, collision_source, collision_records,
            expected_definitions=1, expected_invocations=3,
        ),
        "macro name collision",
    )

    formal_source = source.decode().replace(
        'local macro "tiny_simp" : tactic =>',
        'local macro "tiny_simp" (x : term) : tactic =>',
    )
    formal_data, formal_records = _fixture(formal_source)
    _expect_failure(
        lambda: overlay._module_lowering(
            MODULE, formal_data, formal_records,
            expected_definitions=1, expected_invocations=3,
        ),
        "nullary tactic local macro",
    )

    stale = dict(records[0])
    stale["source"] = "simp only [Nat.zero_eq]"
    _expect_failure(
        lambda: overlay._module_lowering(
            MODULE, source, [stale],
            expected_definitions=1, expected_invocations=3,
        ),
        "target source bytes changed",
    )

    extra = source.decode().replace(
        "example : True := by\n  tiny_simp",
        "local macro \"other_simp\" : tactic => `(tactic| simp only [Nat.add_zero])\n\n"
        "example : True := by\n  tiny_simp",
        1,
    )
    extra_data, extra_records = _fixture(extra)
    _expect_failure(
        lambda: overlay._module_lowering(
            MODULE, extra_data, extra_records,
            expected_definitions=1, expected_invocations=3,
        ),
        "unmanifested or mislocated local macro",
    )
    print("local macro overlay fixtures passed")


if __name__ == "__main__":
    main()
