#!/usr/bin/env python3
"""Validate the fresh T22 raw capture against its UTF-8 source fixture."""

from __future__ import annotations

import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
SOURCE_PATH = ROOT / "test" / "SimpTrace" / "T22SourceArgIdentity.lean"
OUT = ROOT / "test" / "SimpTrace" / "out"


def main() -> int:
    source = SOURCE_PATH.read_text(encoding="utf-8")
    expected = {
        "t22_reverse.json": [("← foo b a h", "rev")],
        "t22_named_arg.json": [("heq_comm (a := a)", "fwd")],
        "t22_one_to_many.json": [("h", "fwd")],
        "t22_repeated.json": [("h", "fwd"), ("h", "fwd")],
    }
    for name, args_expected in expected.items():
        value = json.loads((OUT / name).read_text(encoding="utf-8"))
        args = value.get("sourceArgs")
        if not isinstance(args, list) or len(args) != len(args_expected):
            raise AssertionError(f"{name}: sourceArgs shape mismatch")
        for arg, (text, direction) in zip(args, args_expected):
            start, end = arg["startChar"], arg["endChar"]
            if source[start:end] != text:
                raise AssertionError(
                    f"{name}: scalar slice [{start}:{end}] is {source[start:end]!r}, "
                    f"expected {text!r}"
                )
            if arg["direction"] != direction:
                raise AssertionError(f"{name}: direction mismatch")
            if arg["endChar"] <= arg["startChar"]:
                raise AssertionError(f"{name}: empty source span")
        derived: list[tuple[int, str]] = []

        def visit(node: object) -> None:
            if isinstance(node, dict):
                derivation = node.get("derivation")
                if node.get("kind") == "rw" and isinstance(derivation, dict):
                    if "argId" in derivation:
                        derived.append((derivation["argId"], derivation.get("direction")))
                for child in node.values():
                    visit(child)
            elif isinstance(node, list):
                for child in node:
                    visit(child)

        visit(value.get("locations", []))
        if name == "t22_one_to_many.json" and derived != [(0, "fwd"), (0, "fwd")]:
            raise AssertionError(f"{name}: one-to-many derivations lost identity: {derived}")
        if name == "t22_repeated.json" and derived != [(1, "fwd")]:
            raise AssertionError(f"{name}: repeated argument attribution changed: {derived}")
        if name == "t22_reverse.json" and derived != [(0, "rev")]:
            raise AssertionError(f"{name}: reverse attribution changed: {derived}")
    print("OK: T22 sourceArgs use Unicode-scalar slices and direct rule identity")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
