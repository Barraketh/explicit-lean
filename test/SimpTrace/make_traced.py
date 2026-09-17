#!/usr/bin/env python3
"""Generate a traced copy of a Mathlib module for measurement.

Rewrites every simp-family *tactic* invocation to `simp_trace ... =>trace
"<path>"`, leaving `@[simp]` attributes, declaration names, doc text and the
`Simp.simp` term-level API alone. `test/SimpTrace/check_transcription.py`
verifies afterwards that no site was missed -- REVIEW-8 5 found two dropped by
an earlier line-oriented rewrite, both `<tactic>; simp`.

    python3 -B test/SimpTrace/make_traced.py Logic/Basic.lean LogicBasicTraced
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
MATHLIB = ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"

TACTIC = re.compile(r"(?<![\w?.])(simp only|simp|dsimp only|dsimp)(?![_?\w])")
# What may precede a tactic invocation: start of the tactic block, `by`, a
# sequencing combinator, a focus dot, a match arm, or an opening bracket.
PRECEDES = ("by", ";", "<;>", "·", "|", "=>", "(", "[")
# `<| simp e` and `$ simp e` are *term*-level applications of the `simp` API,
# not tactic invocations, and `Meta.Tactic.simp` is a trace-class name.
TERM_LEVEL = ("<|", "$")


def convert(text: str, name: str) -> tuple[str, int]:
    out: list[str] = []
    n = 0
    for line in text.split("\n"):
        stripped = line.lstrip()
        if (
            "@[" in line
            or stripped.startswith("attribute")
            or "Simp.simp" in line
            or stripped.startswith("--")
            or stripped.startswith("/-")
        ):
            out.append(line)
            continue

        # Rewrite right-to-left so earlier offsets stay valid.
        matches = [
            m
            for m in TACTIC.finditer(line)
            if (
                lambda b: (b == "" or b.endswith(PRECEDES))
                and not b.endswith(TERM_LEVEL)
            )(line[: m.start()].rstrip())
        ]
        if not matches:
            out.append(line)
            continue

        for m in reversed(matches):
            n += 1
        # Number them left-to-right for readable file names.
        base = n - len(matches)
        new = line
        for offset, m in reversed(list(enumerate(matches))):
            idx = base + offset + 1
            head = "simp_trace only" if m.group(1).endswith(" only") else "simp_trace"
            clause = f' =>trace "test/SimpTrace/meas_out/{name}_{idx:02}.json"'
            rest = new[m.end() :]
            # The tactic runs to the end of the line, or to a closing bracket or
            # comma that belongs to an enclosing term (`⟨_, by simp⟩`), or to a
            # sequencing `;` that starts the next tactic.
            cut = None
            depth = 0
            for i, ch in enumerate(rest):
                if ch in "⟨([{":
                    depth += 1
                elif ch in "⟩)]}":
                    if depth == 0:
                        cut = i
                        break
                    depth -= 1
                elif ch == "," and depth == 0:
                    cut = i
                    break
                elif ch == ";" and depth == 0:
                    cut = i
                    break
                elif rest[i : i + 3] == "<;>" and depth == 0:
                    # A following `<;> tac` is a separate tactic; the trace
                    # clause must sit before it, not after.
                    cut = i
                    break
            tail = new[m.end() :]
            if cut is not None:
                new = new[: m.end() + cut].rstrip() + clause + tail[cut:]
            else:
                new = new[: m.end()] + tail.rstrip() + clause
            new = new[: m.start()] + head + new[m.end() :]
        out.append(new)

    text = "\n".join(out)
    text = re.sub(
        r"^(public import .*)$",
        r"\1\npublic meta import ExplicitLean.SimpTrace",
        text,
        count=1,
        flags=re.M,
    )
    return text, n


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 1
    source_rel, name = sys.argv[1], sys.argv[2]
    text, n = convert((MATHLIB / source_rel).read_text(encoding="utf-8"), name)
    (ROOT / "test" / "SimpTrace" / f"{name}.lean").write_text(text, encoding="utf-8")
    print(f"{name}: converted {n} site(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
