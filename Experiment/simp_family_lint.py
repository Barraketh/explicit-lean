#!/usr/bin/env python3
"""Detect simp-family tactics in Lean source text.

The governing rule in ``AGENTS.md`` forbids the simp family from generated and
override code: `simp`, `simp only`, `simpa`, `simp_all`, `simp_rw`, `dsimp`,
`norm_num`, `push_cast`, `norm_cast` and friends, including inside `conv`
blocks.  Everything else (`rw`, `exact`, `unfold`, `change`, `show`, `ring`,
`omega`, ...) is allowed.

This module scans Lean source text -- a whole file or a single replacement
snippet -- and reports every occurrence of a forbidden token.  Two things it
deliberately does *not* flag:

* text inside comments.  Translated files keep the original call as an adjacent
  ``-- Original simp:`` comment, and block comments ``/- ... -/`` (which nest in
  Lean) may quote tactics in documentation.
* text inside string literals, including escaped quotes and ``s!``/``m!``
  interpolations, which are scanned as plain strings.

It also does not flag identifiers that merely contain a forbidden token as a
substring (`simple`, `Simp.Result`, `simp_lemma_name` passed as an argument),
nor the ``@[simps]`` / ``@[simps!]`` attribute, which generates lemmas and is
not a tactic.

Use :func:`findings` for structured results, :func:`format_findings` for a
human report, or run the module as a CLI over files or stdin.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import re
import sys
from typing import Iterable, Sequence


#: Forbidden tactic head tokens.  Multi-word spellings such as ``simp only``
#: and ``dsimp only`` are reported under their head token; the head alone is
#: already forbidden, so matching heads is both necessary and sufficient.
SIMP_FAMILY_TOKENS: frozenset[str] = frozenset(
    {
        "dsimp",
        "dsimp!",
        "dsimp?",
        "field_simp",
        "norm_cast",
        "norm_num",
        "norm_num1",
        "push_cast",
        "simp",
        "simp!",
        "simp?",
        "simp_all",
        "simp_all!",
        "simp_all?",
        "simp_arith",
        "simp_intro",
        "simp_rw",
        "simp_wf",
        "simpa",
        "simpa!",
        "simpa?",
    }
)

#: Tokens that are never tactics even though they start with a forbidden
#: spelling.  ``simps`` is the ``@[simps]`` lemma-generating attribute.
ATTRIBUTE_ONLY_TOKENS: frozenset[str] = frozenset({"simps", "simps!", "simps?"})

# A Lean identifier character.  Lean allows ``_``, ``'``, ``!``, ``?`` and
# ``.`` inside or directly after tactic names, so a candidate token is grown
# greedily and then compared against the table: this is what stops
# ``simp_lemma_name`` and ``Simp.Result`` from matching ``simp``.
_IDENT_BODY = re.compile(r"[A-Za-z0-9_'À-ɏΑ-ω!?]")
_IDENT_START = re.compile(r"[A-Za-z_À-ɏΑ-ω]")

# The `(attr := ...)` configuration used by `@[to_additive (attr := simp)]`.
_ATTR_ASSIGN = re.compile(r"\(\s*attr\s*:=")


@dataclass(frozen=True)
class Finding:
    """One forbidden token occurrence."""

    token: str
    offset: int
    line: int
    column: int
    text: str

    def describe(self) -> str:
        return f"line {self.line}, column {self.column}: {self.token} ({self.text!r})"


def _mask(source: str) -> str:
    """Return ``source`` with comments and string literals blanked out.

    Blanked regions keep their length and their newlines, so offsets and line
    numbers computed on the mask are valid for the original text.
    """

    out = list(source)
    index = 0
    length = len(source)

    def blank(start: int, stop: int) -> None:
        for position in range(start, min(stop, length)):
            if out[position] != "\n":
                out[position] = " "

    while index < length:
        char = source[index]
        # Block comment, including doc comments `/-- ... -/`.  Lean nests them.
        if char == "/" and source.startswith("/-", index):
            start = index
            depth = 0
            while index < length:
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                    if depth == 0:
                        break
                else:
                    index += 1
            blank(start, index)
            continue
        # Line comment.  `--` only starts one outside strings, which is where
        # we are.
        if source.startswith("--", index):
            start = index
            newline = source.find("\n", index)
            index = length if newline == -1 else newline
            blank(start, index)
            continue
        # Character literal, e.g. `'a'` or `'\n'`.  Lean also uses `'` as an
        # identifier suffix (`h'`), so only treat it as a literal when it is
        # not preceded by an identifier character.
        if char == "'" and not (index and _IDENT_BODY.match(source[index - 1])):
            start = index
            index += 1
            if index < length and source[index] == "\\":
                index += 2
            elif index < length:
                index += 1
            if index < length and source[index] == "'":
                index += 1
                blank(start, index)
                continue
            index = start + 1
            continue
        # Raw string literal r"..." / r#"..."#.
        if char == "r" and index + 1 < length and source[index + 1] in '"#':
            match = re.compile(r'r(#*)"').match(source, index)
            if match and not (index and _IDENT_BODY.match(source[index - 1])):
                start = index
                closing = '"' + match.group(1)
                stop = source.find(closing, match.end())
                index = length if stop == -1 else stop + len(closing)
                blank(start, index)
                continue
        # Ordinary string literal, including the `s!"..."` / `m!"..."` forms
        # whose leading marker is consumed as an identifier before we get here.
        if char == '"':
            start = index
            index += 1
            while index < length:
                if source[index] == "\\":
                    index += 2
                    continue
                if source[index] == '"':
                    index += 1
                    break
                index += 1
            blank(start, index)
            continue
        index += 1

    return "".join(out)


def _tokens(masked: str) -> Iterable[tuple[str, int]]:
    """Yield ``(token, offset)`` for every identifier-like run in ``masked``."""

    index = 0
    length = len(masked)
    while index < length:
        char = masked[index]
        if not _IDENT_START.match(char):
            index += 1
            continue
        start = index
        while index < length and _IDENT_BODY.match(masked[index]):
            index += 1
        # Absorb dotted continuations such as `Simp.Result` so that the token
        # compared against the table is the whole name, not its first segment.
        while (
            index + 1 < length
            and masked[index] == "."
            and _IDENT_START.match(masked[index + 1])
        ):
            index += 1
            while index < length and _IDENT_BODY.match(masked[index]):
                index += 1
        yield masked[start:index], start


def _in_attribute_list(masked: str, offset: int) -> bool:
    """True when ``offset`` sits inside an attribute list.

    Generated Mathlib files keep their original attributes, which are
    declaration syntax rather than tactic calls.  The forms recognised here
    are the ones that actually occur in pinned Mathlib:

    * ``@[simp]``, ``@[simp, norm_cast]``, ``@[local simp]``, ``@[simps]``
    * ``attribute [simp] foo``, ``attribute [local simp] foo``,
      ``attribute [scoped simp] foo`` and ``attribute [-simp] foo`` -- the
      last one *removes* the attribute, so flagging it would be doubly wrong
    * ``(attr := simp)``, as used by ``@[to_additive (attr := simp)]``

    The scan walks backwards from the token over the rest of the list,
    tracking bracket depth so nested argument lists such as
    ``@[simps apply_coe, simp]`` are handled, and stops at any character that
    cannot appear in one.
    """

    # `(attr := simp)` and `(attr := simp, norm_cast)`: look back for the
    # `attr :=` marker inside the enclosing parentheses.
    depth = 0
    probe = offset - 1
    while probe >= 0:
        char = masked[probe]
        if char == ")":
            depth += 1
        elif char == "(":
            if depth == 0:
                if _ATTR_ASSIGN.match(masked, probe):
                    return True
                break
            depth -= 1
        elif char in " \t\n,:=" or _IDENT_BODY.match(char) or char == ".":
            pass
        else:
            break
        probe -= 1

    depth = 0
    probe = offset - 1
    while probe >= 0:
        char = masked[probe]
        if char == "]":
            depth += 1
        elif char == "[":
            if depth == 0:
                return _opens_attribute_list(masked, probe)
            depth -= 1
        elif char in " \t\n,-" or _IDENT_BODY.match(char) or char == ".":
            # `-` carries the `@[-simp]` / `attribute [-simp]` removal form.
            pass
        else:
            return False
        probe -= 1
    return False


def _opens_attribute_list(masked: str, bracket: int) -> bool:
    """True when the ``[`` at ``bracket`` opens an attribute list.

    That is either ``@[`` directly, or a ``[`` preceded by the ``attribute``
    command keyword (with optional modifiers already consumed by the caller).
    """

    probe = bracket - 1
    if probe >= 0 and masked[probe] == "@":
        return True
    while probe >= 0 and masked[probe] in " \t\n":
        probe -= 1
    if probe < 0:
        return False
    stop = probe + 1
    while probe >= 0 and _IDENT_BODY.match(masked[probe]):
        probe -= 1
    word = masked[probe + 1 : stop]
    if word != "attribute":
        return False
    # `attribute` must be a command head, i.e. start a line rather than sit in
    # the middle of an expression such as `foo attribute [x]`.
    scan = probe
    while scan >= 0 and masked[scan] in " \t":
        scan -= 1
    return scan < 0 or masked[scan] == "\n"


def _line_column(source: str, offset: int) -> tuple[int, int]:
    prefix = source[:offset]
    line = prefix.count("\n") + 1
    column = offset - (prefix.rfind("\n") + 1) + 1
    return line, column


def _snippet(source: str, offset: int) -> str:
    start = source.rfind("\n", 0, offset) + 1
    stop = source.find("\n", offset)
    if stop == -1:
        stop = len(source)
    return source[start:stop].strip()


def findings(source: str) -> list[Finding]:
    """Return every simp-family tactic occurrence in ``source``.

    ``source`` may be a whole Lean file or a bare tactic snippet such as an
    entry's ``replacement``.  Comments and string literals are ignored.
    """

    if not isinstance(source, str):
        raise TypeError("source must be str")
    masked = _mask(source)
    results: list[Finding] = []
    for token, offset in _tokens(masked):
        if token in ATTRIBUTE_ONLY_TOKENS or token not in SIMP_FAMILY_TOKENS:
            continue
        # `@[simp]` and `@[simp, norm_cast]` mark a lemma for the simp/cast
        # sets; those are declaration attributes rather than tactic calls, and
        # the deliverable removes the simp family from executable code only.
        # Detect them by scanning back over the other entries of the attribute
        # list -- identifiers, their arguments, whitespace and commas -- to an
        # opening `@[`.
        if _in_attribute_list(masked, offset):
            continue
        line, column = _line_column(source, offset)
        results.append(
            Finding(
                token=token,
                offset=offset,
                line=line,
                column=column,
                text=_snippet(source, offset),
            )
        )
    return results


def has_simp_family(source: str) -> bool:
    """True when ``source`` contains at least one simp-family tactic."""

    return bool(findings(source))


def format_findings(results: Sequence[Finding], label: str = "") -> str:
    """Render ``results`` as one report line per finding."""

    prefix = f"{label}: " if label else ""
    return "\n".join(prefix + item.describe() for item in results)


def assert_clean(source: str, label: str = "source") -> None:
    """Raise ``RuntimeError`` naming every simp-family tactic in ``source``."""

    results = findings(source)
    if results:
        detail = "; ".join(item.describe() for item in results)
        raise RuntimeError(
            f"{label} uses forbidden simp-family tactics: {detail}. "
            "Use ordinary tactics (unfold, change, show, rw, exact, rfl) instead."
        )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Report simp-family tactics in Lean source text."
    )
    parser.add_argument(
        "paths",
        nargs="*",
        help="Lean source files to scan; reads stdin when omitted.",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Print nothing; communicate only through the exit status.",
    )
    args = parser.parse_args(argv)

    total = 0
    if args.paths:
        for path in args.paths:
            try:
                with open(path, "r", encoding="utf-8") as handle:
                    text = handle.read()
            except OSError as error:
                print(f"cannot read {path}: {error}", file=sys.stderr)
                return 2
            results = findings(text)
            total += len(results)
            if results and not args.quiet:
                print(format_findings(results, path))
    else:
        results = findings(sys.stdin.read())
        total += len(results)
        if results and not args.quiet:
            print(format_findings(results, "<stdin>"))

    if not args.quiet:
        print(f"{total} simp-family finding(s)")
    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main())
