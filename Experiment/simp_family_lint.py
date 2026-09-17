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

#: Modifiers Lean allows in front of the `attribute` command keyword.
_COMMAND_PREFIX_KEYWORDS = frozenset({"local", "scoped", "private", "protected"})

#: How far out to resolve nested groups when deciding attribute context.
#: Attribute lists in pinned Mathlib nest at most three deep.
_MAX_BRACKET_DEPTH = 16


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


#: Closing delimiters mapped to their openers, for the backward matcher.
_CLOSERS = {"]": "[", ")": "(", "}": "{"}
_OPENERS = frozenset(_CLOSERS.values())


def _enclosing_bracket(masked: str, offset: int) -> int | None:
    """Return the index of the bracket that directly encloses ``offset``.

    Walks backwards matching delimiters, so any content may appear inside a
    nested group.  ``masked`` has comments and string literals blanked out
    already, so delimiters inside them cannot unbalance the scan.  Returns
    ``None`` when ``offset`` is not inside any bracket.
    """

    stack: list[str] = []
    probe = offset - 1
    while probe >= 0:
        char = masked[probe]
        if char in _CLOSERS:
            stack.append(_CLOSERS[char])
        elif char in _OPENERS:
            if not stack:
                return probe
            if stack[-1] != char:
                # Unbalanced source; give up rather than guess.
                return None
            stack.pop()
        probe -= 1
    return None


def _in_attribute_list(masked: str, offset: int) -> bool:
    """True when ``offset`` sits inside an attribute list.

    Generated Mathlib files keep their original attributes, which are
    declaration syntax rather than tactic calls, so an attribute is never a
    finding.  Detection is structural: find the bracket group that directly
    encloses the token by matching delimiters backwards, then ask whether that
    group is an attribute list.  Because the matcher never inspects the
    characters *between* delimiters, arbitrary attribute arguments are handled,
    including the real pinned-Mathlib spellings

    * ``@[simp <-, push_cast]``, ``@[grind =>, simp]``, ``@[simp, grind =]``
    * ``@[aesop (rule_sets := [finiteness]) safe apply, simp]``
    * ``@[deprecated "use X" (since := "..."), norm_cast]``
    * ``@[to_dual self (reorder := f g, hf hg), simp]``

    A group counts as an attribute list when it is a ``[...]`` opened by ``@``
    or by the ``attribute`` command keyword, or a ``(...)`` opened by the
    ``(attr := ...)`` configuration.  Nested groups are resolved outwards, so
    the ``simp`` in ``@[aesop (rule_sets := [x]) safe, simp]`` is recognised
    whether it sits at the top level of the attribute list or inside one of
    its argument groups.
    """

    probe: int | None = offset
    # Resolve outwards: a token inside a nested argument group is still inside
    # the attribute list that contains that group.
    for _ in range(_MAX_BRACKET_DEPTH):
        bracket = _enclosing_bracket(masked, probe)
        if bracket is None:
            return False
        char = masked[bracket]
        if char == "[" and _opens_attribute_list(masked, bracket):
            return True
        if char == "(" and _ATTR_ASSIGN.match(masked, bracket):
            return True
        probe = bracket
    return False


def _opens_attribute_list(masked: str, bracket: int) -> bool:
    """True when the ``[`` at ``bracket`` opens an attribute list.

    Either ``@[`` directly, or a ``[`` preceded by the ``attribute`` command
    keyword.  The keyword may carry the modifiers Lean allows in front of it --
    ``local``, ``scoped``, ``scoped[NS]`` -- and any ``... in`` prefix such as
    ``open Foo in``, all on the same command.
    """

    probe = bracket - 1
    while probe >= 0 and masked[probe] in " \t\n":
        probe -= 1
    if probe >= 0 and masked[probe] == "@":
        return True
    if probe < 0:
        return False
    stop = probe + 1
    while probe >= 0 and _IDENT_BODY.match(masked[probe]):
        probe -= 1
    if masked[probe + 1 : stop] != "attribute":
        return False
    return _is_command_position(masked, probe + 1)


def _is_command_position(masked: str, start: int) -> bool:
    """True when the keyword at ``start`` heads a command.

    The keyword heads a command when what precedes it on the logical line is
    only command prefixes: ``local``, ``scoped``, ``scoped[NS]``, or anything
    ending in ``in`` (``open Foo in``, ``variable ... in``).  This keeps the
    round-1 guard that a keyword sitting mid-expression -- as in
    ``exact foo attribute [simp]`` -- does not shield a real tactic.
    """

    prefix = masked[:start]
    line_start = prefix.rfind("\n") + 1
    before = prefix[line_start:].strip()
    if not before:
        return True
    # `scoped[Pointwise]` and friends: drop bracket groups so the words remain.
    before = re.sub(r"\[[^\[\]]*\]", "", before).strip()
    if not before:
        return True
    words = before.split()
    if words[-1] == "in":
        # `open Foo in`, `variable {x} in`, ... -- a genuine command prefix.
        return True
    return all(word in _COMMAND_PREFIX_KEYWORDS for word in words)


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
