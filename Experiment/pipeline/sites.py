#!/usr/bin/env python3
"""Locate simp sites in a module and splice replacement text at them.

A **site** is the source byte range of one original `simp`/`simp only` call.
Sites are found with the same detection rule T1's `make_traced.py` and
`check_transcription.py` use, so the site list of a source and the `simp_trace`
list of its traced copy are the same list in the same order; that is what lets a
trace written against the traced copy be attributed to a byte range in the
original.

Splicing is whitespace-aware because Lean is. A replacement sits at the original
call's column, and continuation lines indent deeper than the enclosing tactic
block. A site that is not alone on its line (`ext a; simp only [...]`,
`rcases ... <;> simp [...]`, `⟨f y, by simp [...]⟩`) cannot take a multi-line
replacement at all, and cannot take a leading `rename_i` line either, so the
renderer is told to keep such a site on one line.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

# A simp-family tactic *invocation*, as opposed to `@[simp]`, a declaration
# name, a doc comment or the `Simp.simp` term-level API. Identical to the
# pattern in T1's `check_transcription.py`.
TACTIC_RE = re.compile(r"(?<![\w?.])(simp only|simp|dsimp only|dsimp)(?![_?\w])")
PRECEDES = ("by", ";", "<;>", "·", "|", "=>", "(", "[")
TERM_LEVEL = ("<|", "$")

MAX_LINE = 100


@dataclass
class Site:
    """One original simp call, as a byte range in the module source."""

    index: int
    """0-based position in the module's site list, matching the trace order."""
    start: int
    """Byte offset of the first character of the tactic token."""
    end: int
    """Byte offset just past the last character of the call."""
    text: str
    """The exact original call text, `source[start:end]`."""
    line: int
    """1-based line number of `start`."""
    column: int
    """0-based column of `start`, which is where a replacement must sit."""
    alone_on_line: bool
    """True when only whitespace precedes the call on its line."""
    trailing: str
    """What follows the call on its line (`⟩⟩,`, `)` and so on), preserved."""


def call_end(rest: str) -> int:
    """How far the tactic runs from just after its keyword.

    The same bracket-aware scan `make_traced.py` uses to place its `=>trace`
    clause: the call runs to the end of the line, or to a closing bracket or
    comma belonging to an enclosing term, or to a sequencing `;` or `<;>` that
    starts the next tactic.
    """
    depth = 0
    for i, ch in enumerate(rest):
        if ch in "⟨([{":
            depth += 1
        elif ch in "⟩)]}":
            if depth == 0:
                return i
            depth -= 1
        elif ch == "," and depth == 0:
            return i
        elif ch == ";" and depth == 0:
            return i
        elif rest[i : i + 3] == "<;>" and depth == 0:
            return i
    return len(rest)


def skip_line(line: str) -> bool:
    """Lines whose simp mentions are not tactic invocations."""
    stripped = line.lstrip()
    return (
        "@[" in line
        or stripped.startswith("attribute")
        or "Simp.simp" in line
        or stripped.startswith("--")
        or stripped.startswith("/-")
    )


def find_sites(source: str) -> list[Site]:
    """Every simp-family tactic site in `source`, in source order."""
    sites: list[Site] = []
    offset = 0
    for lineno, line in enumerate(source.split("\n"), start=1):
        if skip_line(line):
            offset += len(line) + 1
            continue
        for match in TACTIC_RE.finditer(line):
            before = line[: match.start()].rstrip()
            if before.endswith(TERM_LEVEL):
                continue
            if not (before == "" or before.endswith(PRECEDES)):
                continue
            rest = line[match.end() :]
            end_in_line = match.end() + call_end(rest)
            text = line[match.start() : end_in_line].rstrip()
            sites.append(
                Site(
                    index=len(sites),
                    start=offset + match.start(),
                    end=offset + match.start() + len(text),
                    text=text,
                    line=lineno,
                    column=match.start(),
                    alone_on_line=before == "",
                    trailing=line[match.start() + len(text) :],
                )
            )
        offset += len(line) + 1
    return sites


def comment_original(text: str, indent: str) -> list[str]:
    """The original call preserved as a comment, one `--` per line."""
    lines = [indent + "-- Original simp:"]
    for line in text.split("\n"):
        lines.append((indent + "-- " + line).rstrip())
    return lines


def wrap_step_list(head: str, steps: list[str], tail: str, indent: str,
                   continuation: str) -> list[str]:
    """Lay out `head[steps] tail` within the line budget.

    Breaks only between steps, which is the one place the syntax admits a line
    break without changing meaning. A single step longer than the budget cannot
    be broken; the caller is told so via `overlong`.
    """
    single = indent + head + ", ".join(steps) + tail
    if len(single) <= MAX_LINE or len(steps) <= 1:
        return [single]

    lines: list[str] = []
    current = head
    first = True
    for i, step in enumerate(steps):
        last = i == len(steps) - 1
        piece = step + ("" if last else ",")
        prefix = indent if not lines else continuation
        candidate = current + ("" if first else " ") + piece
        # The final piece carries the tail (`]`, a `then` closer, an `at h`
        # clause), which must fit on the same line as the step it follows.
        width = len(prefix) + len(candidate) + (len(tail) if last else 0)
        if not first and width > MAX_LINE:
            lines.append(prefix + current)
            current = piece
        else:
            current = candidate
        first = False
    lines.append((indent if not lines else continuation) + current + tail)
    return lines


def overlong(lines: list[str]) -> list[str]:
    """The rendered lines that still exceed the budget after breaking."""
    return [line for line in lines if len(line) > MAX_LINE]


def splice(source: str, replacements: dict[int, list[str]],
           sites: list[Site]) -> str:
    """Replace each named site with its rendered lines.

    `replacements` maps a site index to the full replacement lines, already
    indented. Sites are applied right to left so earlier offsets stay valid.
    The first replacement line carries no indentation of its own when the site
    is not alone on its line: there the call is spliced in place, mid-line.
    """
    out = source
    for site in sorted(sites, key=lambda s: s.start, reverse=True):
        if site.index not in replacements:
            continue
        lines = replacements[site.index]
        if not lines:
            continue
        if site.alone_on_line:
            # Drop the leading indentation of the first line: the source keeps
            # its own, and `site.start` already sits after it.
            body = "\n".join(lines)
            body = body[site.column :] if body.startswith(" " * site.column) else body
        else:
            if len(lines) > 1:
                raise ValueError(
                    f"site {site.index} is not alone on its line and cannot take a "
                    f"multi-line replacement"
                )
            body = lines[0].lstrip()
        out = out[: site.start] + body + out[site.end :]
    return out


IMPORT_RE = re.compile(r"^(public )?(meta )?import\s+\S+", re.M)


def add_import(source: str, module: str = "ExplicitLean.ExplicitRw") -> str:
    """Insert `import <module>` after the module's existing imports.

    Mathlib's module system spells these `public import ...`; the new import
    follows the spelling of the last one so the file keeps a uniform header.
    """
    matches = list(IMPORT_RE.finditer(source))
    if not matches:
        raise ValueError("module has no import block")
    last = matches[-1]
    spelling = "public import" if last.group(1) else "import"
    return (
        source[: last.end()] + f"\n{spelling} {module}" + source[last.end() :]
    )
