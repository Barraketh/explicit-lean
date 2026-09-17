#!/usr/bin/env python3
"""Source-site identity for traced Mathlib copies in the trusted environment."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any

TACTIC_RE = re.compile(r"(?<![\w?.])(simp only|simp|dsimp only|dsimp)(?![_?\w])")
PRECEDES = ("by", ";", "<;>", "·", "|", "=>", "(", "[")
TERM_LEVEL = ("<|", "$")


@dataclass(frozen=True)
class Site:
    siteOrdinal: int
    startChar: int
    endChar: int
    line: int
    column: int
    callText: str


@dataclass(frozen=True)
class Edit:
    siteOrdinal: int
    sourceStart: int
    sourceEnd: int
    outputStart: int
    outputEnd: int
    replacement: str


def _mask_attributes(source: str) -> str:
    chars = list(source)
    i = 0
    while i + 1 < len(source):
        if source[i:i + 2] != "@[":
            i += 1
            continue
        start = i
        i += 2
        depth, quoted = 1, False
        while i < len(source) and depth:
            ch = source[i]
            if quoted:
                if ch == "\\":
                    i += 2
                    continue
                if ch == '"':
                    quoted = False
            elif ch == '"':
                quoted = True
            elif ch == "[":
                depth += 1
            elif ch == "]":
                depth -= 1
            i += 1
        for j in range(start, min(i, len(chars))):
            chars[j] = " "
    return "".join(chars)


def _mask_comments(source: str) -> str:
    chars = list(source)
    i, depth, quoted = 0, 0, False
    while i < len(source):
        if depth:
            if source[i:i + 2] == "/-":
                chars[i:i + 2] = [" ", " "]
                depth += 1
                i += 2
            elif source[i:i + 2] == "-/":
                chars[i:i + 2] = [" ", " "]
                depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    chars[i] = " "
                i += 1
            continue
        if quoted:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                quoted = False
                i += 1
            else:
                i += 1
            continue
        if source[i] == '"':
            quoted = True
            i += 1
        elif source[i:i + 2] == "--":
            while i < len(source) and source[i] != "\n":
                chars[i] = " "
                i += 1
        elif source[i:i + 2] == "/-":
            chars[i:i + 2] = [" ", " "]
            depth = 1
            chars[i:i + 2] = [" ", " "]
            i += 2
        else:
            i += 1
    return "".join(chars)


def call_end(rest: str) -> int:
    depth, block_comment, quoted = 0, 0, False
    i = 0
    while i < len(rest):
        ch = rest[i]
        if block_comment:
            if rest[i:i + 2] == "/-":
                block_comment += 1
                i += 2
            elif rest[i:i + 2] == "-/":
                block_comment -= 1
                i += 2
            else:
                i += 1
            continue
        if quoted:
            if ch == "\\":
                i += 2
            else:
                quoted = ch != '"'
                i += 1
            continue
        if ch == '"':
            quoted = True
            i += 1
            continue
        if rest[i:i + 2] == "--" and depth == 0:
            return i
        if rest[i:i + 2] == "/-":
            if depth == 0:
                return i
            block_comment = 1
            i += 2
            continue
        if ch in "⟨([{":
            depth += 1
        elif ch in "⟩)]}":
            if depth == 0:
                return i
            depth -= 1
        elif ch in ",;:" and depth == 0:
            return i
        elif rest[i:i + 3] == "<;>" and depth == 0:
            return i
        i += 1
    return i


def find_sites(source: str) -> list[Site]:
    masked = _mask_attributes(_mask_comments(source))
    sites: list[Site] = []
    offset = 0
    for line_no, line in enumerate(source.split("\n"), start=1):
        masked_line = masked[offset:offset + len(line)]
        stripped = line.lstrip()
        if not (stripped.startswith("attribute") or "Simp.simp" in line
                or stripped.startswith("--") or stripped.startswith("/-")):
            for match in TACTIC_RE.finditer(masked_line):
                before = line[:match.start()].rstrip()
                if before.endswith(TERM_LEVEL):
                    continue
                if before and not before.endswith(PRECEDES):
                    continue
                end = match.end() + call_end(line[match.end():])
                text = line[match.start():end].rstrip()
                start = offset + match.start()
                sites.append(Site(len(sites), start, start + len(text),
                                  line_no, match.start(), text))
        offset += len(line) + 1
    return sites


def manifest(module_path: str, source: str, sites: list[Site]) -> dict[str, Any]:
    return {
        "modulePath": module_path,
        "sites": [{"siteOrdinal": s.siteOrdinal,
                    "startChar": s.startChar, "endChar": s.endChar,
                    "callText": s.callText} for s in sites],
    }


def transform_with_ledger(source: str, traced_name: str) -> tuple[str, list[Edit]]:
    sites = find_sites(source)
    parts: list[str] = []
    edits: list[Edit] = []
    cursor = 0
    for site in sites:
        token = ("simp only" if site.callText.startswith("simp only") else
                 "dsimp only" if site.callText.startswith("dsimp only") else
                 "dsimp" if site.callText.startswith("dsimp") else "simp")
        head = "simp_trace only" if token == "simp only" else "simp_trace"
        replacement = head + site.callText[len(token):]
        replacement += f' =>trace "test/SimpTrace/meas_out/{traced_name}_{site.siteOrdinal + 1:02}.json"'
        parts.append(source[cursor:site.startChar])
        output_start = sum(len(part) for part in parts)
        parts.append(replacement)
        edits.append(Edit(site.siteOrdinal, site.startChar, site.endChar,
                          output_start, output_start + len(replacement), replacement))
        cursor = site.endChar
    parts.append(source[cursor:])
    traced = "".join(parts)
    if "ExplicitLean.SimpTrace" not in traced:
        match = re.search(r"^public import .*?$", traced, re.M)
        if match:
            insertion = "\npublic meta import ExplicitLean.SimpTrace"
            traced = traced[:match.end()] + insertion + traced[match.end():]
            edits = [Edit(e.siteOrdinal, e.sourceStart, e.sourceEnd,
                          e.outputStart + (len(insertion) if e.outputStart >= match.end() else 0),
                          e.outputEnd + (len(insertion) if e.outputStart >= match.end() else 0),
                          e.replacement) for e in edits]
    return traced, edits


def transform(source: str, traced_name: str) -> str:
    """Transform source while retaining the ledger-capable public helper."""
    return transform_with_ledger(source, traced_name)[0]


def verify_transform(source: str, traced_name: str, traced: str,
                     sites: list[Site]) -> list[Edit]:
    expected, edits = transform_with_ledger(source, traced_name)
    if traced != expected:
        raise ValueError("traced source differs from deterministic transform")
    if len(edits) != len(sites):
        raise ValueError("transform edit ledger is incomplete")
    for edit, site in zip(edits, sites):
        if (edit.siteOrdinal != site.siteOrdinal or
                edit.sourceStart != site.startChar or edit.sourceEnd != site.endChar or
                source[edit.sourceStart:edit.sourceEnd] != site.callText):
            raise ValueError(f"transform ledger source mismatch at site {site.siteOrdinal}")
        if traced[edit.outputStart:edit.outputEnd] != edit.replacement:
            raise ValueError(f"transform ledger output mismatch at site {site.siteOrdinal}")
    return edits


def validate_invocations(records: list[dict[str, Any]]) -> None:
    """Ordinary consistency check for one site's invocation ordinals."""
    if not records:
        raise ValueError("site has no invocation records")
    totals = {r.get("invocations") for r in records}
    if len(totals) != 1 or not isinstance(next(iter(totals)), int):
        raise ValueError("site invocation totals are missing or inconsistent")
    total = next(iter(totals))
    ordinals = [r.get("invocation") for r in records]
    if isinstance(total, bool) or total < 1 or len(records) != total:
        raise ValueError("site invocation records do not match declared total")
    if any(not isinstance(x, int) or isinstance(x, bool) or x < 0 or x >= total
           for x in ordinals) or len(set(ordinals)) != total:
        raise ValueError("site invocation ordinal is missing, duplicate, or out of range")
