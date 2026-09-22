#!/usr/bin/env python3
"""Source-site identity for traced Mathlib copies in the trusted environment."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any

DEFAULT_TRACE_ROOT = "test/SimpTrace/meas_out"
TACTIC_RE = re.compile(r"(?<![\w?.])(simp only|simp|dsimp only|dsimp)(?![_?\w])")
PRECEDES = ("by", ";", "<;>", "·", "|", "=>", "(", "[")
TERM_LEVEL = ("<|", "$")
PREFIX_TACTICS = frozenset({"all_goals", "any_goals", "try", "repeat",
                            "repeat'", "focus"})


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


def _source_args(source: str, site: Site) -> list[dict[str, Any]]:
    """Record source argument spans from the original bytes.

    This is a shallow delimiter walk over the already identified call range;
    it never consumes elaborated terms or parses trace output.  The resulting
    slices are the authoritative bytes copied into the source/manifest.  Lean
    assigns the same IDs from its parser argument list and joins them to
    `Origin.stx` by the exact range.
    """
    # Slice the original source directly.  ``callText`` is retained as the
    # exact site payload, but argument identity never parses a later trace
    # call string or a pretty-printed term.
    text = source[site.startChar:site.endChar]
    left = text.find("[")
    if left < 0:
        return []
    depth = 0
    right = -1
    quoted = False
    i = left
    while i < len(text):
        ch = text[i]
        if quoted:
            if ch == "\\":
                i += 2
                continue
            quoted = ch != '"'
        elif ch == '"':
            quoted = True
        elif ch in "([{⟨":
            depth += 1
        elif ch in ")]⟩":
            depth -= 1
            if depth == 0:
                right = i
                break
        i += 1
    if right < 0:
        raise ValueError(f"unterminated simp argument list at site {site.siteOrdinal}")
    body = text[left + 1:right]
    pieces: list[tuple[int, int]] = []
    start, depth, quoted, i = 0, 0, False, 0
    while i <= len(body):
        boundary = i == len(body)
        if boundary:
            stop = i
        else:
            ch = body[i]
            if quoted:
                if ch == "\\":
                    i += 2
                    continue
                quoted = ch != '"'
            elif ch == '"':
                quoted = True
            elif ch in "([{⟨":
                depth += 1
            elif ch in ")]⟩":
                depth -= 1
            elif ch == "," and depth == 0:
                stop = i
                boundary = True
        if not boundary:
            i += 1
            continue
        raw_start = start
        while raw_start < stop and body[raw_start].isspace():
            raw_start += 1
        raw_stop = stop
        while raw_stop > raw_start and body[raw_stop - 1].isspace():
            raw_stop -= 1
        if raw_start < raw_stop:
            pieces.append((raw_start, raw_stop))
        start = stop + 1
        i = start
    result: list[dict[str, Any]] = []
    for arg_id, (a, b) in enumerate(pieces):
        arg = body[a:b]
        reverse = arg.startswith("←") or arg.startswith("<-")
        # This is only term-free source metadata, not elaboration: accept
        # Unicode/inaccessible identifier spelling and quoted names without
        # attempting to resolve or pretty-print the term.
        head = re.match(
            r"(?:←|<-)?\s*(?:@|_root_\.)?"
            r"((?:[^\W\d]|_)[\w✝']*(?:\.[\w✝']+)*|«[^»]+»(?:\.[\w✝']+)*)",
            arg,
        )
        result.append({
            "argId": arg_id,
            "startChar": site.startChar + left + 1 + a,
            "endChar": site.startChar + left + 1 + b,
            "direction": "rev" if reverse else "fwd",
            "kind": "simp-lemma",
            "head": head.group(1) if head else None,
        })
    return result


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
    i, depth, quoted, triple_quoted = 0, 0, False, False
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
        if quoted or triple_quoted:
            if source[i] != "\n":
                chars[i] = " "
            if source[i] == "\\":
                i += 2
            elif triple_quoted and source[i:i + 3] == '\"\"\"':
                chars[i:i + 3] = [" ", " ", " "]
                triple_quoted = False
                i += 3
            elif not triple_quoted and source[i] == '"':
                quoted = False
                i += 1
            else:
                i += 1
            continue
        if source[i:i + 3] == '\"\"\"':
            chars[i:i + 3] = [" ", " ", " "]
            triple_quoted = True
            i += 3
        elif source[i] == '"':
            chars[i] = " "
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


def _is_tactic_start(masked_source: str, line_start: int,
                     match_start: int) -> bool:
    """Recognize tactic starts after punctuation and Lean tactic prefixes."""
    before = masked_source[line_start:line_start + match_start].rstrip()
    if before.endswith(TERM_LEVEL):
        return False
    # Tactic sequences commonly use layout without an explicit separator.
    if not before:
        return True
    if before.endswith(tuple(x for x in PRECEDES if x != "by")):
        return True
    prefix_re = r"(?:^|\s)(?:" + "|".join(
        re.escape(x) for x in sorted(PREFIX_TACTICS, key=len, reverse=True)
    ) + r")$"
    if re.search(r"(?:^|[\s(])by$", before) or re.search(prefix_re, before):
        return True
    prior = masked_source[:line_start + match_start].rstrip()
    if not prior:
        return False
    if prior.endswith((";", "<;>", "·", "|", "=>", "(", "[")):
        return True
    return re.search(r"(?:^|[\s(])by$", prior) is not None or re.search(prefix_re, prior) is not None


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
        if not (stripped.startswith("attribute") or stripped.startswith("--")
                or stripped.startswith("/-")):
            for match in TACTIC_RE.finditer(masked_line):
                if not _is_tactic_start(masked, offset, match.start()):
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
                    "callText": s.callText,
                    "sourceArgs": _source_args(source, s)} for s in sites],
    }


def validate_source_args(value: dict[str, Any], source: str) -> None:
    """Fail closed if a source-argument span escapes its exact call range."""
    for site in value.get("sites", []):
        start, end = site["startChar"], site["endChar"]
        args = site.get("sourceArgs", [])
        ids = [a.get("argId") for a in args]
        if ids != list(range(len(args))):
            raise ValueError("source argument IDs are not site-local and contiguous")
        for arg in args:
            a, b = arg.get("startChar"), arg.get("endChar")
            if not isinstance(a, int) or not isinstance(b, int) or not (start <= a < b <= end):
                raise ValueError("source argument span escapes its call range")
            if not source[a:b].strip():
                raise ValueError("source argument span has no source bytes")
        expected = _source_args(source, Site(site["siteOrdinal"], start, end,
                                             0, 0, site["callText"]))
        if args != expected:
            raise ValueError(f"source argument bytes mismatch at site {site['siteOrdinal']}")


def _trace_clause_path(trace_root: str, traced_name: str, site_ordinal: int) -> str:
    """Return the exact path text embedded in an injected trace clause."""
    root = str(trace_root).rstrip("/")
    if not root:
        raise ValueError("trace output directory must not be empty")
    return f"{root}/{traced_name}_{site_ordinal + 1:02}.json"


def transform_with_ledger(
    source: str, traced_name: str, trace_root: str = DEFAULT_TRACE_ROOT,
    selected_sites: list[Site] | None = None,
) -> tuple[str, list[Edit]]:
    # Callers may instrument a selected subset (for example, commands leased
    # from the simp replacement queue). Keep their source ordinals and ranges
    # intact: trace identity is always checked against the complete source,
    # never inferred from a compacted list position.
    sites = find_sites(source) if selected_sites is None else list(selected_sites)
    all_sites = find_sites(source)
    by_ordinal = {site.siteOrdinal: site for site in all_sites}
    if len({site.siteOrdinal for site in sites}) != len(sites):
        raise ValueError("selected site ordinals are duplicated")
    for site in sites:
        if by_ordinal.get(site.siteOrdinal) != site:
            raise ValueError(f"selected site is not from source at ordinal {site.siteOrdinal}")
    if sites != sorted(sites, key=lambda site: site.siteOrdinal):
        raise ValueError("selected sites are not in source order")
    parts: list[str] = []
    edits: list[Edit] = []
    cursor = 0
    for site in sites:
        token = ("simp only" if site.callText.startswith("simp only") else
                 "dsimp only" if site.callText.startswith("dsimp only") else
                 "dsimp" if site.callText.startswith("dsimp") else "simp")
        head = "simp_trace only" if token == "simp only" else "simp_trace"
        replacement = head + site.callText[len(token):]
        replacement += f' =>trace "{_trace_clause_path(trace_root, traced_name, site.siteOrdinal)}"'
        parts.append(source[cursor:site.startChar])
        output_start = sum(len(part) for part in parts)
        parts.append(replacement)
        edits.append(Edit(site.siteOrdinal, site.startChar, site.endChar,
                          output_start, output_start + len(replacement), replacement))
        cursor = site.endChar
    parts.append(source[cursor:])
    traced = "".join(parts)
    if "ExplicitLean.SimpTrace" not in traced:
        match = re.search(r"^(?:public\s+)?(?:meta\s+)?import\b.*?$", traced, re.M)
        module_match = re.search(r"^module\s*$", traced, re.M)
        module_mode = module_match is not None
        import_text = ("public meta import ExplicitLean.SimpTrace" if module_mode
                       else "import ExplicitLean.SimpTrace")
        insertion = "\n" + import_text
        if match:
            at = match.end()
            traced = traced[:at] + insertion + traced[at:]
            edits = [Edit(e.siteOrdinal, e.sourceStart, e.sourceEnd,
                          e.outputStart + (len(insertion) if e.outputStart >= at else 0),
                          e.outputEnd + (len(insertion) if e.outputStart >= at else 0),
                          e.replacement) for e in edits]
        elif module_match:
            at = module_match.end()
            traced = traced[:at] + insertion + traced[at:]
            edits = [Edit(e.siteOrdinal, e.sourceStart, e.sourceEnd,
                          e.outputStart + (len(insertion) if e.outputStart >= at else 0),
                          e.outputEnd + (len(insertion) if e.outputStart >= at else 0),
                          e.replacement) for e in edits]
        else:
            import_text += "\n"
            traced = import_text + traced
            edits = [Edit(e.siteOrdinal, e.sourceStart, e.sourceEnd,
                          e.outputStart + len(import_text),
                          e.outputEnd + len(import_text),
                          e.replacement) for e in edits]
    return traced, edits


def transform(source: str, traced_name: str,
              trace_root: str = DEFAULT_TRACE_ROOT) -> str:
    """Transform source while retaining the ledger-capable public helper."""
    return transform_with_ledger(source, traced_name, trace_root)[0]


def verify_transform(source: str, traced_name: str, traced: str,
                     sites: list[Site],
                     trace_root: str = DEFAULT_TRACE_ROOT) -> list[Edit]:
    expected, edits = transform_with_ledger(source, traced_name, trace_root, sites)
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
