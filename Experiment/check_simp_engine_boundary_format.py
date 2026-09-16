#!/usr/bin/env python3
"""Check generated boundary formatting without invoking Lean."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
import re
import argparse
import time

from check_simp_engine_boundary_source import (
    GENERATED_LINE_WIDTH,
    _format_generated_line,
    format_report_variants,
    preserve_original_call,
)


ROOT = Path(__file__).resolve().parents[1]


def decode_string_tokens(text: str) -> list[str]:
    """Decode JSON-compatible Lean strings after removing string gaps."""
    values = []
    for start, end in _string_spans(text):
        token = text[start:end]
        body = re.sub(r"\\\n[ \t]*", "", token[1:-1])
        values.append(json.loads('"' + body + '"'))
    return values


def _string_spans(text: str) -> list[tuple[int, int]]:
    spans = []
    index = 0
    while index < len(text):
        if text[index] != '"':
            index += 1
            continue
        start = index
        index += 1
        escaped = False
        while index < len(text):
            char = text[index]
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                index += 1
                spans.append((start, index))
                break
            index += 1
        else:
            raise AssertionError("unterminated generated string")
    return spans


def _expected_report_strings(report: dict[str, object]) -> list[str]:
    """Collect values the renderer must emit, independently of its output."""
    selector = report["selector"]
    assert isinstance(selector, dict)
    pre_state = selector["preState"]
    assert isinstance(pre_state, dict)
    values = [str(report["occurrence"])]
    values.extend(
        str(pre_state[name])
        for name in (
            "targetFingerprint",
            "localContextFingerprint",
            "metavariableContextFingerprint",
        )
    )
    # goalCount and action kinds are syntax numerals/identifiers, not string
    # literals; the remaining selector fields are quoted by the renderer.
    values.append(str(selector["options"]))
    values.append("" if selector["caller"] is None else str(selector["caller"]))
    if report["status"] == "success":
        values.append(
            json.dumps(
                report["stockGenerator"],
                separators=(",", ":"),
                ensure_ascii=False,
                sort_keys=True,
            )
        )
        for action in report.get("environmentActions", []):
            values.extend(
                [
                    json.dumps(action["nameParts"], separators=(",", ":"), ensure_ascii=False),
                    str(action["declaration"]),
                ]
            )

        def add_transformation(transformation: dict[str, object]) -> None:
            values.extend([str(transformation["input"]), str(transformation["result"])])
            if transformation["proof"] is not None:
                values.append(str(transformation["proof"]))

        for local in report["locals"]:
            add_transformation(local["transformation"])
        if report["target"] is not None:
            add_transformation(report["target"])
    return values


def assert_escape_and_gap_contract() -> None:
    # Includes a real JSON unicode escape, escaped quotes/backslashes, and
    # enough payload to force several string gaps.
    encoded = '"' + "\\u1234" + ("x" * 220) + "\\\\\\\"tail" + '"'
    rendered = _format_generated_line("apply_encoded " + encoded)
    if decode_string_tokens(encoded) != decode_string_tokens(rendered):
        raise AssertionError("string-gap formatting changed a decoded payload")
    if max(map(len, rendered.splitlines())) > GENERATED_LINE_WIDTH:
        raise AssertionError("escape-gap fixture exceeded the generated line budget")
    indented = _format_generated_line("  | apply_encoded " + encoded)
    if not indented.startswith("  | apply_encoded"):
        raise AssertionError("renderer dropped the authored leading indentation")
    preserved = preserve_original_call(rendered, "simp only [quoted \\\"text\\\"]", "    ")
    if "-- simp only [quoted \\\"text\\\"]" not in preserved:
        raise AssertionError("original tactic comment was not retained")
    whitespace_payload = '"' + ("x" * 220) + "   tail" + '"'
    whitespace_rendered = _format_generated_line("apply_encoded " + whitespace_payload)
    if decode_string_tokens(whitespace_payload) != decode_string_tokens(whitespace_rendered):
        raise AssertionError("payload whitespace was changed by string gaps")
    empty_rendered = _format_generated_line("x" * 98 + ' ""', "  ")
    if '""' not in empty_rendered or max(map(len, empty_rendered.splitlines())) > GENERATED_LINE_WIDTH:
        raise AssertionError("empty literal near the line boundary was malformed")
    try:
        _format_generated_line('"x"', " " * (GENERATED_LINE_WIDTH - 3))
    except RuntimeError:
        pass
    else:
        raise AssertionError("deep continuation indentation was not rejected")
    try:
        _format_generated_line("x" * 96 + ' "xxxx"', " " * (GENERATED_LINE_WIDTH - 4))
    except RuntimeError:
        pass
    else:
        raise AssertionError("boundary continuation indentation emitted an invalid gap")
    large = '"' + ("x" * 200_000) + '"'
    started = time.monotonic()
    large_rendered = _format_generated_line("apply_encoded " + large)
    if time.monotonic() - started > 2.0:
        raise AssertionError("large generated payload formatter made no bounded progress")
    if decode_string_tokens(large) != decode_string_tokens(large_rendered):
        raise AssertionError("large payload changed during string-gap formatting")


def assert_real_report_render(path: Path, indent: str) -> dict[str, object]:
    reports = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    if not reports:
        raise AssertionError(f"empty artifact report: {path}")
    grouped: dict[str, list[dict[str, object]]] = {}
    for report in reports:
        grouped.setdefault(str(report["occurrence"]), []).append(report)
    rendered_groups = [format_report_variants(group, indent) for group in grouped.values()]
    expected = Counter()
    for group in grouped.values():
        # The module is emitted once in the artifact header; branch selector
        # and outcome values are emitted once per report variant.
        expected[str(group[0]["selector"]["module"])] += 1
        expected.update(
            value
            for report in group
            for value in _expected_report_strings(report)
        )
    rendered_values = Counter(
        value
        for rendered in rendered_groups
        for value in decode_string_tokens(rendered)
    )
    missing = {
        value: count - rendered_values[value]
        for value, count in expected.items()
        if rendered_values[value] < count
    }
    if missing:
        raise AssertionError(f"{path}: rendered report values changed: {missing}")
    max_line = max(len(line) for rendered in rendered_groups for line in rendered.splitlines())
    if max_line > GENERATED_LINE_WIDTH:
        raise AssertionError(f"{path}: generated line length {max_line}")
    if any(not rendered.rstrip().endswith("))") for rendered in rendered_groups):
        raise AssertionError(f"{path}: selector closing delimiter escaped renderer budget")
    if any(not rendered.startswith("(simp_engine_boundary_select") for rendered in rendered_groups):
        raise AssertionError(f"{path}: malformed selector rendering")
    return {
        "report": str(path),
        "provenance": "historical frozen v8 report input; not fresh69 acceptance evidence",
        "reportSha256": __import__("hashlib").sha256(path.read_bytes()).hexdigest(),
        "occurrences": len(reports),
        "renderedLines": sum(len(rendered.splitlines()) for rendered in rendered_groups),
        "renderedBytes": sum(len(rendered.encode()) for rendered in rendered_groups),
        "checkedReportValues": sum(expected.values()),
        "maxGeneratedLine": max_line,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--report",
        action="append",
        type=Path,
        help="optional historical artifact-reports.jsonl path for a real re-render check",
    )
    args = parser.parse_args()
    assert_escape_and_gap_contract()
    results = []
    indents = ("  ", "    ", "      ", "          ")
    for index, path in enumerate(args.report or []):
        results.append(assert_real_report_render(path, indents[index % len(indents)]))
    print(json.dumps({"status": "ok", "selfContainedFixtures": True, "targets": results}, sort_keys=True))


if __name__ == "__main__":
    main()
