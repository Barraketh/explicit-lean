#!/usr/bin/env python3
"""Record and materialize seventeen source occurrences end to end."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import tempfile
import re
from collections import defaultdict

from simp_engine_inventory import inject_import, rewrite_simp_heads, syntax_inventory_file


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Experiment" / "SimpEngineBoundarySourceInput.lean"
ARTIFACT_MARKER = "SIMP_ENGINE_BOUNDARY_ARTIFACT "
INVENTORY_TIMEOUT = 300


def run(command: list[str], timeout: int = 300) -> str:
    result = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def query_json_string(output: str, label: str) -> str:
    """Read Lake's JSON result after any replayed dependency diagnostics."""
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    if not lines:
        raise RuntimeError(f"{label} returned no JSON result")
    value = json.loads(lines[-1])
    if not isinstance(value, str) or not value:
        raise RuntimeError(f"{label} returned an invalid value: {value!r}")
    return value


def compile_source(dylib: str, source: Path) -> str:
    return run(["lake", "env", "lean", f"--load-dynlib={dylib}", str(source)])


def replace_occurrence(source: bytes, start: int, end: int, replacement: str) -> bytes:
    return source[:start] + replacement.encode("utf-8") + source[end:]


def replace_all_occurrences(
    source: bytes,
    entries: list[dict[str, object]],
    reports: dict[str, list[dict[str, object]]],
) -> bytes:
    """Replace complete occurrences and indent from their actual final columns.

    Multiple occurrences may share one source line. First installing one-line
    placeholders preserves stable original ranges; expanding those placeholders
    from left to right then accounts for newlines introduced by every earlier
    artifact on the line.
    """
    for entry in entries:
        occurrence = str(entry["id"])
        if occurrence not in reports:
            raise RuntimeError(f"missing artifact report for {occurrence}")
    placeholders: dict[str, bytes] = {
        str(entry["id"]): f"__simpBoundaryPlaceholder_{entry['id']}__".encode("ascii")
        for entry in entries
    }
    for entry in sorted(entries, key=lambda item: int(item["startByte"]), reverse=True):
        occurrence = str(entry["id"])
        source = replace_occurrence(
            source,
            int(entry["startByte"]),
            int(entry["endByte"]),
            placeholders[occurrence].decode("ascii"),
        )
    for entry in sorted(entries, key=lambda item: int(item["startByte"])):
        occurrence = str(entry["id"])
        placeholder = placeholders[occurrence]
        if source.count(placeholder) != 1:
            raise RuntimeError(f"materialization placeholder is not unique: {occurrence}")
        start = source.index(placeholder)
        replacement = format_report_variants(
            reports[occurrence], source_continuation_indent(source, start)
        )
        source = replace_occurrence(
            source, start, start + len(placeholder), replacement
        )
    return source


IDENTIFIER_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
UNSTABLE_RENDER_RE = re.compile(r"\?[_A-Za-z]")


def validate_rendered_term(value: str, label: str) -> None:
    for sentinel in ("⋯", "✝"):
        if sentinel in value:
            raise RuntimeError(f"{label} contains unstable printer output {sentinel!r}")
    invalid_source = re.search(r"@fun(?=\s|\{|\()|@\(let", value)
    if invalid_source:
        raise RuntimeError(
            f"{label} contains invalid explicit-printer source "
            f"{invalid_source.group(0)!r}"
        )
    if UNSTABLE_RENDER_RE.search(value):
        raise RuntimeError(f"{label} contains an internal metavariable name: {value!r}")


def validate_transformation(value: object, label: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise RuntimeError(f"{label} must be an object, got {value!r}")
    for field in ("input", "result", "proof"):
        if field not in value:
            raise RuntimeError(f"{label} is missing `{field}`: {value!r}")
    if not isinstance(value["input"], str) or not isinstance(value["result"], str):
        raise RuntimeError(f"{label} input/result must be strings: {value!r}")
    if value["proof"] is not None and not isinstance(value["proof"], str):
        raise RuntimeError(f"{label} proof must be a string or null: {value!r}")
    validate_rendered_term(value["input"], f"{label} input")
    validate_rendered_term(value["result"], f"{label} result")
    if value["proof"] is not None:
        validate_rendered_term(value["proof"], f"{label} proof")
    return value


def validate_environment_actions(value: object, label: str) -> list[dict[str, object]]:
    if not isinstance(value, list):
        raise RuntimeError(f"{label} must be an array: {value!r}")
    result: list[dict[str, object]] = []
    for action in value:
        if not isinstance(action, dict) or set(action) != {"kind", "name"}:
            raise RuntimeError(f"{label} contains an invalid action: {action!r}")
        if action["kind"] != "realize_reserved_name":
            raise RuntimeError(f"{label} contains an unsupported action: {action!r}")
        if not isinstance(action["name"], str) or not action["name"]:
            raise RuntimeError(f"{label} contains an invalid reserved name: {action!r}")
        result.append(action)
    return result


def validate_report(report: object, expected_id: str) -> dict[str, object]:
    if not isinstance(report, dict):
        raise RuntimeError(f"artifact report must be an object: {report!r}")
    if report.get("occurrence") != expected_id:
        raise RuntimeError(
            f"artifact occurrence mismatch: expected {expected_id}, "
            f"got {report.get('occurrence')!r}"
        )
    selector = report.get("selector")
    if not isinstance(selector, dict):
        raise RuntimeError(f"artifact selector must be an object: {report!r}")
    pre_state = selector.get("preState")
    if not isinstance(pre_state, dict) or set(pre_state) != {
        "targetFingerprint",
        "localContextFingerprint",
        "metavariableContextFingerprint",
        "goalCount",
    }:
        raise RuntimeError(f"artifact selector has invalid pre-state: {selector!r}")
    if any(
        not isinstance(pre_state[field], str)
        for field in (
            "targetFingerprint",
            "localContextFingerprint",
            "metavariableContextFingerprint",
        )
    ) or not isinstance(pre_state["goalCount"], int) or isinstance(
        pre_state["goalCount"], bool
    ):
        raise RuntimeError(f"artifact selector pre-state has invalid fields: {selector!r}")
    if not isinstance(selector.get("options"), str):
        raise RuntimeError(f"artifact selector options must be a string: {selector!r}")
    if selector.get("caller") is not None and not isinstance(selector.get("caller"), str):
        raise RuntimeError(f"artifact selector caller must be a string or null: {selector!r}")
    status = report.get("status")
    if status == "failure":
        if set(report) != {"occurrence", "selector", "status"}:
            raise RuntimeError(f"failure artifact contains success data: {report!r}")
        return report
    if status != "success":
        raise RuntimeError(f"artifact has invalid status: {report!r}")
    validate_environment_actions(
        report.get("environmentActions"),
        f"artifact environmentActions for {expected_id}",
    )
    locals_value = report.get("locals")
    if not isinstance(locals_value, list):
        raise RuntimeError(f"artifact locals must be an array: {report!r}")
    names: set[str] = set()
    previous_index = -1
    for local in locals_value:
        if not isinstance(local, dict):
            raise RuntimeError(f"artifact local must be an object: {local!r}")
        name = local.get("name")
        index = local.get("index")
        if not isinstance(name, str) or not IDENTIFIER_RE.fullmatch(name):
            raise RuntimeError(f"unsafe emitted local identifier: {name!r}")
        if name in names:
            raise RuntimeError(f"duplicate emitted local identifier: {name}")
        names.add(name)
        if not isinstance(index, int) or isinstance(index, bool) or index <= previous_index:
            raise RuntimeError(f"local declaration order is not strict: {locals_value!r}")
        previous_index = index
        validate_transformation(local.get("transformation"), f"local {name}")
    target = report.get("target")
    if target is not None:
        validate_transformation(target, "target")
    elif not locals_value:
        raise RuntimeError(f"artifact has neither locals nor target: {report!r}")

    # Target-only reports retain flat fields for compatibility. Keep them
    # checked against the structured target so the materializer never silently
    # emits a different transformation.
    flat = {
        "input": report.get("input"),
        "result": report.get("result"),
        "proof": report.get("proof"),
    }
    if target is not None and not locals_value:
        if flat != target:
            raise RuntimeError(f"flat/structured target report mismatch: {report!r}")
    return report


def selector_key(report: dict[str, object]) -> str:
    """Return the runtime-relevant selector key, excluding module provenance."""
    selector = report["selector"]
    if not isinstance(selector, dict):
        raise RuntimeError(f"artifact selector must be an object: {report!r}")
    return json.dumps(
        {
            "preState": selector["preState"],
            "options": selector["options"],
            "caller": selector["caller"],
        },
        sort_keys=True,
        separators=(",", ":"),
    )


def artifact_payload(report: dict[str, object]) -> str:
    return json.dumps(
        {key: value for key, value in report.items() if key not in {"selector"}},
        sort_keys=True,
        separators=(",", ":"),
    )


def group_report_variants(
    report_list: list[object],
    expected_ids: list[str],
    *,
    unobserved_ids: set[str] | None = None,
) -> dict[str, list[dict[str, object]]]:
    unobserved_ids = set() if unobserved_ids is None else unobserved_ids
    if not unobserved_ids.issubset(expected_ids):
        raise RuntimeError(
            f"unobserved occurrence IDs are not in the inventory: {sorted(unobserved_ids)}"
        )
    grouped: defaultdict[str, list[dict[str, object]]] = defaultdict(list)
    for raw_report in report_list:
        if not isinstance(raw_report, dict) or not isinstance(
            raw_report.get("occurrence"), str
        ):
            raise RuntimeError(f"artifact report has no string occurrence: {raw_report!r}")
        occurrence = raw_report["occurrence"]
        if occurrence not in expected_ids:
            raise RuntimeError(f"artifact report has unknown occurrence: {raw_report!r}")
        grouped[occurrence].append(validate_report(raw_report, occurrence))
    missing = set(expected_ids) - set(grouped)
    if set(grouped) - set(expected_ids) or missing != unobserved_ids:
        raise RuntimeError(
            f"artifact occurrence map mismatch: expected {expected_ids}, "
            f"found {sorted(grouped)}, explicitly unobserved {sorted(unobserved_ids)}"
        )

    result: dict[str, list[dict[str, object]]] = {}
    for occurrence in expected_ids:
        if occurrence in unobserved_ids:
            result[occurrence] = []
            continue
        by_selector: dict[str, dict[str, object]] = {}
        for report in grouped[occurrence]:
            key = selector_key(report)
            previous = by_selector.get(key)
            if previous is not None and artifact_payload(previous) != artifact_payload(report):
                raise RuntimeError(
                    f"ambiguous_boundary_variant:{occurrence}: selector={key}"
                )
            by_selector[key] = report
        result[occurrence] = [by_selector[key] for key in sorted(by_selector)]
    return result


def assert_grouping_rejections(report_list: list[object], expected_ids: list[str]) -> None:
    validate_environment_actions(
        [{"kind": "realize_reserved_name", "name": "«foo-bar».αfun.congr_simp"}],
        "quoted/unicode environment action",
    )
    try:
        group_report_variants([], expected_ids)
    except RuntimeError as error:
        if "artifact occurrence map mismatch" not in str(error):
            raise
    else:
        raise RuntimeError("missing artifact reports were accepted")

    success = next(
        (
            report
            for report in report_list
            if isinstance(report, dict) and report.get("status") == "success"
        ),
        None,
    )
    if success is None:
        raise RuntimeError("ambiguity rejection test requires a successful report")
    mutated = json.loads(json.dumps(success))
    target = mutated.get("target")
    if not isinstance(target, dict) or not isinstance(target.get("result"), str):
        raise RuntimeError("ambiguity rejection test requires target evidence")
    target["result"] += " "
    if not mutated["locals"]:
        mutated["result"] = target["result"]
    occurrence = str(success["occurrence"])
    try:
        group_report_variants([success, mutated], [occurrence])
    except RuntimeError as error:
        if "ambiguous_boundary_variant" not in str(error):
            raise
    else:
        raise RuntimeError("unequal artifacts under one selector were accepted")


def source_continuation_indent(source: bytes, start: int) -> str:
    line_start = source.rfind(b"\n", 0, start) + 1
    prefix = source[line_start:start].decode("utf-8")
    # Lean's offside rule is relative to the tactic token, not merely the
    # enclosing declaration's leading whitespace. This matters for occurrences
    # nested after `by`, in structure fields, or inside term arguments.
    return " " * (len(prefix.expandtabs(8)) + 2)


def indent_rendered_term(value: object, continuation_indent: str) -> str:
    if not isinstance(value, str):
        raise RuntimeError(f"rendered term is not a string: {value!r}")
    return value.replace("\n", "\n" + continuation_indent)


def format_transformation(
    transformation: dict[str, object], continuation_indent: str
) -> str:
    proof = transformation["proof"]
    input_term = indent_rendered_term(transformation["input"], continuation_indent)
    result_term = indent_rendered_term(transformation["result"], continuation_indent)
    using = (
        ""
        if proof is None
        else f" using {indent_rendered_term(proof, continuation_indent)}"
    )
    return f"({input_term} ==> {result_term}{using})"


def lean_string(value: str) -> str:
    """Render the selector's recorder-produced text as a Lean string literal."""
    return json.dumps(value, ensure_ascii=False)


def format_selector_values(report: dict[str, object]) -> str:
    selector = report["selector"]
    if not isinstance(selector, dict):
        raise RuntimeError(f"artifact selector must be an object: {report!r}")
    pre_state = selector["preState"]
    if not isinstance(pre_state, dict):
        raise RuntimeError(f"artifact pre-state must be an object: {report!r}")
    caller = selector["caller"]
    if caller is None:
        caller = ""
    return " ".join(
        [
            lean_string(str(pre_state["targetFingerprint"])),
            lean_string(str(pre_state["localContextFingerprint"])),
            lean_string(str(pre_state["metavariableContextFingerprint"])),
            str(pre_state["goalCount"]),
            lean_string(str(selector["options"])),
            lean_string(str(caller)),
        ]
    )


def format_variant_outcome(
    report: dict[str, object], continuation_indent: str
) -> str:
    if report["status"] == "failure":
        return "failure"

    def encoded(transformation: dict[str, object]) -> str:
        proof = transformation["proof"]
        result = (
            f"({lean_string(str(transformation['input']))} ==> "
            f"{lean_string(str(transformation['result']))}"
        )
        if proof is not None:
            result += f" using {lean_string(str(proof))}"
        return result + ")"

    target = report["target"]
    actions = validate_environment_actions(
        report.get("environmentActions"), "artifact environmentActions"
    )

    def encoded_prefix() -> str:
        if not actions:
            return "apply_encoded"
        encoded_actions = ", ".join(
            "realize_reserved_name " + lean_string(str(action["name"]))
            for action in actions
        )
        return f"apply_encoded_with_actions [{encoded_actions}]"

    if not report["locals"]:
        if target is None:
            raise RuntimeError(f"target-only report has no target evidence: {report!r}")
        return encoded_prefix() + " " + encoded(target)

    parts = [encoded_prefix()]
    for local in report["locals"]:
        parts.extend(
            [
                "at_index",
                str(local["index"]),
                encoded(local["transformation"]),
            ]
        )
    if target is not None:
        parts.extend(["⊢", encoded(target)])
    return " ".join(parts)


def format_report_variants(
    reports: list[dict[str, object]], continuation_indent: str = "  "
) -> str:
    if not reports:
        return "simp_engine_boundary_occurrence_unobserved"

    # Selection is non-backtracking: the dispatcher first chooses an exact
    # observed pre-state and only then executes its outcome. This preserves an
    # intentional failure so the unchanged surrounding `first`/`try` sees it.
    artifact_indent = continuation_indent + "  "
    parts = ["simp_engine_boundary_select"]
    for report in reports:
        parts.append(
            continuation_indent
            + "| "
            + format_selector_values(report)
            + " => "
            + format_variant_outcome(report, artifact_indent)
        )
    return "\n".join(parts)


def main() -> None:
    run(["lake", "build", "ExplicitLean:shared"])
    dylib = query_json_string(
        run(["lake", "query", "ExplicitLean:shared", "--json"]),
        "lake query ExplicitLean:shared",
    )
    entries = syntax_inventory_file(
        SOURCE, "Experiment.SimpEngineBoundarySourceInput", INVENTORY_TIMEOUT
    )
    if len(entries) != 17:
        raise RuntimeError(f"expected seventeen source occurrences, found {len(entries)}: {entries}")
    original = SOURCE.read_bytes()

    instrumented = rewrite_simp_heads(
        original,
        entries,
        lambda item: f'simp_engine_boundary_record "{item["id"]}"',
    )
    instrumented = inject_import(instrumented, "ExplicitLean.SimpEngine.Boundary")

    temporary_root = ROOT / ".lake"
    temporary_root.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="boundary-source-", dir=temporary_root) as raw_dir:
        work = Path(raw_dir)
        instrumented_path = work / "Instrumented.lean"
        instrumented_path.write_bytes(instrumented)
        output = compile_source(dylib, instrumented_path)
        report_list = [
            json.loads(line.split(ARTIFACT_MARKER, 1)[1])
            for line in output.splitlines()
            if ARTIFACT_MARKER in line
        ]
        expected_ids = [str(entry["id"]) for entry in entries]
        unobserved_ids = {
            str(entry["id"])
            for entry in entries
            if "zetaDelta := false" in str(entry["source"])
        }
        if len(unobserved_ids) != 1:
            raise RuntimeError(
                f"expected one explicitly unobserved fixture occurrence, found {unobserved_ids}"
            )
        assert_grouping_rejections(report_list, expected_ids)
        try:
            reports = group_report_variants(
                report_list, expected_ids, unobserved_ids=unobserved_ids
            )
        except RuntimeError as error:
            raise RuntimeError(f"{error}\n{output}") from error

        materialized = replace_all_occurrences(original, entries, reports)
        materialized = inject_import(
            materialized, "ExplicitLean.SimpEngine.Boundary.Tactic"
        )
        materialized_path = work / "Materialized.lean"
        materialized_path.write_bytes(materialized)
        compile_source(dylib, materialized_path)
        remaining = syntax_inventory_file(
            materialized_path,
            "Experiment.MaterializedBoundarySource",
            INVENTORY_TIMEOUT,
            allow_elaboration_errors=True,
        )
        if remaining:
            raise RuntimeError(f"materialized source retains simp occurrences: {remaining}")

    print("boundary source: seventeen occurrences materialized, including one explicit unobserved occurrence, compiled, zero remaining: ok")


if __name__ == "__main__":
    main()
