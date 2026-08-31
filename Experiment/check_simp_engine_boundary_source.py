#!/usr/bin/env python3
"""Record and materialize seventeen source occurrences end to end."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import tempfile

from simp_engine_inventory import inject_import, rewrite_simp_heads, syntax_inventory_file
from boundary_protocol import (
    ARTIFACT_KIND,
    ARTIFACT_SCHEMA,
    SEMANTIC_CONTRACT,
    SELECTOR_SCHEMA,
    assert_exact_source_preservation,
    check_recording_abort_markers,
    parse_framed_json_lines,
    recording_subprocess_environment,
    group_report_variants,
    replacement_plan,
    reject_forbidden_generated_text,
    validate_report,
    validate_environment_actions,
)


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Experiment" / "SimpEngineBoundarySourceInput.lean"
ARTIFACT_MARKER = "SIMP_ENGINE_BOUNDARY_ARTIFACT "
INVENTORY_TIMEOUT = 300


def run(
    command: list[str], timeout: int = 300, *, env: dict[str, str] | None = None
) -> str:
    result = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
        env=env,
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


def compile_source(
    dylib: str, source: Path, *, env: dict[str, str] | None = None
) -> str:
    command = ["lake", "env", "lean", f"--load-dynlib={dylib}"]
    # Instrumented and materialized copies live in different disposable
    # directories.  Give both the same source root so Lean assigns the same
    # logical module name; the generated artifact's module provenance is then
    # checked by the apply elaborator instead of being weakened for fixtures.
    if source.parent.name == "Experiment":
        command.extend(["-R", str(source.parent.parent)])
    command.append(str(source))
    return run(command, env=env)


def compile_recording_source(dylib: str, source: Path) -> tuple[str, str]:
    """Compile one instrumented source with an authenticated recording nonce."""
    environment, nonce = recording_subprocess_environment()
    return compile_source(dylib, source, env=environment), nonce


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
    artifact on the line. Contained occurrences are consumed with their outer
    root, which is the only place an artifact is emitted.
    """
    entries, _covered = replacement_plan(source, entries, "materialized source")
    for entry in entries:
        occurrence = str(entry["id"])
        if occurrence not in reports:
            raise RuntimeError(f"missing artifact report for {occurrence}")
    if set(reports) != {str(entry["id"]) for entry in entries}:
        raise RuntimeError("artifact reports must belong exactly to replacement roots")
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


def expect_validation_error(
    report: object,
    occurrence: str,
    message: str,
    *,
    expected_module: str | None = None,
) -> None:
    try:
        validate_report(report, occurrence, expected_module)
    except RuntimeError as error:
        if message not in str(error):
            raise RuntimeError(
                f"expected validation error containing {message!r}, got {error}"
            ) from error
    else:
        raise RuntimeError(f"invalid boundary mutation was accepted: {message}")


def assert_protocol_mutations(report_list: list[object], expected_ids: list[str]) -> None:
    """Exercise the closed protocol's fail-closed checks without Lean fixtures."""
    success = next(
        (
            report
            for report in report_list
            if isinstance(report, dict) and report.get("status") == "success"
        ),
        None,
    )
    failure = next(
        (
            report
            for report in report_list
            if isinstance(report, dict) and report.get("status") == "failure"
        ),
        None,
    )
    if not isinstance(success, dict) or not isinstance(failure, dict):
        raise RuntimeError("protocol mutation tests require both success and failure reports")
    occurrence = str(success["occurrence"])
    module = success["selector"]["module"]

    def copy_success() -> dict[str, object]:
        return json.loads(json.dumps(success))

    mutated = copy_success()
    mutated["unexpected"] = True
    expect_validation_error(mutated, occurrence, "success artifact has invalid fields")

    mutated = json.loads(json.dumps(failure))
    mutated["target"] = None
    expect_validation_error(
        mutated, str(failure["occurrence"]), "failure artifact contains success data"
    )

    mutated = copy_success()
    mutated["schema"] = True
    expect_validation_error(mutated, occurrence, "artifact schema must be an integer")
    mutated = copy_success()
    mutated["schema"] = ARTIFACT_SCHEMA + 1
    expect_validation_error(mutated, occurrence, "unsupported artifact schema")
    mutated = copy_success()
    mutated["kind"] = "wrong_kind"
    expect_validation_error(mutated, occurrence, "artifact has invalid kind")
    mutated = copy_success()
    mutated["semanticContract"] = "wrong_contract"
    expect_validation_error(mutated, occurrence, "artifact has invalid semantic contract")

    selector = copy_success()["selector"]
    if not isinstance(selector, dict):
        raise RuntimeError("protocol mutation test requires a selector")
    mutated = copy_success()
    mutated["selector"]["selectorSchema"] = True
    expect_validation_error(mutated, occurrence, "artifact selector schema must be an integer")
    mutated = copy_success()
    mutated["selector"]["selectorSchema"] = 2
    expect_validation_error(mutated, occurrence, "unsupported artifact selector schema")
    mutated = copy_success()
    mutated["selector"]["occurrence"] = "other_occurrence"
    expect_validation_error(mutated, occurrence, "artifact selector occurrence mismatch")
    mutated = copy_success()
    mutated["selector"]["module"] = "Other.Module"
    expect_validation_error(
        mutated, occurrence, "artifact selector module mismatch", expected_module=module
    )
    mutated = copy_success()
    mutated["selector"]["caller"] = True
    expect_validation_error(
        mutated,
        occurrence,
        "artifact selector caller must be a nonempty string or null",
    )
    mutated = copy_success()
    mutated["selector"]["caller"] = ""
    expect_validation_error(
        mutated,
        occurrence,
        "artifact selector caller must be a nonempty string or null",
    )
    mutated = copy_success()
    mutated["selector"]["preState"]["goalCount"] = True
    expect_validation_error(mutated, occurrence, "artifact selector preState.goalCount must be an integer")
    mutated = copy_success()
    mutated["selector"]["preState"]["goalCount"] = -1
    expect_validation_error(mutated, occurrence, "artifact selector preState.goalCount must be nonnegative")

    mutated = copy_success()
    mutated["stateDeltas"] = [{"kind": "unsupported"}]
    expect_validation_error(mutated, occurrence, "boundary_state_delta_unsupported")
    mutated = copy_success()
    mutated["encoding"]["term"] = "wrong_encoding"
    expect_validation_error(mutated, occurrence, "artifact has unsupported encoding")
    mutated = copy_success()
    mutated["terminal"] = {"closed": True}
    expect_validation_error(mutated, occurrence, "artifact has invalid terminal")

    local_report = next(
        (
            report
            for report in report_list
            if isinstance(report, dict)
            and report.get("status") == "success"
            and isinstance(report.get("locals"), list)
            and report["locals"]
        ),
        None,
    )
    if not isinstance(local_report, dict):
        raise RuntimeError("protocol mutation tests require local evidence")
    local_occurrence = str(local_report["occurrence"])

    def copy_local_report() -> dict[str, object]:
        return json.loads(json.dumps(local_report))

    mutated = copy_local_report()
    mutated["locals"][0]["reference"]["kind"] = "fvar_id"
    expect_validation_error(mutated, local_occurrence, "unsupported kind")
    mutated = copy_local_report()
    mutated["locals"][0]["reference"]["index"] = True
    expect_validation_error(mutated, local_occurrence, "index must be an integer")
    mutated = copy_local_report()
    mutated["locals"][0]["reference"]["index"] = -1
    expect_validation_error(mutated, local_occurrence, "index must be nonnegative")
    mutated = copy_local_report()
    mutated["locals"][0]["transformation"]["extra"] = True
    expect_validation_error(mutated, local_occurrence, "transformation has invalid fields")

    locals_value = local_report["locals"]
    if not isinstance(locals_value, list) or not locals_value:
        raise RuntimeError("protocol mutation test requires a local array")
    # The fixture currently has only one location occurrence in many runs.
    # Add a second structurally valid local record solely for testing the
    # ordering/uniqueness invariant; no generated source is materialized from
    # this synthetic mutation.
    pair_report = copy_local_report()
    first_local = json.loads(json.dumps(pair_report["locals"][0]))
    second_local = json.loads(json.dumps(first_local))
    first_local["reference"]["index"] = 1
    second_local["reference"]["index"] = 2
    pair_report["locals"] = [first_local, second_local]
    mutated = json.loads(json.dumps(pair_report))
    mutated["locals"][1]["reference"]["index"] = 1
    expect_validation_error(
        mutated, local_occurrence, "local declaration indices are not unique"
    )
    mutated = json.loads(json.dumps(pair_report))
    # Source order is not a numeric-order requirement.  A descending index
    # sequence is a valid representation of the recorder's authored local
    # order and must remain accepted.
    mutated["locals"][1]["reference"]["index"] = 0
    validate_report(mutated, local_occurrence, module)


def assert_grouping_rejections(
    report_list: list[object],
    expected_ids: list[str],
    expected_module: str,
) -> None:
    assert_protocol_mutations(report_list, expected_ids)
    validate_environment_actions(
        [{"kind": "realize_reserved_name", "name": "«foo-bar».αfun.congr_simp"}],
        "quoted/unicode environment action",
    )
    for actions in (
        [
            {"kind": "realize_reserved_name", "name": "z"},
            {"kind": "realize_reserved_name", "name": "a"},
        ],
        [
            {"kind": "realize_reserved_name", "name": "same"},
            {"kind": "realize_reserved_name", "name": "same"},
        ],
    ):
        try:
            validate_environment_actions(actions, "environment action mutation")
        except RuntimeError as error:
            if "strictly sorted and unique" not in str(error):
                raise
        else:
            raise RuntimeError("unsorted or duplicate environment actions were accepted")
    try:
        group_report_variants([], expected_ids, expected_module=expected_module)
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
    occurrence = str(success["occurrence"])
    try:
        group_report_variants(
            [success, mutated], [occurrence], expected_module=expected_module
        )
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


def format_artifact_header(report: dict[str, object]) -> str:
    """Render the closed artifact's provenance before any variant evidence."""
    selector = report["selector"]
    if not isinstance(selector, dict):
        raise RuntimeError(f"artifact selector must be an object: {report!r}")
    occurrence = report.get("occurrence")
    module = selector.get("module")
    if not isinstance(occurrence, str) or not occurrence:
        raise RuntimeError(f"artifact occurrence must be a nonempty string: {report!r}")
    if not isinstance(module, str) or not module:
        raise RuntimeError(f"artifact module must be a nonempty string: {report!r}")
    return (
        "(artifact_kind := "
        f"{lean_string(ARTIFACT_KIND)} artifact_schema := {ARTIFACT_SCHEMA} "
        f"selector_schema := {SELECTOR_SCHEMA} "
        "semantic_contract := "
        f"{lean_string(SEMANTIC_CONTRACT)} occurrence_id := {lean_string(occurrence)} "
        f"recorded_module := {lean_string(module)})"
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
        reference = local["reference"]
        parts.extend(
            [
                "at_index",
                str(reference["index"]),
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

    first_occurrence = reports[0].get("occurrence")
    if not isinstance(first_occurrence, str) or not first_occurrence:
        raise RuntimeError(f"artifact occurrence must be a nonempty string: {reports[0]!r}")
    first_selector = reports[0].get("selector")
    if not isinstance(first_selector, dict):
        raise RuntimeError(f"artifact selector must be an object: {reports[0]!r}")
    expected_module = first_selector.get("module")
    if not isinstance(expected_module, str) or not expected_module:
        raise RuntimeError(f"artifact module must be a nonempty string: {reports[0]!r}")
    for report in reports:
        validate_report(report, first_occurrence, expected_module)

    # Selection is non-backtracking: the dispatcher first chooses an exact
    # observed pre-state and only then executes its outcome. This preserves an
    # intentional failure so the unchanged surrounding `first`/`try` sees it.
    artifact_indent = continuation_indent + "  "
    parts = ["simp_engine_boundary_select"]
    parts.append(format_artifact_header(reports[0]))
    for report in reports:
        parts.append(
            continuation_indent
            + "| "
            + lean_string(str(report["occurrence"]))
            + " "
            + format_selector_values(report)
            + " => "
            + format_variant_outcome(report, artifact_indent)
        )
    return "\n".join(parts)


def header_fixture_source(
    kind: str,
    schema: int,
    selector_schema: int,
    contract: str,
    occurrence: str,
    module: str,
) -> str:
    """Make a tiny selector fixture whose outcome is never elaborated."""
    header = (
        "(artifact_kind := "
        f"{lean_string(kind)} artifact_schema := {schema} "
        f"selector_schema := {selector_schema} "
        "semantic_contract := "
        f"{lean_string(contract)} occurrence_id := {lean_string(occurrence)} "
        f"recorded_module := {lean_string(module)})"
    )
    # The fingerprints are intentionally arbitrary: header validation must
    # happen before selector matching, evidence elaboration, or environment
    # actions. The failure outcome also avoids depending on any term printer.
    return "\n".join(
        [
            "import ExplicitLean.SimpEngine.Boundary.Tactic",
            "theorem boundaryHeaderValidationFixture : True := by",
            f"  simp_engine_boundary_select {header}",
            f'    | {lean_string(occurrence or "headerMutation")} "target" "locals" "mvars" 1 "options" "" => failure',
            "",
        ]
    )


def assert_generated_header_rejections(
    dylib: str, work: Path, report: dict[str, object]
) -> None:
    """Check stable fail-closed errors before the generated tactic can run."""
    selector = report.get("selector")
    if not isinstance(selector, dict):
        raise RuntimeError("header mutation test requires a selector")
    occurrence = report.get("occurrence")
    module = selector.get("module")
    if not isinstance(occurrence, str) or not occurrence:
        raise RuntimeError("header mutation test requires a nonempty occurrence")
    if not isinstance(module, str) or not module:
        raise RuntimeError("header mutation test requires a nonempty module")

    cases = [
        (ARTIFACT_KIND, ARTIFACT_SCHEMA + 1, SELECTOR_SCHEMA, SEMANTIC_CONTRACT,
         occurrence, module,
         "unsupported_boundary_artifact_schema"),
        (ARTIFACT_KIND, ARTIFACT_SCHEMA, SELECTOR_SCHEMA + 1, SEMANTIC_CONTRACT,
         occurrence, module, "unsupported_boundary_selector_schema"),
        (ARTIFACT_KIND, ARTIFACT_SCHEMA, SELECTOR_SCHEMA, "wrong-contract",
         occurrence, module,
         "unsupported_boundary_semantic_contract"),
        ("wrong-kind", ARTIFACT_SCHEMA, SELECTOR_SCHEMA, SEMANTIC_CONTRACT,
         occurrence, module, "unsupported_boundary_artifact_kind"),
        (ARTIFACT_KIND, ARTIFACT_SCHEMA, SELECTOR_SCHEMA, SEMANTIC_CONTRACT, "", module,
         "invalid_boundary_occurrence"),
        (ARTIFACT_KIND, ARTIFACT_SCHEMA, SELECTOR_SCHEMA, SEMANTIC_CONTRACT,
         occurrence, "Other.Module",
         "boundary_module_mismatch"),
    ]
    mutation_root = work / "header-mutations"
    source_path = mutation_root / "Experiment" / SOURCE.name
    source_path.parent.mkdir(parents=True, exist_ok=True)
    for index, (kind, schema, selector_schema, contract, occ_id, module_name,
            expected_error) in enumerate(cases):
        source_path.write_text(
            header_fixture_source(
                kind, schema, selector_schema, contract, occ_id, module_name
            ),
            encoding="utf-8",
        )
        try:
            compile_source(dylib, source_path)
        except RuntimeError as error:
            if expected_error not in str(error):
                raise RuntimeError(
                    f"header mutation {index} expected {expected_error!r}, got {error}"
                ) from error
        else:
            raise RuntimeError(f"header mutation {index} was accepted")


def assert_caught_recording_abort_is_fatal(dylib: str, work: Path) -> None:
    """A caught post-stock recorder failure must not look unobserved."""
    fixture = work / "recording-abort" / "Experiment" / "SimpEngineBoundaryRecordingAbort.lean"
    fixture.parent.mkdir(parents=True, exist_ok=True)
    fixture.write_text(
        """module

import Mathlib
public meta import ExplicitLean.SimpEngine.Boundary

open Lean Meta Elab Tactic

syntax "boundary_abort_mutating_discharger" : tactic

elab_rules : tactic
  | `(tactic| boundary_abort_mutating_discharger) => withMainContext do
      addDecl <| .axiomDecl {
        name := `boundaryRecordingAbortCaught.abortHelper
        levelParams := []
        type := mkConst ``True
        isUnsafe := false
      }
      evalTactic (← `(tactic| assumption))

theorem boundaryRecordingAbortCaught (p q : Prop) (h : p) (hpq : p → q) : q := by
  first
  | simp_engine_boundary_record "recording-abort-test"
      (disch := boundary_abort_mutating_discharger) [hpq]
  | exact hpq h
""",
        encoding="utf-8",
    )
    output, nonce = compile_recording_source(dylib, fixture)
    artifact_reports = parse_framed_json_lines(
        output,
        marker=ARTIFACT_MARKER,
        expected_nonce=nonce,
        label="boundary artifact",
    )
    if artifact_reports:
        raise RuntimeError(
            "post-stock recording abort incorrectly emitted a usable artifact report\n"
            + output
        )
    try:
        check_recording_abort_markers(
            output,
            expected_nonce=nonce,
            expected_occurrence="recording-abort-test",
            expected_module="Experiment.SimpEngineBoundaryRecordingAbort",
        )
    except RuntimeError as error:
        if "boundary recording abort" not in str(error):
            raise
    else:
        raise RuntimeError(
            "caught post-stock recorder failure emitted no durable abort marker\n"
            + output
        )


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

    instrumented_without_import = rewrite_simp_heads(
        original,
        entries,
        lambda item: f'simp_engine_boundary_record "{item["id"]}"',
    )
    instrumented = inject_import(
        instrumented_without_import, "ExplicitLean.SimpEngine.Boundary"
    )
    expected_module = "Experiment.SimpEngineBoundarySourceInput"
    assert_exact_source_preservation(
        original,
        instrumented,
        entries,
        imported="ExplicitLean.SimpEngine.Boundary",
        label="instrumented source Experiment.SimpEngineBoundarySourceInput",
        expected_without_import=instrumented_without_import,
    )

    temporary_root = ROOT / ".lake"
    temporary_root.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="boundary-source-", dir=temporary_root) as raw_dir:
        work = Path(raw_dir)
        instrumented_path = work / "instrumented" / "Experiment" / SOURCE.name
        instrumented_path.parent.mkdir(parents=True, exist_ok=True)
        instrumented_path.write_bytes(instrumented)
        output, nonce = compile_recording_source(dylib, instrumented_path)
        check_recording_abort_markers(
            output, expected_nonce=nonce, expected_module=expected_module
        )
        report_list = parse_framed_json_lines(
            output,
            marker=ARTIFACT_MARKER,
            expected_nonce=nonce,
            label="boundary artifact",
        )
        reject_forbidden_generated_text(report_list, "boundary artifact reports")
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
        assert_grouping_rejections(report_list, expected_ids, expected_module)
        try:
            reports = group_report_variants(
                report_list,
                expected_ids,
                expected_module=expected_module,
                unobserved_ids=unobserved_ids,
            )
        except RuntimeError as error:
            raise RuntimeError(f"{error}\n{output}") from error

        materialized_without_import = replace_all_occurrences(original, entries, reports)
        materialized = inject_import(
            materialized_without_import, "ExplicitLean.SimpEngine.Boundary.Tactic"
        )
        assert_exact_source_preservation(
            original,
            materialized,
            entries,
            imported="ExplicitLean.SimpEngine.Boundary.Tactic",
            label="materialized source Experiment.SimpEngineBoundarySourceInput",
            expected_without_import=materialized_without_import,
        )
        materialized_path = work / "materialized" / "Experiment" / SOURCE.name
        materialized_path.parent.mkdir(parents=True, exist_ok=True)
        materialized_path.write_bytes(materialized)
        success = next(
            report
            for report in report_list
            if isinstance(report, dict) and report.get("status") == "success"
        )
        assert_generated_header_rejections(dylib, work, success)
        assert_caught_recording_abort_is_fatal(dylib, work)
        compile_source(dylib, materialized_path)
        remaining = syntax_inventory_file(
            materialized_path,
            "Experiment.SimpEngineBoundarySourceInput.materialized",
            INVENTORY_TIMEOUT,
            allow_elaboration_errors=True,
        )
        if remaining:
            raise RuntimeError(f"materialized source retains simp occurrences: {remaining}")

    print("boundary source: seventeen occurrences materialized, including one explicit unobserved occurrence, compiled, zero remaining: ok")


if __name__ == "__main__":
    main()
