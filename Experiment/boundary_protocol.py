"""Shared protocol definitions and validators for boundary artifacts.

The Lean recorder and the Python materializers intentionally share these
literal protocol values.  This module is the single Python implementation of
the wire-format checks; source rewriting and report reduction should not
reimplement them independently.
"""

from __future__ import annotations

from collections import defaultdict
import difflib
import json
import os
import re
import secrets
from typing import Any, Iterable

from boundary_expr_codec import (
    validate_boundary_expr_dag, validate_reference_expr_dag, reference_expr_is_constant, validate_expr_dag, validate_struct_expr_dag,
    validate_theorem_payload, validate_congruence_payload, validate_equation_payload,
    validate_matcher_payload, validate_local_theorems_payload, validate_realization_payload,
    expr_is_constant, validate_declaration_branch_payload,
)


# Keep these values synchronized with the public constants in
# ExplicitLean/SimpEngine/Boundary/Apply.lean.
ARTIFACT_KIND = "simp_engine_boundary_artifact"
ARTIFACT_SCHEMA = 5
SEMANTIC_CONTRACT = "boundary-observable-v1"
SELECTOR_SCHEMA = 2

SUCCESS_STATUS = "success"
FAILURE_STATUS = "failure"
TERMINALS = {
    "open",
    "closed_from_local_false",
    "closed_from_target_true",
}

# These strings are part of the artifact wire format. The encoding describes
# how the materializer interprets a field, not a printer or implementation
# module version.
TERM_ENCODING = "lean_expr_dag_v3"
LOCAL_REFERENCE_ENCODING = "local_decl_index_v1"
UNIVERSE_ENCODING = "pre_boundary_universe_reference_v1"
INSTANCE_ENCODING = "explicit_terms_v1"
ENCODING = {
    "terms": TERM_ENCODING,
    "locals": LOCAL_REFERENCE_ENCODING,
    "universes": UNIVERSE_ENCODING,
    "expressionReferences": "pre_boundary_expression_reference_v1",
    "instances": INSTANCE_ENCODING,
}

# This is the exact protocol identity embedded in materialization
# reports. Keep the object deliberately small: the report is identified by
# the artifact wire format, not by a Python runner or a Mathlib shard.
ARTIFACT_PROTOCOL = {
    "kind": ARTIFACT_KIND,
    "schema": ARTIFACT_SCHEMA,
    "semanticContract": SEMANTIC_CONTRACT,
    "selectorSchema": SELECTOR_SCHEMA,
    "encoding": ENCODING,
}

SELECTOR_FIELDS = frozenset(
    {"selectorSchema", "occurrence", "preState", "options", "module", "caller"}
)
PRE_STATE_FIELDS = frozenset(
    {
        "targetFingerprint",
        "localContextFingerprint",
        "metavariableContextFingerprint",
        "goalCount",
    }
)
SUCCESS_REPORT_FIELDS = frozenset(
    {
        "kind",
        "schema",
        "semanticContract",
        "occurrence",
        "selector",
        "status",
        "stockGenerator",
        "terminal",
        "encoding",
        "stateDeltas",
        "environmentActions",
        "locals",
        "target",
    }
)

GENERATOR_FIELDS = frozenset({"namePrefix", "idx", "parentIdxs"})


def validate_stock_generator(
    value: object, label: str = "artifact stockGenerator"
) -> dict[str, object]:
    """Validate the structural post-stock DeclNameGenerator witness."""
    if not isinstance(value, dict) or set(value) != GENERATOR_FIELDS:
        raise RuntimeError(f"{label} has invalid fields: {value!r}")
    prefix = value["namePrefix"]
    if not isinstance(prefix, list):
        raise RuntimeError(f"{label}.namePrefix must be a structural Name array: {prefix!r}")
    for position, part in enumerate(prefix):
        if not isinstance(part, list) or len(part) != 2:
            raise RuntimeError(f"{label}.namePrefix[{position}] is invalid: {part!r}")
        if part[0] == "s":
            if not isinstance(part[1], str):
                raise RuntimeError(f"{label}.namePrefix string component is invalid: {part!r}")
        elif part[0] == "n":
            if not isinstance(part[1], int) or isinstance(part[1], bool) or part[1] < 0:
                raise RuntimeError(f"{label}.namePrefix numeric component is invalid: {part!r}")
        else:
            raise RuntimeError(f"{label}.namePrefix component tag is invalid: {part!r}")
    _require_int(value["idx"], f"{label}.idx", nonnegative=True)
    parents = value["parentIdxs"]
    if not isinstance(parents, list):
        raise RuntimeError(f"{label}.parentIdxs must be an array: {parents!r}")
    for position, parent in enumerate(parents):
        _require_int(parent, f"{label}.parentIdxs[{position}]", nonnegative=True)
    return value
FAILURE_REPORT_FIELDS = frozenset(
    {"kind", "schema", "semanticContract", "occurrence", "selector", "status"}
)
LOCAL_FIELDS = frozenset({"reference", "userName", "transformation"})
LOCAL_REFERENCE_FIELDS = frozenset({"kind", "index"})
TRANSFORMATION_FIELDS = frozenset({"input", "result", "proof"})
ENVIRONMENT_ACTION_KINDS = {"reserve_declaration_branch", "declare_congruence", "declare_equation", "declare_matcher", "declare_local_theorems", "realize_groups"}

# These are successful per-occurrence outcomes.  They must not be confused
# with abort categories: an abort stops the run and publishes no successful
# occurrence classification.
OCCURRENCE_CLASSIFICATIONS = {
    "materialized",
    "expected_failure",
    "unobserved_executable",
    "covered_by_ancestor",
    "retained_syntax_data",
}
ABORT_CATEGORIES = {
    "printer_failure",
    "ambiguous_boundary_variant",
    "external_effect_failure",
    "declaration_value_mismatch",
    "environment_delta_mismatch",
}

UNSTABLE_RENDER_RE = re.compile(r"\?[_A-Za-z]")
FORBIDDEN_AXIOM = "sorryAx"
FORBIDDEN_TOKEN_RE = re.compile(
    r"(?<![A-Za-z0-9_'])(?:sorry|admit)(?![A-Za-z0-9_'])"
)

# A recorder can fail while fingerprinting or after stock ``simp`` has already
# run. The enclosing tactic may catch that exception and continue, so this
# marker is the durable nonce-framed process record that prevents consumers
# from mistaking the occurrence for an unobserved call.
RECORDING_ABORT_MARKER = "SIMP_ENGINE_BOUNDARY_RECORDING_ABORT "
RECORDING_ABORT_KIND = "simp_engine_boundary_recording_abort"
RECORDING_ABORT_SCHEMA = 1
RECORDING_ABORT_FIELDS = frozenset(
    {"kind", "schema", "occurrence", "module", "stage", "detail"}
)
REPLAY_ABORT_MARKER = "SIMP_ENGINE_BOUNDARY_REPLAY_ABORT "
REPLAY_ABORT_KIND = "simp_engine_boundary_replay_abort"
REPLAY_ABORT_SCHEMA = 1
REPLAY_GUARD_KIND = "simp_engine_boundary_replay_guard"
REPLAY_GUARD_SCHEMA = 1

# Marker lines cross a compiler-process boundary through combined stdout and
# stderr.  Authored Lean diagnostics can contain the old marker text, so every
# production recording process gets a fresh nonce and consumers accept only
# the exact marker/nonce/JSON framing for that process.  The explicit token is
# for direct probes that intentionally do not arrange a recording environment;
# it is not authentication for a production run.
RUN_NONCE_ENV = "SIMP_ENGINE_BOUNDARY_RUN_NONCE"
UNAUTHENTICATED_RUN_NONCE = "unauthenticated"


def fresh_run_nonce() -> str:
    """Return a high-entropy nonce for one compiler subprocess."""
    return secrets.token_urlsafe(32)


def recording_subprocess_environment() -> tuple[dict[str, str], str]:
    """Copy the current environment and add a fresh compiler-process nonce."""
    nonce = fresh_run_nonce()
    environment = os.environ.copy()
    environment[RUN_NONCE_ENV] = nonce
    return environment, nonce


def replay_subprocess_environment() -> tuple[dict[str, str], str]:
    """Use the same runtime framing protocol with a fresh replay-process nonce."""
    return recording_subprocess_environment()


def marker_prefix(marker: str, nonce: str) -> str:
    """Build the exact prefix used by a framed JSON marker line."""
    if not marker or not marker.endswith(" "):
        raise RuntimeError(f"marker must end in one framing space: {marker!r}")
    if not nonce or any(character.isspace() for character in nonce):
        raise RuntimeError(f"marker nonce must be nonempty and whitespace-free: {nonce!r}")
    return marker + nonce + " "


def parse_framed_json_lines(
    output: str,
    *,
    marker: str,
    expected_nonce: str,
    label: str,
) -> list[object]:
    """Parse only marker lines authenticated by ``expected_nonce``.

    A line beginning with the marker but carrying a different nonce or any
    other framing is rejected.  Marker text appearing later in ordinary
    compiler output is not treated as a report.
    """
    prefix = marker_prefix(marker, expected_nonce)
    reports: list[object] = []
    for line in output.splitlines():
        if line.startswith(marker) and not line.startswith(prefix):
            raise RuntimeError(f"{label} marker has wrong nonce or framing: {line!r}")
        if not line.startswith(prefix):
            continue
        payload = line[len(prefix) :]
        if not payload:
            raise RuntimeError(f"{label} marker has an empty JSON payload")
        try:
            reports.append(json.loads(payload))
        except json.JSONDecodeError as error:
            raise RuntimeError(f"invalid {label} marker line: {line}") from error
    return reports


def _require_int(value: object, label: str, *, nonnegative: bool = False) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise RuntimeError(f"{label} must be an integer: {value!r}")
    if nonnegative and value < 0:
        raise RuntimeError(f"{label} must be nonnegative: {value!r}")
    return value


def _require_nonempty_string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise RuntimeError(f"{label} must be a nonempty string: {value!r}")
    return value


def artifact_protocol() -> dict[str, object]:
    """Return a fresh copy of the artifact protocol identity."""
    return {
        "kind": ARTIFACT_KIND,
        "schema": ARTIFACT_SCHEMA,
        "semanticContract": SEMANTIC_CONTRACT,
        "selectorSchema": SELECTOR_SCHEMA,
        "encoding": dict(ENCODING),
    }


def validate_artifact_protocol(
    value: object, label: str = "artifactProtocol"
) -> dict[str, object]:
    """Validate the exact artifact identity carried by a shard report."""
    if not isinstance(value, dict) or set(value) != set(ARTIFACT_PROTOCOL):
        raise RuntimeError(f"{label} has invalid fields: {value!r}")
    if value["kind"] != ARTIFACT_KIND:
        raise RuntimeError(f"{label} has invalid kind: {value!r}")
    if _require_int(value["schema"], f"{label}.schema") != ARTIFACT_SCHEMA:
        raise RuntimeError(f"{label} has unsupported schema: {value!r}")
    if value["semanticContract"] != SEMANTIC_CONTRACT:
        raise RuntimeError(f"{label} has invalid semantic contract: {value!r}")
    if (
        _require_int(value["selectorSchema"], f"{label}.selectorSchema")
        != SELECTOR_SCHEMA
    ):
        raise RuntimeError(f"{label} has unsupported selector schema: {value!r}")
    if value["encoding"] != ENCODING:
        raise RuntimeError(f"{label} has unsupported encoding: {value!r}")
    return value


def validate_rendered_term(value: object, label: str) -> str:
    validate_reference_expr_dag(value, label)
    return value


def validate_transformation(value: object, label: str) -> dict[str, object]:
    if not isinstance(value, dict) or set(value) != TRANSFORMATION_FIELDS:
        raise RuntimeError(f"{label} has invalid fields: {value!r}")
    validate_rendered_term(value["input"], f"{label} input")
    validate_rendered_term(value["result"], f"{label} result")
    proof = value["proof"]
    if proof is not None:
        validate_rendered_term(proof, f"{label} proof")
    return value


def validate_environment_actions(value: object, label: str) -> list[dict[str, object]]:
    if not isinstance(value, list):
        raise RuntimeError(f"{label} must be an array: {value!r}")
    result: list[dict[str, object]] = []
    previous_name: str | None = None
    seen_names: set[str] = set()
    for action in value:
        if not isinstance(action, dict) or set(action) != {"kind", "name", "nameParts", "declaration"}:
            raise RuntimeError(f"{label} contains an invalid action: {action!r}")
        if (
            not isinstance(action["kind"], str)
            or action["kind"] not in ENVIRONMENT_ACTION_KINDS
        ):
            raise RuntimeError(f"{label} contains an unsupported action: {action!r}")
        name = _require_nonempty_string(action["name"], f"{label} reserved name")
        if previous_name is not None and name <= previous_name:
            raise RuntimeError(
                f"{label} reserved names must be strictly sorted and unique: {value!r}"
            )
        if action["kind"] == "reserve_declaration_branch" and len(value) != 1:
            raise RuntimeError(f"{label}: reservation must be the sole action")
        validator = {"reserve_declaration_branch": validate_declaration_branch_payload,
                     "declare_congruence": validate_congruence_payload,
                     "declare_equation": validate_equation_payload,
                     "declare_matcher": validate_matcher_payload,
                     "declare_local_theorems": validate_local_theorems_payload,
                     "realize_groups": validate_realization_payload}[action["kind"]]
        validator(action["declaration"], action["nameParts"], label)
        exact_name = json.dumps(action["nameParts"], separators=(",", ":"))
        if exact_name in seen_names:
            raise RuntimeError(f"{label} reserved names must be strictly sorted and unique")
        seen_names.add(exact_name)
        previous_name = name
        result.append(action)
    return result


def validate_selector(
    value: object,
    expected_occurrence: str,
    expected_module: str | None = None,
) -> dict[str, object]:
    if not isinstance(value, dict) or set(value) != SELECTOR_FIELDS:
        raise RuntimeError(f"artifact selector has invalid fields: {value!r}")
    schema = value["selectorSchema"]
    if _require_int(schema, "artifact selector schema") != SELECTOR_SCHEMA:
        raise RuntimeError(f"unsupported artifact selector schema: {schema!r}")
    occurrence = _require_nonempty_string(
        value["occurrence"], "artifact selector occurrence"
    )
    if occurrence != expected_occurrence:
        raise RuntimeError(
            f"artifact selector occurrence mismatch: expected {expected_occurrence}, "
            f"got {occurrence!r}"
        )
    pre_state = value["preState"]
    if not isinstance(pre_state, dict) or set(pre_state) != PRE_STATE_FIELDS:
        raise RuntimeError(f"artifact selector has invalid pre-state: {value!r}")
    for field in (
        "targetFingerprint",
        "localContextFingerprint",
        "metavariableContextFingerprint",
    ):
        _require_nonempty_string(pre_state[field], f"artifact selector preState.{field}")
    _require_int(pre_state["goalCount"], "artifact selector preState.goalCount", nonnegative=True)
    _require_nonempty_string(value["options"], "artifact selector options")
    module = _require_nonempty_string(value["module"], "artifact selector module")
    if expected_module is not None and module != expected_module:
        raise RuntimeError(
            f"artifact selector module mismatch: expected {expected_module!r}, got {module!r}"
        )
    caller = value["caller"]
    if caller is not None and (
        not isinstance(caller, str) or not caller
    ):
        raise RuntimeError(
            f"artifact selector caller must be a nonempty string or null: {caller!r}"
        )
    return value


def validate_local_reference(value: object, label: str) -> dict[str, object]:
    if not isinstance(value, dict) or set(value) != LOCAL_REFERENCE_FIELDS:
        raise RuntimeError(f"{label} has invalid fields: {value!r}")
    if value["kind"] != "local_decl_index":
        raise RuntimeError(f"{label} has unsupported kind: {value!r}")
    _require_int(value["index"], f"{label} index", nonnegative=True)
    return value


def validate_local(value: object, label: str) -> dict[str, object]:
    if not isinstance(value, dict) or set(value) != LOCAL_FIELDS:
        raise RuntimeError(f"{label} has invalid fields: {value!r}")
    if not isinstance(value["userName"], str):
        raise RuntimeError(f"{label} userName must be a string: {value!r}")
    validate_local_reference(value["reference"], f"{label} reference")
    validate_transformation(value["transformation"], f"{label} transformation")
    return value


def validate_report(
    report: object,
    expected_occurrence: str,
    expected_module: str | None = None,
) -> dict[str, object]:
    if not isinstance(report, dict):
        raise RuntimeError(f"artifact report must be an object: {report!r}")
    if report.get("kind") != ARTIFACT_KIND:
        raise RuntimeError(f"artifact has invalid kind: {report!r}")
    schema = report.get("schema")
    if _require_int(schema, "artifact schema") != ARTIFACT_SCHEMA:
        raise RuntimeError(f"unsupported artifact schema: {schema!r}")
    if report.get("semanticContract") != SEMANTIC_CONTRACT:
        raise RuntimeError(f"artifact has invalid semantic contract: {report!r}")
    occurrence = report.get("occurrence")
    if not isinstance(occurrence, str) or not occurrence:
        raise RuntimeError(f"artifact occurrence must be a nonempty string: {report!r}")
    if occurrence != expected_occurrence:
        raise RuntimeError(
            f"artifact occurrence mismatch: expected {expected_occurrence}, "
            f"got {report.get('occurrence')!r}"
        )
    status = report.get("status")
    if (
        not isinstance(status, str)
        or status not in {SUCCESS_STATUS, FAILURE_STATUS}
    ):
        raise RuntimeError(f"artifact has invalid status: {report!r}")
    validate_selector(report.get("selector"), expected_occurrence, expected_module)
    if status == FAILURE_STATUS:
        if set(report) != FAILURE_REPORT_FIELDS:
            raise RuntimeError(f"failure artifact contains success data: {report!r}")
        return report

    if set(report) != SUCCESS_REPORT_FIELDS:
        raise RuntimeError(f"success artifact has invalid fields: {report!r}")
    validate_stock_generator(report["stockGenerator"])
    terminal = report["terminal"]
    if not isinstance(terminal, str) or terminal not in TERMINALS:
        raise RuntimeError(f"artifact has invalid terminal: {terminal!r}")
    if report["encoding"] != ENCODING:
        raise RuntimeError(f"artifact has unsupported encoding: {report!r}")
    if report["stateDeltas"] != []:
        raise RuntimeError(
            "boundary_state_delta_unsupported: artifact stateDeltas must be exactly []"
        )
    validate_environment_actions(report["environmentActions"], "artifact environmentActions")
    locals_value = report["locals"]
    if not isinstance(locals_value, list):
        raise RuntimeError(f"artifact locals must be an array: {report!r}")
    local_indices: set[int] = set()
    for position, local in enumerate(locals_value):
        label = f"artifact local[{position}]"
        validate_local(local, label)
        reference = local["reference"]
        index = int(reference["index"])
        if index in local_indices:
            raise RuntimeError(
                f"local declaration indices are not unique: {locals_value!r}"
            )
        local_indices.add(index)
    target = report["target"]
    if target is not None:
        validate_transformation(target, "artifact target")
    elif not locals_value:
        raise RuntimeError(f"artifact has neither locals nor target: {report!r}")
    local_closed_false = any(
        reference_expr_is_constant(local["transformation"]["result"], "False")
        for local in locals_value
    )
    target_closed_true = (
        target is not None and reference_expr_is_constant(target["result"], "True")
    )
    if terminal == "closed_from_local_false":
        if not local_closed_false or target is not None:
            raise RuntimeError(
                "closed_from_local_false requires a local False result and no "
                "surviving target"
            )
    elif terminal == "closed_from_target_true":
        if not target_closed_true or local_closed_false:
            raise RuntimeError(
                "closed_from_target_true requires a target True result and no "
                "earlier local False result"
            )
    elif local_closed_false or target_closed_true:
        raise RuntimeError(
            "open terminal contradicts a local False or target True closure result"
        )
    return report


def _walk_strings(value: object) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for key, child in value.items():
            if isinstance(key, str):
                yield key
            yield from _walk_strings(child)
    elif isinstance(value, (list, tuple)):
        for child in value:
            yield from _walk_strings(child)


def reject_forbidden_generated_text(value: object, label: str) -> None:
    """Reject proof-hole axioms and hole tokens in generated protocol data."""
    for text in _walk_strings(value):
        # A literal string inside a closed expression is data, not Lean source.
        # Inspect the DAG's constant nodes rather than searching its JSON text.
        if text.startswith("["):
            try:
                encoded = json.loads(text)
            except (ValueError, RecursionError):
                encoded = None
            if isinstance(encoded, list) and encoded:
                if encoded[0] == "boundary_declaration_branch_v1":
                    validate_declaration_branch_payload(text, None, label)
                    continue
                if encoded[0] == "expr_dag_v3":
                    validate_reference_expr_dag(text, label)
                    continue
                if encoded[0] == "expr_dag_v2":
                    validate_boundary_expr_dag(text, label)
                    continue
                if encoded[0] == "expr_dag_v1":
                    validate_expr_dag(text, label)
                    continue
                if encoded[0] == "expr_struct_dag_v1":
                    validate_struct_expr_dag(text, label)
                    continue
                if encoded[0] == "boundary_equation_v1":
                    validate_equation_payload(text, None, label)
                    continue
                if encoded[0] == "boundary_congruence_v1":
                    validate_congruence_payload(text, None, label)
                    continue
                if encoded[0] == "boundary_theorem_dag_v1":
                    validate_theorem_payload(text, encoded[1] if len(encoded) > 1 else None, label)
                    continue
                if encoded[0] == "boundary_local_theorems_bundle_v1":
                    validate_local_theorems_payload(text, encoded[1] if len(encoded) > 1 else None, label)
                    continue
                if encoded[0] == "boundary_local_equation_sequence_v1":
                    validate_realization_payload(text, encoded[1] if len(encoded) == 11 else None, label)
                    continue
                if encoded[0] in ("boundary_cached_congruence_sequence_v1", "boundary_cached_congruence_sequence_v2"):
                    validate_realization_payload(text, encoded[1] if len(encoded) == 7 else None, label)
                    continue
                if encoded[0] in ("boundary_local_cached_v1", "boundary_local_cached_aux_v1", "boundary_local_cached_congruence_v1", "boundary_local_cached_congruence_v2", "boundary_local_cached_equation_v2"):
                    anchor = encoded[10][1] if (len(encoded) == 11 and isinstance(encoded[10], list)
                                                and len(encoded[10]) == 5) else None
                    validate_realization_payload(text, anchor, label)
                    continue
                if encoded[0] == "boundary_realization_batch_v1":
                    validate_realization_payload(text, encoded[10][0][1] if len(encoded) == 11 and encoded[10] else None, label)
                    continue
                if encoded[0] == "boundary_realization_batch_v2":
                    anchor = None
                    if (len(encoded) == 12 and isinstance(encoded[10], list)
                            and isinstance(encoded[11], list) and encoded[11]
                            and type(encoded[11][0]) is int
                            and 0 <= encoded[11][0] < len(encoded[10])):
                        node = encoded[10][encoded[11][0]]
                        if isinstance(node, list) and len(node) == 6:
                            anchor = node[2]
                    validate_realization_payload(text, anchor, label)
                    continue
                if encoded[0] == "boundary_local_cached_sequence_v1":
                    anchor = encoded[1][0] if len(encoded) == 8 and isinstance(encoded[1], list) and encoded[1] else None
                    validate_realization_payload(text, anchor, label)
                    continue
                if encoded[0] == "boundary_realization_sequence_v1":
                    anchor = None
                    if (len(encoded) == 13 and isinstance(encoded[10], list)
                            and isinstance(encoded[12], list) and encoded[12]):
                        step = next((step for step in encoded[12] if isinstance(step, list)
                                     and step and step[0] != "registration"), None)
                        if isinstance(step, list) and step:
                            if step[0] == "helper" and len(step) == 5:
                                anchor = step[1]
                            elif (step[0] == "group" and len(step) == 2 and type(step[1]) is int
                                  and 0 <= step[1] < len(encoded[10])):
                                node = encoded[10][step[1]]
                                if isinstance(node, list) and len(node) == 6:
                                    anchor = node[2]
                    validate_realization_payload(text, anchor, label)
                    continue
                if encoded[0] in {"boundary_matcher_bundle_v1", "boundary_matcher_bundle_v2", "boundary_matcher_bundle_v3"}:
                    validate_matcher_payload(text, encoded[1] if len(encoded) > 1 else None, label)
                    continue
        if FORBIDDEN_AXIOM in text:
            raise RuntimeError(f"{label} contains forbidden {FORBIDDEN_AXIOM}")
        match = FORBIDDEN_TOKEN_RE.search(text)
        if match:
            raise RuntimeError(
                f"{label} contains introduced forbidden token {match.group(0)!r}"
            )


def check_recording_abort_markers(
    output: str,
    *,
    expected_nonce: str,
    expected_occurrence: str | None = None,
    expected_module: str | None = None,
) -> None:
    """Fail closed if a recorder reported an infrastructure failure.

    The marker is deliberately parsed even when another valid marker was
    already found, so a malformed second marker cannot be hidden behind the
    first.  A valid marker always raises: callers must never classify it as an
    unobserved occurrence.
    """
    _check_abort_markers(
        output, marker=RECORDING_ABORT_MARKER, kind=RECORDING_ABORT_KIND,
        schema=RECORDING_ABORT_SCHEMA, label="recording",
        expected_nonce=expected_nonce, expected_occurrence=expected_occurrence,
        expected_module=expected_module,
    )


def check_replay_abort_markers(
    output: str, *, expected_nonce: str,
    expected_occurrence: str | None = None, expected_module: str | None = None,
) -> None:
    """Reject replay infrastructure errors even when Lean caught the exception.

    A deliberately selected recorded stock failure emits no replay-abort marker.
    All marker lines, including malformed or unauthenticated ones, fail closed.
    """
    _check_abort_markers(
        output, marker=REPLAY_ABORT_MARKER, kind=REPLAY_ABORT_KIND,
        schema=REPLAY_ABORT_SCHEMA, label="replay",
        expected_nonce=expected_nonce, expected_occurrence=expected_occurrence,
        expected_module=expected_module,
    )


def _check_abort_markers(
    output: str, *, marker: str, kind: str, schema: int, label: str,
    expected_nonce: str, expected_occurrence: str | None,
    expected_module: str | None,
) -> None:
    markers: list[dict[str, object]] = []
    for raw in parse_framed_json_lines(
        output,
        marker=marker,
        expected_nonce=expected_nonce,
        label=f"boundary {label}-abort",
    ):
        value = raw
        if not isinstance(value, dict) or set(value) != RECORDING_ABORT_FIELDS:
            raise RuntimeError(
                f"malformed boundary {label}-abort marker fields: {value!r}"
            )
        if value["kind"] != kind:
            raise RuntimeError(
                f"malformed boundary {label}-abort marker kind: {value!r}"
            )
        actual_schema = value["schema"]
        if (
            isinstance(actual_schema, bool)
            or not isinstance(actual_schema, int)
            or actual_schema != schema
        ):
            raise RuntimeError(
                f"malformed boundary {label}-abort marker schema: {value!r}"
            )
        occurrence = _require_nonempty_string(
            value["occurrence"], f"{label}-abort occurrence"
        )
        if expected_occurrence is not None and occurrence != expected_occurrence:
            raise RuntimeError(
                f"boundary {label}-abort occurrence mismatch: "
                f"expected {expected_occurrence!r}, got {occurrence!r}"
            )
        module = _require_nonempty_string(value["module"], f"{label}-abort module")
        if expected_module is not None and module != expected_module:
            raise RuntimeError(
                f"boundary {label}-abort module mismatch: "
                f"expected {expected_module!r}, got {module!r}"
            )
        _require_nonempty_string(value["stage"], f"{label}-abort stage")
        _require_nonempty_string(value["detail"], f"{label}-abort detail")
        markers.append(value)
    if markers:
        first = markers[0]
        raise RuntimeError(
            f"boundary {label} abort: "
            f"occurrence={first['occurrence']!r}, stage={first['stage']!r}, "
            f"detail={first['detail']}"
        )


def _without_import_candidates(source: bytes, imported: str) -> list[bytes]:
    """Return the two supported, unambiguous import-removal candidates.

    The source checker injects a leading newline with the import, while the
    shard runner inserts the import immediately after the authored import
    header.  Trying both exact fragments keeps import removal independent of
    the source-range proof below; the exact expected-output comparison selects
    the one actually used by the caller.
    """
    candidates: list[bytes] = []
    for injected in (
        f"\nimport {imported}\n".encode("utf-8"),
        f"import {imported}\n".encode("utf-8"),
    ):
        if source.count(injected) != 1:
            continue
        position = source.index(injected)
        candidate = source[:position] + source[position + len(injected) :]
        if candidate not in candidates:
            candidates.append(candidate)
    if not candidates:
        raise RuntimeError(
            "generated source does not contain one expected injected import: "
            f"{imported}"
        )
    return candidates


def _selected_ranges(
    original: bytes, entries: Iterable[dict[str, Any]], label: str
) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            raise RuntimeError(f"{label} entry[{index}] must be an object")
        start = _require_int(entry.get("startByte"), f"{label} entry[{index}].startByte")
        end = _require_int(entry.get("endByte"), f"{label} entry[{index}].endByte")
        if start < 0 or end <= start or end > len(original):
            raise RuntimeError(
                f"{label} entry[{index}] has invalid source range [{start},{end})"
            )
        result.append((start, end))
    # A whole outer replacement owns all of its contained source bytes. Check
    # every interval (not just adjacent roots) so crossing descendants cannot
    # disappear behind an otherwise valid outer range.
    roots: list[tuple[int, int]] = []
    stack: list[tuple[int, int]] = []
    for current in sorted(result, key=lambda value: (value[0], -value[1])):
        while stack and current[0] >= stack[-1][1]:
            stack.pop()
        if stack:
            parent = stack[-1]
            if current[0] == parent[0] or current[1] > parent[1]:
                raise RuntimeError(
                    f"{label} has duplicate-start or crossing selected ranges: "
                    f"{parent}, {current}"
                )
        else:
            roots.append(current)
        stack.append(current)
    return roots


def replacement_plan(
    original: bytes, entries: Iterable[dict[str, Any]], label: str
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    """Return disjoint outer replacements and nested-ID → outer-ID coverage.

    Covered syntax is consumed as part of the outer tactic's recording-only
    arguments. It gets no independent dispatcher or execution/variant claim.
    Mixed retained/executable containment is deliberately unsupported.
    """
    entries = list(entries)
    root_ranges = set(_selected_ranges(original, entries, label))
    ids: set[str] = set()
    roots: list[dict[str, Any]] = []
    covered: dict[str, str] = {}
    root: dict[str, Any] | None = None
    for entry in sorted(entries, key=lambda value: (value["startByte"], -value["endByte"])):
        occurrence = _require_nonempty_string(entry.get("id"), f"{label} occurrence ID")
        if occurrence in ids:
            raise RuntimeError(f"{label} has duplicate occurrence ID: {occurrence}")
        ids.add(occurrence)
        if (entry["startByte"], entry["endByte"]) in root_ranges:
            root = entry
            roots.append(entry)
        else:
            assert root is not None
            if entry.get("action") != root.get("action"):
                raise RuntimeError(f"{label} has mixed retained/executable containment")
            covered[occurrence] = str(root["id"])
    return roots, covered


def _assert_changes_within_ranges(
    original: bytes,
    generated_without_import: bytes,
    ranges: list[tuple[int, int]],
    label: str,
) -> None:
    """Independently prove diff operations touch only selected source ranges."""
    matcher = difflib.SequenceMatcher(
        None, original, generated_without_import, autojunk=False
    )
    for tag, original_start, original_end, _generated_start, _generated_end in matcher.get_opcodes():
        if tag == "equal":
            continue
        if original_start == original_end:
            permitted = any(start <= original_start <= end for start, end in ranges)
        else:
            permitted = any(
                start <= original_start and original_end <= end
                for start, end in ranges
            )
        if not permitted:
            raise RuntimeError(
                f"{label} changes authored bytes outside selected ranges: "
                f"{tag} at [{original_start},{original_end})"
            )


def _assert_exact_context_gaps(
    original: bytes, generated: bytes, ranges: list[tuple[int, int]],
    lengths: list[int], label: str,
) -> None:
    """Verify unchanged gaps in linear time using declared replacement lengths.

    Replacement lengths delimit generated regions, not permitted source ranges.
    Every byte outside the independently validated source ranges must match.
    This avoids ambiguous/quadratic diff alignment when originals also appear
    in provenance comments or the generated proofs contain repetitive terms.
    """
    if len(lengths) != len(ranges):
        raise RuntimeError(f"{label} replacement length count differs from root ranges")
    for length in lengths:
        _require_int(length, f"{label} replacement length", nonnegative=True)
    expected_size = len(original) + sum(lengths) - sum(end - start for start, end in ranges)
    if len(generated) != expected_size:
        raise RuntimeError(f"{label} generated size disagrees with replacement lengths")
    old_cursor = new_cursor = 0
    for (start, end), length in zip(ranges, lengths):
        gap = original[old_cursor:start]
        if generated[new_cursor:new_cursor + len(gap)] != gap:
            raise RuntimeError(f"{label} changes authored bytes outside selected ranges")
        new_cursor += len(gap) + length
        old_cursor = end
    if generated[new_cursor:] != original[old_cursor:]:
        raise RuntimeError(f"{label} changes authored bytes outside selected ranges")


def assert_exact_source_preservation(
    original: bytes,
    generated: bytes,
    entries: Iterable[dict[str, Any]],
    *,
    imported: str,
    label: str,
    expected_without_import: bytes,
    replacement_lengths: list[int] | None = None,
) -> None:
    """Prove that only the known transformation and import changed source.

    Explicit replacement lengths allow a linear check of every unchanged gap;
    callers without lengths use a diff check. Both independently confine edits
    to validated source ranges. The exact pre-import comparison also checks
    that the replacements themselves equal the recorded transformation.
    """
    ranges = _selected_ranges(original, entries, label)
    errors: list[str] = []
    for generated_without_import in _without_import_candidates(generated, imported):
        try:
            if replacement_lengths is None:
                _assert_changes_within_ranges(original, generated_without_import, ranges, label)
            else:
                _assert_exact_context_gaps(
                    original, generated_without_import, ranges, replacement_lengths, label
                )
            if generated_without_import != expected_without_import:
                raise RuntimeError(
                    f"{label} does not match its recorded transformation"
                )
        except RuntimeError as error:
            errors.append(str(error))
            continue
        return
    raise RuntimeError(
        f"{label} failed exact source preservation: " + "; ".join(errors)
    )


def selector_key(report: dict[str, object]) -> str:
    """Return all runtime selector values except closed-artifact provenance."""
    selector = report["selector"]
    if not isinstance(selector, dict):
        raise RuntimeError(f"artifact selector must be an object: {report!r}")
    # Callers validate the complete selector first.  The artifact is already
    # scoped to one occurrence/module, so those two provenance values need not
    # distinguish variants, but the selector schema is retained in the key.
    caller = selector["caller"]
    if caller is None:
        caller = ""
    return json.dumps(
        {
            "selectorSchema": selector["selectorSchema"],
            "preState": selector["preState"],
            "options": selector["options"],
            "caller": caller,
        },
        sort_keys=True,
        separators=(",", ":"),
    )


def artifact_payload(report: dict[str, object]) -> str:
    return json.dumps(
        {key: value for key, value in report.items() if key != "selector"},
        sort_keys=True,
        separators=(",", ":"),
    )


def group_report_variants(
    report_list: list[object],
    expected_ids: list[str],
    *,
    expected_module: str | None = None,
    unobserved_ids: set[str] | None = None,
) -> dict[str, list[dict[str, object]]]:
    unobserved_ids = set() if unobserved_ids is None else set(unobserved_ids)
    if not unobserved_ids.issubset(expected_ids):
        raise RuntimeError(
            f"unobserved occurrence IDs are not in the inventory: {sorted(unobserved_ids)}"
        )
    grouped: defaultdict[str, list[dict[str, object]]] = defaultdict(list)
    modules: dict[str, str] = {}
    for raw_report in report_list:
        if not isinstance(raw_report, dict) or not isinstance(
            raw_report.get("occurrence"), str
        ):
            raise RuntimeError(f"artifact report has no string occurrence: {raw_report!r}")
        occurrence = raw_report["occurrence"]
        if occurrence not in expected_ids:
            raise RuntimeError(f"artifact report has unknown occurrence: {raw_report!r}")
        selector = raw_report.get("selector")
        if isinstance(selector, dict) and isinstance(selector.get("module"), str):
            prior_module = modules.get(occurrence)
            if prior_module is not None and prior_module != selector["module"]:
                raise RuntimeError(
                    f"artifact occurrence has conflicting modules: {occurrence}"
                )
            modules[occurrence] = selector["module"]
        grouped[occurrence].append(
            validate_report(raw_report, occurrence, expected_module)
        )
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


def classify_occurrence(
    action: str, execution_count: int, variant_count: int, statuses: list[str]
) -> str:
    """Classify an independently recorded or retained occurrence."""
    _require_int(execution_count, "occurrence executionCount", nonnegative=True)
    _require_int(variant_count, "occurrence variantCount", nonnegative=True)
    if not isinstance(statuses, list):
        raise RuntimeError(f"occurrence variant statuses must be an array: {statuses!r}")
    if any(status not in {SUCCESS_STATUS, FAILURE_STATUS} for status in statuses):
        raise RuntimeError(f"occurrence variant has invalid status: {statuses!r}")
    if action == "retain":
        if execution_count != 0 or variant_count != 0 or statuses:
            raise RuntimeError(
                "retained occurrence must have zero executions and variants"
            )
        return "retained_syntax_data"
    if action != "materialize":
        raise RuntimeError(f"unsupported successful occurrence action: {action!r}")
    if execution_count == 0:
        if variant_count != 0 or statuses:
            raise RuntimeError(
                "unobserved occurrence must have zero variants and statuses"
            )
        return "unobserved_executable"
    if variant_count == 0 or variant_count > execution_count:
        raise RuntimeError(
            "observed occurrence must have at least one variant and no more "
            "variants than executions"
        )
    if len(statuses) != variant_count:
        raise RuntimeError(
            "occurrence variant statuses do not match variantCount: "
            f"{len(statuses)} != {variant_count}"
        )
    if all(status == FAILURE_STATUS for status in statuses):
        return "expected_failure"
    return "materialized"


def _variant_counts(statuses: list[str], label: str) -> tuple[int, int]:
    if not isinstance(statuses, list):
        raise RuntimeError(f"{label} must be an array: {statuses!r}")
    if any(status not in {SUCCESS_STATUS, FAILURE_STATUS} for status in statuses):
        raise RuntimeError(f"{label} contains an invalid status: {statuses!r}")
    return (
        sum(status == SUCCESS_STATUS for status in statuses),
        sum(status == FAILURE_STATUS for status in statuses),
    )


def validate_occurrence_result(
    value: object,
    expected_id: str,
    *,
    statuses: list[str] | None = None,
) -> dict[str, object]:
    fields = {
        "occurrence",
        "action",
        "classification",
        "executionCount",
        "variantCount",
        "successVariantCount",
        "failureVariantCount",
        "coveredBy",
    }
    if not isinstance(value, dict) or set(value) != fields:
        raise RuntimeError(f"invalid successful occurrence result: {value!r}")
    if value["occurrence"] != expected_id:
        raise RuntimeError(f"occurrence result ID mismatch: {value!r}")
    if (
        not isinstance(value["action"], str)
        or value["action"] not in {"materialize", "retain"}
    ):
        raise RuntimeError(f"invalid occurrence result action: {value!r}")
    if (
        not isinstance(value["classification"], str)
        or value["classification"] not in OCCURRENCE_CLASSIFICATIONS
    ):
        raise RuntimeError(f"invalid occurrence result classification: {value!r}")
    _require_int(value["executionCount"], "occurrence executionCount", nonnegative=True)
    _require_int(value["variantCount"], "occurrence variantCount", nonnegative=True)
    _require_int(
        value["successVariantCount"],
        "occurrence successVariantCount",
        nonnegative=True,
    )
    _require_int(
        value["failureVariantCount"],
        "occurrence failureVariantCount",
        nonnegative=True,
    )
    execution_count = value["executionCount"]
    variant_count = value["variantCount"]
    success_variant_count = value["successVariantCount"]
    failure_variant_count = value["failureVariantCount"]
    action = value["action"]
    classification = value["classification"]
    covered_by = value["coveredBy"]
    if classification == "covered_by_ancestor":
        _require_nonempty_string(covered_by, "covered occurrence ancestor")
        if (
            action != "materialize" or covered_by == expected_id
            or execution_count != 0 or variant_count != 0
        ):
            raise RuntimeError(f"covered occurrence has invalid result: {value!r}")
    elif covered_by is not None:
        raise RuntimeError(f"non-covered occurrence has an ancestor: {value!r}")
    if success_variant_count + failure_variant_count != variant_count:
        raise RuntimeError(
            f"occurrence variant status counts do not match variantCount: {value!r}"
        )
    if action == "retain":
        if (
            classification != "retained_syntax_data"
            or execution_count != 0
            or variant_count != 0
        ):
            raise RuntimeError(f"retained occurrence has invalid result: {value!r}")
    elif classification == "retained_syntax_data":
        raise RuntimeError(
            f"materialized occurrence has retained classification: {value!r}"
        )
    elif classification in {"unobserved_executable", "covered_by_ancestor"}:
        if execution_count != 0 or variant_count != 0:
            raise RuntimeError(f"unobserved occurrence has observations: {value!r}")
    elif classification in {"expected_failure", "materialized"}:
        if (
            execution_count == 0
            or variant_count == 0
            or variant_count > execution_count
        ):
            raise RuntimeError(f"observed occurrence has invalid counts: {value!r}")
        if classification == "expected_failure" and (
            success_variant_count != 0 or failure_variant_count == 0
        ):
            raise RuntimeError(
                f"expected-failure occurrence has a successful variant: {value!r}"
            )
        if classification == "materialized" and success_variant_count == 0:
            raise RuntimeError(
                f"materialized occurrence has no successful variant: {value!r}"
            )
    if statuses is not None:
        success_count, failure_count = _variant_counts(
            statuses, "occurrence variant statuses"
        )
        if (
            success_variant_count != success_count
            or failure_variant_count != failure_count
        ):
            raise RuntimeError(
                "occurrence variant status counts disagree with variant statuses: "
                f"{value!r}"
            )
        expected = (
            "covered_by_ancestor" if covered_by is not None
            else classify_occurrence(action, execution_count, variant_count, statuses)
        )
        if classification != expected:
            raise RuntimeError(
                "occurrence classification disagrees with observed variants: "
                f"expected {expected!r}, got {classification!r}"
            )
    return value


def make_occurrence_result(
    occurrence: str,
    action: str,
    execution_count: int,
    variants: list[dict[str, object]],
    *,
    covered_by: str | None = None,
) -> dict[str, object]:
    """Build and validate one successful per-occurrence summary record."""
    _require_nonempty_string(occurrence, "occurrence result occurrence")
    if not isinstance(variants, list):
        raise RuntimeError(f"occurrence variants must be an array: {variants!r}")
    statuses: list[str] = []
    for variant in variants:
        if not isinstance(variant, dict):
            raise RuntimeError(f"occurrence variant must be an object: {variant!r}")
        status = variant.get("status")
        if not isinstance(status, str):
            raise RuntimeError(
                f"occurrence variant status must be a string: {variant!r}"
            )
        statuses.append(status)
    variant_count = len(variants)
    classification = (
        "covered_by_ancestor" if covered_by is not None
        else classify_occurrence(action, execution_count, variant_count, statuses)
    )
    result = {
        "occurrence": occurrence,
        "action": action,
        "classification": classification,
        "coveredBy": covered_by,
        "executionCount": execution_count,
        "variantCount": variant_count,
        "successVariantCount": sum(
            variant.get("status") == SUCCESS_STATUS for variant in variants
        ),
        "failureVariantCount": sum(
            variant.get("status") == FAILURE_STATUS for variant in variants
        ),
    }
    return validate_occurrence_result(result, occurrence, statuses=statuses)


def occurrence_classification_counts(
    results: list[dict[str, object]],
) -> dict[str, int]:
    """Return a deterministic count map for validated results."""
    counts = {name: 0 for name in sorted(OCCURRENCE_CLASSIFICATIONS)}
    for result in results:
        classification = result.get("classification")
        if classification not in counts:
            raise RuntimeError(f"invalid occurrence result classification: {result!r}")
        counts[classification] += 1
    return counts


def validate_occurrence_summary(
    results: object,
    expected_ids: list[str],
    expected_actions: list[str],
    classification_counts: object,
) -> dict[str, int]:
    """Validate order, action partition, counts, and classification summary."""
    if not isinstance(results, list):
        raise RuntimeError(f"occurrenceResults must be an array: {results!r}")
    if len(expected_ids) != len(expected_actions):
        raise RuntimeError("occurrence summary expectations have different lengths")
    if len(expected_ids) != len(set(expected_ids)):
        raise RuntimeError(f"occurrence summary expectations contain duplicate IDs: {expected_ids!r}")
    if len(results) != len(expected_ids):
        raise RuntimeError(
            f"occurrenceResults length mismatch: {len(results)} != {len(expected_ids)}"
        )
    for index, (result, expected_id, expected_action) in enumerate(
        zip(results, expected_ids, expected_actions)
    ):
        checked = validate_occurrence_result(result, expected_id)
        if checked["action"] != expected_action:
            raise RuntimeError(
                f"occurrence result action mismatch at {index}: "
                f"{checked['action']!r} != {expected_action!r}"
            )
    by_id = {result["occurrence"]: result for result in results}
    for result in results:
        ancestor = result["coveredBy"]
        if ancestor is not None:
            root = by_id.get(ancestor)
            if root is None or root["action"] != "materialize" or root["coveredBy"] is not None:
                raise RuntimeError("covered occurrence must reference a replacement root")
    computed = occurrence_classification_counts(results)
    if not isinstance(classification_counts, dict):
        raise RuntimeError(
            "occurrenceClassificationCounts must be an object: "
            f"{classification_counts!r}"
        )
    if set(classification_counts) != set(computed):
        raise RuntimeError(
            "occurrenceClassificationCounts fields changed: "
            f"{sorted(classification_counts)} != {sorted(computed)}"
        )
    for classification, count in classification_counts.items():
        _require_int(
            count,
            f"occurrenceClassificationCounts.{classification}",
            nonnegative=True,
        )
    if classification_counts != computed:
        raise RuntimeError(
            "occurrenceClassificationCounts do not match occurrenceResults: "
            f"{classification_counts!r} != {computed!r}"
        )
    if sum(computed.values()) != len(expected_ids):
        raise RuntimeError(
            "occurrence classification counts do not sum to totalCount"
        )
    return computed
