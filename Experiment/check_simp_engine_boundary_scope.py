#!/usr/bin/env python3
"""Classify ``simp`` syntax by compiled declaration semantics and syntax ancestry."""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
import json
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
from collections.abc import Sequence

import simp_engine_inventory as inventory
from process_runner import run_process


ROOT = Path(__file__).resolve().parents[1]
OCCURRENCE_MARKER = "SIMP_ENGINE_SCOPE_OCCURRENCE "
DECLARATION_MARKER = "SIMP_ENGINE_SCOPE_DECLARATION "
FALLBACK_MARKER = "SIMP_ENGINE_SCOPE_FULL_FALLBACK module="
EXECUTION_MARKER = "SIMP_ENGINE_SCOPE_EXECUTION "
SCOPE_PROBE_IMPORT = "ExplicitLean.SimpEngine.Boundary.ScopeProbe"
SCOPE_PROBE_SCHEDULING = "set_option Elab.async false"
TO_DUAL_PROOF_COMMAND = "Mathlib.Tactic.ToDual.«commandTo_dual_insert_cast_:=_»"

# These are the only scope dimensions published in the schema-2 manifest.
# Keep the vocabulary here so the classifier, manifest builder, and consumers
# validate exactly the same closed set of values.
EXECUTION_ROLES = {
    "direct_executable",
    "reusable_executable",
    "retained_syntax_data",
    "unresolved",
}
DECLARATION_KINDS = {
    "proof",
    "computational",
    "generated_proof",
    "generated_computational",
    "signature_or_default",
    "caller_dependent",
    "not_applicable",
    "mixed",
    "unknown",
}
ACTIONS = {"materialize", "retain", "unresolved"}
DECLARATION_KINDS_BY_ROLE = {
    "direct_executable": {
        "proof",
        "computational",
        "generated_proof",
        "generated_computational",
        "signature_or_default",
        "mixed",
        "unknown",
    },
    "reusable_executable": {"caller_dependent"},
    "retained_syntax_data": {"not_applicable"},
    "unresolved": {"mixed", "unknown"},
}


def expected_action(execution_role: str, declaration_kind: str) -> str:
    """Return the fail-closed action implied by the two scope dimensions."""
    if execution_role == "retained_syntax_data" and declaration_kind == "not_applicable":
        return "retain"
    if execution_role == "reusable_executable" and declaration_kind == "caller_dependent":
        return "materialize"
    if execution_role == "direct_executable" and declaration_kind in {
        "proof",
        "computational",
        "generated_proof",
        "generated_computational",
        "signature_or_default",
    }:
        return "materialize"
    return "unresolved"


def validate_scope_dimensions(
    execution_role: object, declaration_kind: object, action: object
) -> tuple[str, str, str]:
    """Validate and cross-check one manifest scope triple."""
    if not isinstance(execution_role, str) or execution_role not in EXECUTION_ROLES:
        raise RuntimeError(f"invalid execution role: {execution_role!r}")
    if not isinstance(declaration_kind, str) or declaration_kind not in DECLARATION_KINDS:
        raise RuntimeError(f"invalid declaration kind: {declaration_kind!r}")
    if not isinstance(action, str) or action not in ACTIONS:
        raise RuntimeError(f"invalid scope action: {action!r}")
    if declaration_kind not in DECLARATION_KINDS_BY_ROLE[execution_role]:
        raise RuntimeError(
            "declaration kind is incompatible with execution role: "
            f"{execution_role}/{declaration_kind}"
        )
    expected = expected_action(execution_role, declaration_kind)
    if action != expected:
        raise RuntimeError(
            "scope dimensions imply a different action: "
            f"{execution_role}/{declaration_kind} -> {expected}, found {action}"
        )
    return execution_role, declaration_kind, action


@dataclass(frozen=True)
class ModuleSpec:
    module: str
    source: Path
    expected_occurrences: int
    fixture: bool = False


SPECS = (
    ModuleSpec(
        "ExplicitLean.SimpEngine.Boundary.ScopeFixture",
        ROOT / "ExplicitLean/SimpEngine/Boundary/ScopeFixture.lean",
        13,
        fixture=True,
    ),
    ModuleSpec(
        "Mathlib.CategoryTheory.EqToHom",
        ROOT / ".lake/packages/mathlib/Mathlib/CategoryTheory/EqToHom.lean",
        33,
    ),
    ModuleSpec(
        "Mathlib.Data.Fintype.List",
        ROOT / ".lake/packages/mathlib/Mathlib/Data/Fintype/List.lean",
        6,
    ),
    ModuleSpec(
        "Mathlib.Algebra.Algebra.NonUnitalHom",
        ROOT / ".lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean",
        7,
    ),
    ModuleSpec(
        "Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart",
        ROOT
        / ".lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/SpecialFunctions/PosPart.lean",
        3,
    ),
)


def run(command: list[str], timeout: int = 600) -> str:
    result = run_process(
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


def load_records_with_fallbacks(
    specs: Sequence[ModuleSpec] | None = None,
    *,
    batch_size: int = 128,
    timeout: int = 600,
) -> tuple[
    dict[str, list[dict[str, object]]],
    dict[str, list[dict[str, object]]],
    list[str],
]:
    """Load scope records for ``specs`` in bounded Lean invocations.

    The no-argument form intentionally retains the original representative
    checker behavior.  Corpus callers pass an explicit sequence so a single
    large command line is never constructed.  A module belongs to exactly
    one batch; seeing records for a module more than once is rejected instead
    of silently merging duplicate observations. The timeout applies separately
    to the prerequisite build and each batch.
    """
    if batch_size <= 0:
        raise ValueError("scope batch size must be positive")
    selected = tuple(SPECS if specs is None else specs)
    if not selected:
        raise ValueError("scope classifier requires at least one module")
    run(
        [
            "lake",
            "build",
            "ExplicitLean",
            "ExplicitLean.SimpEngine.Boundary.ScopeFixture",
            "ExplicitLean.SimpEngine.Boundary.ScopeProbe",
        ],
        timeout=timeout,
    )
    occurrences: defaultdict[str, list[dict[str, object]]] = defaultdict(list)
    declarations: defaultdict[str, list[dict[str, object]]] = defaultdict(list)
    fallback_modules: set[str] = set()
    requested_modules: set[str] = set()
    for start in range(0, len(selected), batch_size):
        batch = selected[start : start + batch_size]
        batch_modules: set[str] = set()
        command = [
            sys.executable,
            str(ROOT / "Experiment" / "lean_toolchain_cache.py"),
            "scope",
        ]
        for spec in batch:
            if not isinstance(spec.module, str) or not spec.module:
                raise ValueError(f"scope module name must be nonempty: {spec!r}")
            if not spec.source.is_file():
                raise RuntimeError(f"scope source does not exist: {spec.source}")
            if spec.module in requested_modules or spec.module in batch_modules:
                raise RuntimeError(f"duplicate scope module specification: {spec.module}")
            batch_modules.add(spec.module)
            command.extend([spec.module, str(spec.source)])
        requested_modules.update(batch_modules)
        output = run(command, timeout=timeout)
        batch_occurrences: defaultdict[str, list[dict[str, object]]] = defaultdict(list)
        batch_declarations: defaultdict[str, list[dict[str, object]]] = defaultdict(list)
        batch_fallbacks: set[str] = set()
        for line in output.splitlines():
            if OCCURRENCE_MARKER in line:
                value = json.loads(line.split(OCCURRENCE_MARKER, 1)[1])
                batch_occurrences[str(value["module"])].append(value)
            elif DECLARATION_MARKER in line:
                value = json.loads(line.split(DECLARATION_MARKER, 1)[1])
                batch_declarations[str(value["module"])].append(value)
            elif FALLBACK_MARKER in line:
                detail = line.split(FALLBACK_MARKER, 1)[1]
                module, separator, _path = detail.partition(" file=")
                if not separator or not module:
                    raise RuntimeError(f"invalid scope fallback marker: {line}")
                batch_fallbacks.add(module)
        returned_modules = set(batch_occurrences) | set(batch_declarations)
        unexpected = returned_modules - batch_modules
        if unexpected:
            raise RuntimeError(
                "scope classifier returned unrequested modules: "
                f"{sorted(unexpected)}"
            )
        unexpected_fallbacks = batch_fallbacks - batch_modules
        if unexpected_fallbacks:
            raise RuntimeError(
                "scope classifier reported fallbacks for unrequested modules: "
                f"{sorted(unexpected_fallbacks)}"
            )
        duplicate_modules = returned_modules & (
            set(occurrences) | set(declarations)
        )
        if duplicate_modules:
            raise RuntimeError(
                "scope classifier returned duplicate module data: "
                f"{sorted(duplicate_modules)}"
            )
        for module, values in batch_occurrences.items():
            occurrences[module].extend(values)
        for module, values in batch_declarations.items():
            declarations[module].extend(values)
        fallback_modules.update(batch_fallbacks)
    return dict(occurrences), dict(declarations), sorted(fallback_modules)


def load_records(
    specs: Sequence[ModuleSpec] | None = None,
    *,
    batch_size: int = 128,
    timeout: int = 600,
) -> tuple[dict[str, list[dict[str, object]]], dict[str, list[dict[str, object]]]]:
    """Load scope records while preserving the original two-result API."""
    occurrences, declarations, _fallbacks = load_records_with_fallbacks(
        specs, batch_size=batch_size, timeout=timeout
    )
    return occurrences, declarations


def containing_declarations(
    occurrence: dict[str, object], declarations: list[dict[str, object]]
) -> list[dict[str, object]]:
    start = int(occurrence["startByte"])
    end = int(occurrence["endByte"])
    containing = [
        declaration
        for declaration in declarations
        if int(declaration["startByte"]) <= start
        and end <= int(declaration["endByte"])
    ]
    if not containing:
        return []
    smallest_span = min(
        int(declaration["endByte"]) - int(declaration["startByte"])
        for declaration in containing
    )
    return sorted(
        (
            declaration
            for declaration in containing
            if int(declaration["endByte"]) - int(declaration["startByte"])
            == smallest_span
        ),
        key=lambda declaration: str(declaration["name"]),
    )


def _is_antiquotation_kind(kind: str) -> bool:
    """Return whether a syntax ancestry entry enters an antiquotation.

    The parser uses both a namespaced ``term.pseudo.antiquot`` node and the
    unnamespaced ``antiquotNestedExpr`` node for the expression that fills a
    quotation hole.  Keep this test centralized so classification and
    execution-evidence joining use the same boundary rules.
    """
    lowered = kind.lower()
    return "antiquot" in lowered


def _quotation_context(ancestors: list[str]) -> str:
    """Classify the innermost quotation boundary containing an occurrence.

    A quotation node makes descendants syntax data until an antiquotation
    opens an ordinary term expression.  Nested quotations and antiquotations
    are handled by comparing their innermost boundary positions.  ``unknown``
    is deliberately conservative when an antiquotation marker appears
    without a quotation marker; callers must then obtain execution evidence.
    """
    quotation_positions = [
        index for index, kind in enumerate(ancestors) if kind.endswith(".quot")
    ]
    antiquotation_positions = [
        index for index, kind in enumerate(ancestors) if _is_antiquotation_kind(kind)
    ]
    if not quotation_positions:
        return "unknown" if antiquotation_positions else "none"
    quotation_position = max(quotation_positions)
    antiquotation_position = max(antiquotation_positions, default=-1)
    if antiquotation_position > quotation_position:
        return "antiquotation"
    return "quotation"


def classify(
    occurrence: dict[str, object], declarations: list[dict[str, object]]
) -> dict[str, object]:
    """Classify one occurrence along independent execution/scope axes.

    The old classifier collapsed proof-vs-data and executable-vs-retained into
    one proof-only label.  That made computational calls look out of scope.
    This classifier keeps those decisions independent and derives the action
    only after both dimensions are known.  Quoted syntax is deliberately
    fail-closed unless a temporary execution probe resolves it.
    """
    ancestors = occurrence.get("ancestors")
    if not isinstance(ancestors, list) or not all(
        isinstance(kind, str) for kind in ancestors
    ):
        raise RuntimeError(f"scope occurrence has invalid ancestry: {occurrence!r}")
    command_kind = occurrence.get("commandKind")
    quotation_context = _quotation_context(ancestors)
    quoted = quotation_context == "quotation"
    reusable = quoted and any(
        kind
        in {
            "Lean.Parser.Command.macro",
            "Lean.Parser.Command.macro_rules",
            "Lean.Parser.Command.elab",
            "Lean.Parser.Command.elab_rules",
        }
        for kind in ancestors
    )
    candidates = containing_declarations(occurrence, declarations)

    # #check consumes a quotation as Syntax data.  An antiquotation is an
    # ordinary term expression nested in that quotation and therefore executes
    # while the #check term is elaborated; it must reach the evidence path.
    if quoted and command_kind == "Lean.Parser.Command.check":
        execution_role = "retained_syntax_data"
        declaration_kind = "not_applicable"
        reason = "#check retains the tactic quotation as Syntax data"
    # A quotation in a macro/elaborator is reusable executable syntax.  It is
    # not tied to the declaration in which a caller eventually expands it.
    elif reusable:
        execution_role = "reusable_executable"
        declaration_kind = "caller_dependent"
        reason = "tactic quotation belongs to a reusable macro/elaborator command"
    # This generated theorem command is known statically to materialize a
    # proof-valued declaration.
    elif TO_DUAL_PROOF_COMMAND in ancestors:
        execution_role = "direct_executable"
        declaration_kind = "generated_proof"
        reason = (
            "to_dual_insert_cast elaborates its command RHS as the proof value "
            "of a generated theorem"
        )
    # Any other quotation might execute (for example inside run_cmd) or might
    # remain syntax data.  This check precedes command/declaration rules because
    # a quoted tactic in an irreducible RHS or default can still be retained as
    # a Syntax value rather than executed.
    elif quoted:
        execution_role = "unresolved"
        declaration_kind = "unknown"
        reason = "quoted occurrence requires execution evidence"
    # Irreducible definitions generate an implementation command whose body is
    # computational even when the body contains proof fields.
    elif any(
        kind == "Lean.Elab.Command.command_Irreducible_def____"
        for kind in ancestors
    ):
        execution_role = "direct_executable"
        declaration_kind = "computational"
        reason = (
            "tactic is in the RHS of an irreducible computational definition"
        )
    elif command_kind == "Lean.Parser.Command.variable":
        execution_role = "direct_executable"
        declaration_kind = "signature_or_default"
        reason = "tactic occurs in a declaration signature/default value, not a proof body"

    elif candidates and all(bool(candidate["isProof"]) for candidate in candidates):
        execution_role = "direct_executable"
        declaration_kind = "proof"
        reason = "smallest enclosing compiled declarations are all proof-valued"
    elif candidates and all(not bool(candidate["isProof"]) for candidate in candidates):
        execution_role = "direct_executable"
        declaration_kind = "computational"
        reason = "smallest enclosing compiled declarations are all non-proof-valued"
    elif candidates:
        execution_role = "direct_executable"
        declaration_kind = "mixed"
        reason = "smallest enclosing declarations disagree on proof-valued status"
    else:
        execution_role = "direct_executable"
        declaration_kind = "unknown"
        reason = "no conservative declaration rule applies; execution evidence may resolve it"

    action = expected_action(execution_role, declaration_kind)

    return {
        "executionRole": execution_role,
        "declarationKind": declaration_kind,
        "action": action,
        "reason": reason,
        "occurrence": occurrence,
        "declarations": candidates,
    }


def _occurrence_key(entry: dict[str, object]) -> tuple[int, int, str, str]:
    return (
        int(entry["startByte"]),
        int(entry["endByte"]),
        str(entry["kind"]),
        str(entry["source"]),
    )


def _strip_lean_comments(line: bytes, block_depth: int) -> tuple[bytes, int]:
    """Remove Lean comments from one header line for command detection.

    Mathlib headers use nested block comments for copyright and module
    documentation.  Header imports themselves are one-line commands, so a
    small comment lexer is sufficient and avoids making source classification
    depend on a second parser.
    """
    output = bytearray()
    cursor = 0
    while cursor < len(line):
        if block_depth:
            if line[cursor : cursor + 2] == b"/-":
                block_depth += 1
                cursor += 2
            elif line[cursor : cursor + 2] == b"-/":
                block_depth -= 1
                cursor += 2
            else:
                cursor += 1
        elif line[cursor : cursor + 2] == b"--":
            break
        elif line[cursor : cursor + 2] == b"/-":
            block_depth = 1
            cursor += 2
        else:
            output.append(line[cursor])
            cursor += 1
    return bytes(output), block_depth


def _header_offsets(source: bytes) -> tuple[int, int]:
    """Return insertion offsets after imports and before the first command."""
    offset = 0
    module_seen = False
    block_depth = 0
    import_offset = 0
    for line in source.splitlines(keepends=True):
        code, block_depth = _strip_lean_comments(line, block_depth)
        stripped = code.strip()
        if not module_seen:
            if stripped == b"module":
                module_seen = True
            offset += len(line)
            continue
        if not stripped:
            offset += len(line)
            continue
        tokens = stripped.split()
        if tokens == [b"prelude"]:
            import_offset = offset + len(line)
            offset += len(line)
            continue
        modifier_index = 0
        while modifier_index < len(tokens) and tokens[modifier_index] in {
            b"public",
            b"meta",
        }:
            modifier_index += 1
        if modifier_index < len(tokens) and tokens[modifier_index] == b"import":
            import_offset = offset + len(line)
            offset += len(line)
            continue
        return import_offset, offset
    if not module_seen:
        raise RuntimeError("Lean source has no `module` header")
    return import_offset, offset


def _inject_scope_probe_header(source: bytes) -> bytes:
    """Inject the standalone probe and deterministic scheduling option.

    Both commands are inserted after all original header imports (and module
    documentation comments), before the first declaration.  This keeps the
    option global for the temporary copy while avoiding any source command
    scope changes in the original module.
    """
    if b"Elab.async" in source:
        raise RuntimeError(
            "scope probe source already mentions Elab.async; refusing to override it"
        )
    import_offset, body_offset = _header_offsets(source)
    import_text = f"import {SCOPE_PROBE_IMPORT}\n".encode("utf-8")
    source = source[:import_offset] + import_text + source[import_offset:]
    if body_offset >= import_offset:
        body_offset += len(import_text)
    option_text = f"{SCOPE_PROBE_SCHEDULING}\n\n".encode("utf-8")
    return source[:body_offset] + option_text + source[body_offset:]


def _apply_scope_edits(
    source: bytes, edits: Sequence[tuple[int, int, bytes, str]]
) -> bytes:
    ordered = sorted(edits, key=lambda edit: (edit[0], edit[1]))
    previous_end = -1
    for start, end, _replacement, label in ordered:
        if start < 0 or end < start or end > len(source):
            raise RuntimeError(f"invalid {label} source edit: {start}:{end}")
        if start < previous_end:
            raise RuntimeError(f"overlapping scope probe source edits at {label}")
        previous_end = end
    for start, end, replacement, _label in reversed(ordered):
        source = source[:start] + replacement + source[end:]
    return source


def _simp_probe_edits(
    source: bytes, entries: Sequence[dict[str, object]]
) -> list[tuple[int, int, bytes, str]]:
    edits: list[tuple[int, int, bytes, str]] = []
    starts: set[int] = set()
    for entry in entries:
        inventory.validate_occurrence(source, dict(entry))
        start = int(entry["startByte"])
        if start in starts:
            raise RuntimeError(
                f"duplicate scope probe instrumentation start: {entry!r}"
            )
        starts.add(start)
        suffix_start = start + 4
        head_antiquotation = b""
        if source[suffix_start : suffix_start + 2] == b"%$":
            cursor = suffix_start + 2
            occurrence_end = int(entry["endByte"])
            delimiters = b" \t\r\n[](){},;"
            while cursor < occurrence_end and source[cursor] not in delimiters:
                cursor += 1
            if cursor == suffix_start + 2:
                raise RuntimeError(
                    f"empty tactic-head antiquotation: {entry!r}"
                )
            head_antiquotation = source[suffix_start:cursor]
            suffix_start = cursor
        replacement = (
            f'simp_engine_boundary_scope_probe "{entry["id"]}"'.encode("utf-8")
        )
        insertion = next(
            (index for index, byte in enumerate(replacement) if byte in b" \t\r\n"),
            len(replacement),
        )
        replacement = (
            replacement[:insertion]
            + head_antiquotation
            + replacement[insertion:]
        )
        edits.append((start, suffix_start, replacement, "simp head"))
    return edits


def _example_probe_edits(
    module: str,
    source: bytes,
    occurrences: Sequence[dict[str, object]],
) -> list[tuple[int, int, bytes, str]]:
    command_ranges: dict[tuple[int, int], str] = {}
    for occurrence in occurrences:
        if occurrence.get("commandKind") != "Lean.Parser.Command.example":
            continue
        command_start = occurrence.get("commandStartByte")
        command_end = occurrence.get("commandEndByte")
        if not isinstance(command_start, int) or not isinstance(command_end, int):
            raise RuntimeError(
                f"example occurrence has no source-backed command range: {occurrence!r}"
            )
        if source[command_start : command_start + len(b"example")] != b"example":
            raise RuntimeError(
                f"example command does not start with `example`: {occurrence!r}"
            )
        key = (command_start, command_end)
        prior = command_ranges.get(key)
        if prior is None:
            command_bytes = source[command_start:command_end]
            digest = hashlib.sha256(
                f"{module}:{command_start}:{command_end}:".encode("utf-8")
                + command_bytes
            ).hexdigest()[:16]
            prior = f"private def simpEngineScopeExample_{digest}"
            command_ranges[key] = prior
    return [
        (start, start + len(b"example"), replacement.encode("utf-8"), "example command")
        for (start, _end), replacement in sorted(command_ranges.items())
    ]


def _module_relative_path(module: str) -> Path:
    if not (module.startswith("Mathlib.") or module.startswith("ExplicitLean.")):
        raise RuntimeError(f"scope probe cannot derive a source path for {module!r}")
    return Path(*module.split(".")).with_suffix(".lean")


def _parse_execution_reports(output: str) -> list[dict[str, object]]:
    reports: list[dict[str, object]] = []
    for line in output.splitlines():
        if not line.startswith(EXECUTION_MARKER):
            continue
        try:
            value = json.loads(line[len(EXECUTION_MARKER) :])
        except json.JSONDecodeError as error:
            raise RuntimeError(f"invalid scope execution marker: {line}") from error
        if not isinstance(value, dict):
            raise RuntimeError(f"scope execution marker is not an object: {value!r}")
        reports.append(value)
    return reports


def _bool_or_none(value: object) -> bool | None:
    if value is None:
        return None
    if not isinstance(value, bool):
        raise RuntimeError(f"scope execution evidence has non-boolean proof flag: {value!r}")
    return value


def _execution_evidence(
    expected_ids: set[str], reports: Sequence[dict[str, object]], module: str
) -> dict[str, dict[str, object]]:
    seen: set[tuple[str, str | None]] = set()
    grouped: defaultdict[str, list[dict[str, object]]] = defaultdict(list)
    modules: dict[str, str] = {}
    for report in reports:
        required = {
            "occurrenceId",
            "module",
            "caller",
            "executionCount",
            "isProofDeclaration",
            "evidenceStatus",
        }
        if set(report) != required:
            raise RuntimeError(
                f"scope execution evidence fields changed for {module}: {report!r}"
            )
        occurrence_id = report["occurrenceId"]
        report_module = report["module"]
        caller = report["caller"]
        execution_count = report["executionCount"]
        status = report["evidenceStatus"]
        if not isinstance(occurrence_id, str) or not occurrence_id:
            raise RuntimeError(f"scope execution evidence has invalid occurrence ID: {report!r}")
        if occurrence_id not in expected_ids:
            raise RuntimeError(
                f"scope execution evidence returned an unrequested ID: {occurrence_id}"
            )
        if not isinstance(report_module, str) or not report_module:
            raise RuntimeError(f"scope execution evidence has invalid module: {report!r}")
        if report_module != module:
            raise RuntimeError(
                "scope execution evidence returned the wrong module: "
                f"expected {module!r}, found {report_module!r}"
            )
        if caller is not None and (
            not isinstance(caller, str) or not caller.strip()
        ):
            raise RuntimeError(f"scope execution evidence has invalid caller: {report!r}")
        if (
            not isinstance(execution_count, int)
            or isinstance(execution_count, bool)
            or execution_count <= 0
        ):
            raise RuntimeError(f"scope execution evidence has invalid count: {report!r}")
        if not isinstance(status, str) or not status:
            raise RuntimeError(f"scope execution evidence has invalid status: {report!r}")
        proof = _bool_or_none(report["isProofDeclaration"])
        key = (occurrence_id, caller)
        if key in seen:
            raise RuntimeError(
                f"duplicate scope execution evidence for {occurrence_id}:{caller}"
            )
        seen.add(key)
        prior_module = modules.get(occurrence_id)
        if prior_module is not None and prior_module != report_module:
            raise RuntimeError(
                f"conflicting scope execution modules for {occurrence_id}: "
                f"{prior_module!r} versus {report_module!r}"
            )
        modules[occurrence_id] = report_module
        grouped[occurrence_id].append(
            {
                "caller": caller,
                "executionCount": execution_count,
                "isProofDeclaration": proof,
                "evidenceStatus": status,
            }
        )

    result: dict[str, dict[str, object]] = {}
    for occurrence_id in sorted(expected_ids):
        observations = grouped.get(occurrence_id, [])
        if not observations:
            result[occurrence_id] = {
                "status": "missing_execution",
                "executionCount": 0,
                "callers": [],
                "module": None,
                "scheduling": SCOPE_PROBE_SCHEDULING,
            }
            continue
        observations = sorted(
            observations,
            key=lambda item: str(item["caller"])
            if item["caller"] is not None
            else "",
        )
        complete = all(
            item["evidenceStatus"] == "complete"
            and item["caller"] is not None
            and item["isProofDeclaration"] is not None
            for item in observations
        )
        proof_values = {
            bool(item["isProofDeclaration"])
            for item in observations
            if item["isProofDeclaration"] is not None
        }
        if complete and proof_values == {True}:
            status = "complete_proof_declaration"
        elif complete and proof_values == {False}:
            status = "complete_nonproof_declaration"
        elif complete and len(proof_values) > 1:
            status = "mixed_execution_classification"
        else:
            status = "incomplete_execution_evidence"
        result[occurrence_id] = {
            "status": status,
            "executionCount": sum(
                int(item["executionCount"]) for item in observations
            ),
            "callers": [
                {
                    "caller": item["caller"],
                    "executionCount": item["executionCount"],
                    "isProofDeclaration": item["isProofDeclaration"],
                }
                for item in observations
            ],
            "module": modules.get(occurrence_id),
            "scheduling": SCOPE_PROBE_SCHEDULING,
        }
    return result


def _result_occurrence(result: dict[str, object]) -> dict[str, object]:
    """Return the source occurrence from either classifier result shape.

    The representative scope checker retains the raw occurrence under an
    ``occurrence`` field.  The corpus manifest flattens the same fields into its
    occurrence record before execution evidence is added.  Both forms must use
    the identical evidence path.
    """
    nested = result.get("occurrence")
    if isinstance(nested, dict):
        return nested
    required = {"startByte", "endByte", "kind", "source"}
    if required <= set(result):
        return result
    raise RuntimeError(f"unresolved scope result has no occurrence: {result!r}")


def resolve_execution_evidence(
    module: str,
    source: bytes,
    entries: Sequence[dict[str, object]],
    occurrences: Sequence[dict[str, object]],
    *,
    timeout: int = 600,
) -> dict[str, dict[str, object]]:
    """Compile one temporary source copy and join its carried probe IDs.

    ``entries`` and ``occurrences`` are intentionally restricted to the
    statically unresolved calls.  The source copy is disposable: anonymous
    examples are renamed only so their final declaration types can be resolved
    by the report command, and no renamed source is ever materialized.
    """
    if not entries:
        return {}
    expected_ids = {str(entry["id"]) for entry in entries}
    if len(expected_ids) != len(entries):
        raise RuntimeError(f"duplicate scope execution entry IDs for {module}")
    entries_by_key = {_occurrence_key(entry): entry for entry in entries}
    if len(entries_by_key) != len(entries):
        raise RuntimeError(f"duplicate scope execution source ranges for {module}")
    selected_occurrences: list[dict[str, object]] = []
    selected_ids: set[str] = set()
    for occurrence in occurrences:
        entry = entries_by_key.get(_occurrence_key(occurrence))
        if entry is None:
            raise RuntimeError(
                f"scope execution occurrence is not one of the selected entries: {occurrence!r}"
            )
        occurrence_id = str(entry["id"])
        if occurrence_id in selected_ids:
            raise RuntimeError(
                f"duplicate scope execution occurrence for {module}:{occurrence_id}"
            )
        selected_ids.add(occurrence_id)
        selected_occurrences.append(occurrence)
    if selected_ids != expected_ids:
        raise RuntimeError(
            f"scope execution selection mismatch for {module}: "
            f"missing={sorted(expected_ids - selected_ids)}, "
            f"extra={sorted(selected_ids - expected_ids)}"
        )

    edits = _simp_probe_edits(source, entries)
    edits.extend(_example_probe_edits(module, source, selected_occurrences))
    rewritten = _apply_scope_edits(source, edits)
    rewritten = _inject_scope_probe_header(rewritten)
    if not rewritten.endswith(b"\n"):
        rewritten += b"\n"
    rewritten += b"\nsimp_engine_boundary_scope_report\n"

    with tempfile.TemporaryDirectory(
        prefix="boundary-scope-probe-", dir=ROOT / ".lake"
    ) as raw_directory:
        work = Path(raw_directory)
        destination = work / _module_relative_path(module)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(rewritten)
        command = inventory.lean_command(destination)
        if not module.startswith("Mathlib."):
            # `lean_command` already adds -R for Mathlib copies.  Add the
            # equivalent source root for fixtures so the report sees the
            # original compiled module name rather than a temporary basename.
            command[-1:] = ["-R", str(work), str(destination)]
        code, output, _elapsed = inventory.run(command, timeout=timeout)
        if code != 0:
            raise RuntimeError(
                f"scope execution probe failed for {module}:\n{output}"
            )
    reports = _parse_execution_reports(output)
    return _execution_evidence(expected_ids, reports, module)


def apply_execution_evidence(
    module: str,
    source: bytes,
    results: list[dict[str, object]],
    *,
    entries: Sequence[dict[str, object]] | None = None,
    timeout: int = 600,
) -> dict[str, dict[str, object]]:
    """Resolve action-unresolved results and mutate them with audit evidence.

    Quoted occurrences are classified as generated declarations when the probe
    observes a complete caller.  Nonquoted occurrences retain their known
    direct-executable role and use the observed caller only to fill in a
    missing proof/computational declaration kind.  Mixed or incomplete
    evidence remains unresolved.
    """
    unknown = [
        result
        for result in results
        if result.get("action") == "unresolved"
    ]
    if not unknown:
        return {}
    selected_entries: list[dict[str, object]] = []
    occurrences = []
    provided_by_key = (
        {_occurrence_key(entry): entry for entry in entries}
        if entries is not None
        else None
    )
    if provided_by_key is not None and len(provided_by_key) != len(entries):
        raise RuntimeError(f"duplicate execution entries for {module}")
    result_ids: dict[int, str] = {}
    for result in unknown:
        occurrence = _result_occurrence(result)
        if provided_by_key is None:
            occurrence_id = inventory.occurrence_id(
                module,
                int(occurrence["startByte"]),
                int(occurrence["endByte"]),
            )
            entry = dict(occurrence)
            entry["id"] = occurrence_id
            entry["module"] = module
        else:
            entry = provided_by_key.get(_occurrence_key(occurrence))
            if entry is None:
                raise RuntimeError(
                    f"execution entry does not match an unresolved result in {module}: "
                    f"{occurrence!r}"
                )
            occurrence_id = str(entry["id"])
        selected_entries.append(dict(entry))
        occurrences.append(occurrence)
        result_ids[id(result)] = occurrence_id
    if provided_by_key is not None:
        selected_ids = {str(entry["id"]) for entry in selected_entries}
        provided_ids = {str(entry["id"]) for entry in entries}
        if selected_ids != provided_ids:
            raise RuntimeError(
                f"execution entry selection mismatch for {module}: "
                f"missing={sorted(provided_ids - selected_ids)}, "
                f"extra={sorted(selected_ids - provided_ids)}"
            )
    evidence = resolve_execution_evidence(
        module, source, selected_entries, occurrences, timeout=timeout
    )
    for result in unknown:
        occurrence_id = result_ids[id(result)]
        observed = evidence[occurrence_id]
        result["executionEvidence"] = observed
        status = observed["status"]
        occurrence = _result_occurrence(result)
        ancestors = occurrence.get("ancestors")
        quoted = isinstance(ancestors, list) and all(
            isinstance(kind, str) for kind in ancestors
        ) and _quotation_context(ancestors) == "quotation"
        declarations = result.get("declarations")
        generated = quoted and isinstance(declarations, list) and not declarations
        if status == "complete_proof_declaration":
            result["executionRole"] = "direct_executable"
            result["declarationKind"] = (
                "generated_proof" if generated else "proof"
            )
            result["action"] = "materialize"
            result["reason"] = (
                "temporary source instrumentation observed executions whose "
                "final caller declarations are all proof-valued"
            )
        elif status == "complete_nonproof_declaration":
            result["executionRole"] = "direct_executable"
            result["declarationKind"] = (
                "generated_computational" if generated else "computational"
            )
            result["action"] = "materialize"
            result["reason"] = (
                "temporary source instrumentation observed executions whose "
                "final caller declarations are all non-proof-valued"
            )
        elif status == "mixed_execution_classification":
            result["executionRole"] = "unresolved" if quoted else "direct_executable"
            result["declarationKind"] = "mixed"
            result["action"] = "unresolved"
            result["reason"] = (
                "executions resolved to both proof and non-proof declarations; "
                "scope action fails closed"
            )
        elif status == "missing_execution":
            result["executionRole"] = "unresolved" if quoted else "direct_executable"
            result["declarationKind"] = "unknown"
            result["action"] = "unresolved"
            result["reason"] = (
                "selected source occurrence did not execute in the temporary "
                "probe copy; scope action fails closed"
            )
        else:
            result["executionRole"] = "unresolved" if quoted else "direct_executable"
            result["declarationKind"] = "unknown"
            result["action"] = "unresolved"
            result["reason"] = (
                "temporary execution evidence was incomplete; scope action "
                "fails closed"
            )
        validate_scope_dimensions(
            result.get("executionRole"),
            result.get("declarationKind"),
            result.get("action"),
        )
    return evidence


def assert_fixture(results: list[dict[str, object]]) -> None:
    role_counts = Counter(str(result["executionRole"]) for result in results)
    expected_roles = {
        "direct_executable": 11,
        "reusable_executable": 1,
        "retained_syntax_data": 1,
    }
    if dict(role_counts) != expected_roles:
        raise RuntimeError(f"scope fixture execution-role mismatch: {role_counts}\n{results}")
    kind_counts = Counter(str(result["declarationKind"]) for result in results)
    expected_kinds = {
        "proof": 3,
        "computational": 5,
        "generated_proof": 1,
        "generated_computational": 1,
        "signature_or_default": 1,
        "caller_dependent": 1,
        "not_applicable": 1,
    }
    if dict(kind_counts) != expected_kinds:
        raise RuntimeError(
            f"scope fixture declaration-kind mismatch: {kind_counts}\n{results}"
        )
    action_counts = Counter(str(result["action"]) for result in results)
    expected_actions = {"materialize": 12, "retain": 1}
    if dict(action_counts) != expected_actions:
        raise RuntimeError(f"scope fixture action mismatch: {action_counts}\n{results}")
    for result in results:
        validate_scope_dimensions(
            result.get("executionRole"),
            result.get("declarationKind"),
            result.get("action"),
        )

    prop_data = [
        result
        for result in results
        if any(
            str(declaration["name"]).endswith(".scopePropData")
            for declaration in result["declarations"]
        )
    ]
    if len(prop_data) != 1 or prop_data[0]["declarationKind"] != (
        "computational"
    ) or any(bool(declaration["isProof"]) for declaration in prop_data[0]["declarations"]):
        raise RuntimeError(
            "`def scopePropData : Prop` was not classified as proposition data"
        )

    execution_results = [
        result for result in results if "executionEvidence" in result
    ]
    if len(execution_results) != 4:
        raise RuntimeError(
            "scope fixture expected four execution-evidence occurrences, found "
            f"{len(execution_results)}"
        )
    if any(
        result["executionEvidence"]["status"]
        not in {"complete_proof_declaration", "complete_nonproof_declaration"}
        for result in execution_results
    ):
        raise RuntimeError(
            f"scope fixture has incomplete execution evidence: {execution_results}"
        )
    evidence_counts = Counter(
        result["executionEvidence"]["status"] for result in execution_results
    )
    if evidence_counts != Counter(
        {
            "complete_proof_declaration": 2,
            "complete_nonproof_declaration": 2,
        }
    ):
        raise RuntimeError(
            f"scope fixture execution-evidence mismatch: {evidence_counts}"
        )
    named_proof = [
        result
        for result in execution_results
        if "scopeGeneratedFromRunCmd" in str(result["executionEvidence"])
    ]
    named_data = [
        result
        for result in execution_results
        if "scopeGeneratedDataFromRunCmd" in str(result["executionEvidence"])
    ]
    if (
        len(named_proof) != 1
        or named_proof[0]["executionEvidence"]["status"]
        != "complete_proof_declaration"
        or len(named_data) != 1
        or named_data[0]["executionEvidence"]["status"]
        != "complete_nonproof_declaration"
    ):
        raise RuntimeError(
            "scope fixture did not resolve named generated proof/nonproof callers"
        )


def main() -> None:
    occurrences_by_module, declarations_by_module = load_records()
    for spec in SPECS:
        occurrences = occurrences_by_module.get(spec.module, [])
        declarations = declarations_by_module.get(spec.module, [])
        if len(occurrences) != spec.expected_occurrences:
            raise RuntimeError(
                f"scope inventory for {spec.module}: expected {spec.expected_occurrences}, "
                f"found {len(occurrences)}"
            )
        if not declarations:
            raise RuntimeError(f"scope inventory found no declarations for {spec.module}")
        results = [classify(occurrence, declarations) for occurrence in occurrences]
        if len(results) != len(occurrences):
            raise RuntimeError(f"scope classification did not partition {spec.module}")
        if any(result["action"] == "unresolved" for result in results):
            apply_execution_evidence(
                spec.module,
                spec.source.read_bytes(),
                results,
                timeout=600,
            )
        for result in results:
            validate_scope_dimensions(
                result.get("executionRole"),
                result.get("declarationKind"),
                result.get("action"),
            )
        role_counts = Counter(str(result["executionRole"]) for result in results)
        action_counts = Counter(str(result["action"]) for result in results)
        if spec.fixture:
            assert_fixture(results)
        unresolved = [
            result for result in results if result["action"] == "unresolved"
        ]
        print(
            f"boundary scope {spec.module}: {len(results)} occurrences, "
            + ", ".join(
                f"role.{kind}={count}" for kind, count in sorted(role_counts.items())
            )
            + ", "
            + ", ".join(
                f"action.{kind}={count}" for kind, count in sorted(action_counts.items())
            )
        )
        for result in unresolved:
            occurrence = result["occurrence"]
            print(
                "boundary scope unresolved: "
                f"{spec.module}:{occurrence['line']}:{occurrence['column']} "
                f"{result['reason']}; source={occurrence['source']!r}"
            )
        if unresolved:
            raise RuntimeError(
                f"scope checker left {len(unresolved)} unresolved occurrences in "
                f"{spec.module}"
            )


if __name__ == "__main__":
    main()
