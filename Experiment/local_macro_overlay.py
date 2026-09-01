#!/usr/bin/env python3
"""Fail-closed lowering of the authenticated elliptic-curve local macros.

The source inventory records the ``simp only`` inside a local macro quotation,
but the ordinary recorder cannot execute that quotation once the macro is
removed from its source module.  This module authenticates the exact manifest
records for the twelve elliptic-curve modules, comments out each complete macro
command, and expands every bare same-module use to the fixed tactic body.  It
does not elaborate Lean or infer a replacement.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import textwrap
from typing import Any, Mapping

import simp_engine_inventory as inventory


ROOT = Path(__file__).resolve().parents[1]
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"
MANIFEST_KIND = "simp_engine_boundary_manifest"
MANIFEST_SCHEMA = 2
MACRO_PREFIX = "Mathlib/AlgebraicGeometry/EllipticCurve/"
EXPECTED_DEFINITIONS = 22
EXPECTED_MODULES = 12
EXPECTED_INVOCATIONS = 88

TARGET_MODULES = frozenset(
    {
        "Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean",
        "Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean",
        "Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean",
        "Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean",
        "Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Basic.lean",
        "Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean",
        "Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean",
        "Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.lean",
        "Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean",
        "Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean",
        "Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean",
        "Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean",
    }
)

_LOCAL_MACRO_START = re.compile(r"(?m)^[ \t]*local[ \t]+macro\b")
_MACRO_HEAD = re.compile(
    r'^local[ \t]+macro[ \t]+"([A-Za-z_][A-Za-z0-9_]*)"'
    r'[ \t]*:[ \t]*tactic[ \t]*=>[ \t]*$'
)
_TOKEN = re.compile(r"(?<![A-Za-z0-9_'])[A-Za-z_][A-Za-z0-9_']*(?![A-Za-z0-9_'])")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _error(message: str) -> RuntimeError:
    return RuntimeError(f"local macro lowering: {message}")


def _mask_lean(source: str) -> str:
    """Mask comments and strings while retaining byte/character positions."""
    chars = list(source)
    i = 0
    while i < len(source):
        if source.startswith("--", i):
            j = source.find("\n", i)
            j = len(source) if j < 0 else j
            chars[i:j] = " " * (j - i)
            i = j
            continue
        if source.startswith("/-", i):
            start = i
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise _error(f"unterminated block comment at character {start}")
            chars[start:i] = "".join("\n" if c == "\n" else " " for c in source[start:i])
            continue
        if source[i] == '"':
            start = i
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise _error(f"unterminated string at character {start}")
            chars[start:i] = "".join("\n" if c == "\n" else " " for c in source[start:i])
            continue
        i += 1
    return "".join(chars)


def _line_column(source: str, position: int) -> int:
    return len(source[source.rfind("\n", 0, position) + 1 : position].expandtabs(8))


def _char_offset(source: str, byte_offset: int) -> int:
    """Convert an authenticated UTF-8 byte offset to a character offset."""
    if byte_offset < 0:
        raise _error("negative source offset")
    try:
        return len(source.encode("utf-8")[:byte_offset].decode("utf-8"))
    except UnicodeDecodeError as error:
        raise _error(f"source offset {byte_offset} splits UTF-8") from error


def _byte_offset(source: str, char_offset: int) -> int:
    return len(source[:char_offset].encode("utf-8"))


def _command_from_record(source: str, record: Mapping[str, Any], module: str) -> "MacroDefinition":
    start = record.get("startByte")
    end = record.get("endByte")
    command_start = record.get("commandStartByte")
    command_end = record.get("commandEndByte")
    for value, label in (
        (start, "startByte"), (end, "endByte"),
        (command_start, "commandStartByte"), (command_end, "commandEndByte"),
    ):
        if type(value) is not int or value < 0:
            raise _error(f"{module} macro record has invalid {label}")
    source_bytes = len(source.encode("utf-8"))
    if not start < end <= source_bytes or not command_start < command_end <= source_bytes:
        raise _error(f"{module} macro record has an invalid source range")
    if not command_start <= start < end <= command_end:
        raise _error(f"{module} macro tactic is outside its command range")
    if record.get("executionRole") != "reusable_executable":
        raise _error(f"{module} target record is not reusable_executable")
    if record.get("declarationKind") != "caller_dependent":
        raise _error(f"{module} target record has unexpected declaration kind")
    if record.get("action") != "materialize" or record.get("kind") != "simp_only":
        raise _error(f"{module} target record is not a materializable simp only")
    if record.get("syntaxKind") != "Lean.Parser.Tactic.simp":
        raise _error(f"{module} target record has unexpected syntax kind")
    if record.get("commandKind") != "Lean.Parser.Command.macro":
        raise _error(f"{module} target record is not owned by a macro command")
    start_char, end_char = _char_offset(source, start), _char_offset(source, end)
    command_start_char = _char_offset(source, command_start)
    command_end_char = _char_offset(source, command_end)
    actual = source[start_char:end_char]
    if actual != record.get("source"):
        raise _error(f"{module} target source bytes changed at {start}:{end}")
    expected_id = inventory.occurrence_id(module, start, end)
    if record.get("id") != expected_id:
        raise _error(f"{module} target occurrence identity changed")

    command = source[command_start_char:command_end_char]
    lines = command.splitlines()
    if not lines:
        raise _error(f"{module} macro command is empty")
    head = _MACRO_HEAD.fullmatch(lines[0].strip())
    if head is None:
        raise _error(f"{module} macro is not a nullary tactic local macro")
    name = head.group(1)
    quote = "`(tactic|"
    quote_at = command.find(quote)
    if quote_at < 0 or not command.rstrip().endswith(")"):
        raise _error(f"{module} macro {name} does not have one closed tactic quotation")
    # The manifest occurrence must be the unique ``simp only`` text in the
    # quotation.  This binds both the command range and the executable body.
    body_start = quote_at + len(quote)
    body = command[body_start:-1].strip()
    if not re.fullmatch(r"simp only \[.*\]", body, flags=re.DOTALL):
        raise _error(f"{module} macro {name} is not an exact simp-only body")
    if any(token in body for token in ("$", "`", "%", "?")):
        raise _error(f"{module} macro {name} contains an antiquotation or option")
    body_offset = command.find(body, body_start)
    if body_offset < 0 or command.find(body, body_offset + 1) >= 0:
        raise _error(f"{module} macro {name} has an ambiguous tactic body")
    body_start_byte = command_start + len(command[:body_offset].encode("utf-8"))
    body_end_byte = body_start_byte + len(body.encode("utf-8"))
    if body_start_byte != start or body_end_byte != end:
        raise _error(f"{module} macro {name} manifest range is not its exact tactic body")
    if not source[command_start_char : command_start_char + len(lines[0])].startswith("local macro"):
        raise _error(f"{module} macro {name} command starts unexpectedly")
    return MacroDefinition(
        module=module,
        occurrence_id=str(record["id"]),
        name=name,
        command_start=command_start,
        command_end=command_end,
        source_start=start,
        source_end=end,
        command=command,
        body=body,
    )


@dataclass(frozen=True)
class MacroDefinition:
    module: str
    occurrence_id: str
    name: str
    command_start: int  # authenticated byte offsets
    command_end: int
    source_start: int
    source_end: int
    command: str
    body: str


@dataclass(frozen=True)
class MacroInvocation:
    module: str
    name: str
    start: int  # UTF-8 byte offsets in the original source
    end: int
    original: str
    body: str


@dataclass(frozen=True)
class LoweredModule:
    module: str
    source: bytes
    definitions: tuple[MacroDefinition, ...]
    invocations: tuple[MacroInvocation, ...]
    generated_ranges: tuple[tuple[int, int, str], ...]


def _is_tactic_position(masked: str, start: int, end: int) -> bool:
    """Accept only a bare tactic token in an unambiguous sequence position."""
    line_start = masked.rfind("\n", 0, start) + 1
    prefix = masked[line_start:start].rstrip()
    suffix_end = masked.find("\n", end)
    if suffix_end < 0:
        suffix_end = len(masked)
    suffix = masked[end:suffix_end].lstrip()
    previous = prefix[-1] if prefix else None
    following = suffix[0] if suffix else None
    after_by = re.search(r"\bby[ \t]*$", prefix) is not None
    if previous is not None and previous not in ";>|({" and not after_by:
        return False
    if following is not None and following not in ";<|)},":
        return False
    return True


def _definition_candidates(source: str) -> tuple[int, ...]:
    masked = _mask_lean(source)
    return tuple(match.start() for match in _LOCAL_MACRO_START.finditer(masked))


def _module_lowering(
    module: str,
    source: bytes,
    records: list[Mapping[str, Any]],
    *,
    expected_definitions: int = EXPECTED_DEFINITIONS,
    expected_invocations: int = EXPECTED_INVOCATIONS,
) -> LoweredModule:
    try:
        source_text = source.decode("utf-8")
    except UnicodeDecodeError as error:
        raise _error(f"{module} source is not UTF-8") from error
    definitions = tuple(
        _command_from_record(source_text, record, module)
        for record in sorted(records, key=lambda item: int(item["commandStartByte"]))
    )
    if len(definitions) != expected_definitions and expected_definitions >= 0:
        raise _error(f"expected {expected_definitions} definitions, found {len(definitions)}")
    if len({item.name for item in definitions}) != len(definitions):
        raise _error(f"{module} contains colliding local macro names")
    command_starts = tuple(item.command_start for item in definitions)
    candidate_bytes = tuple(_byte_offset(source_text, position) for position in _definition_candidates(source_text))
    if candidate_bytes != command_starts:
        raise _error(f"{module} has an unmanifested or mislocated local macro command")
    ranges = tuple((item.command_start, item.command_end) for item in definitions)
    names = {item.name: item for item in definitions}
    masked = _mask_lean(source_text)
    invocations: list[MacroInvocation] = []
    for name, definition in names.items():
        for match in re.finditer(
            r"(?<![A-Za-z0-9_'])" + re.escape(name) + r"(?![A-Za-z0-9_'])", masked
        ):
            start, end = match.span()
            if any(_char_offset(source_text, left) <= start < _char_offset(source_text, right) for left, right in ranges):
                # Quoted macro names are masked.  Any surviving occurrence in
                # a command body is a collision, rather than an invocation.
                raise _error(f"{module} macro name collides inside a definition")
            if start <= _char_offset(source_text, definition.command_end):
                raise _error(f"{module} macro {name} occurs before its definition")
            if not _is_tactic_position(masked, start, end):
                raise _error(f"{module} macro name collision at {start}:{end}")
            invocations.append(
                MacroInvocation(
                    module, name, _byte_offset(source_text, start),
                    _byte_offset(source_text, end), source_text[start:end], definition.body
                )
            )
    invocations.sort(key=lambda item: item.start)
    if len(invocations) != expected_invocations and expected_invocations >= 0:
        raise _error(f"expected {expected_invocations} invocations, found {len(invocations)}")
    # Edits use character offsets for safe slicing; authenticated manifest
    # offsets and generated ranges remain UTF-8 byte offsets at the boundary.
    edits: list[tuple[int, int, bytes, str | None]] = []
    for definition in definitions:
        edits.append((
            _char_offset(source_text, definition.command_start),
            _char_offset(source_text, definition.command_end),
            _comment_definition(definition.command), None,
        ))
    for invocation in invocations:
        edits.append((
            _char_offset(source_text, invocation.start),
            _char_offset(source_text, invocation.end),
            _render_invocation(source_text, invocation), invocation.body,
        ))
    edits.sort(key=lambda item: item[0])
    for prior, current in zip(edits, edits[1:]):
        if current[0] < prior[1]:
            raise _error(f"{module} lowering edits overlap")
    chunks: list[str] = []
    cursor = 0
    generated: list[tuple[int, int, str]] = []
    delta = 0
    for start, end, replacement, body in edits:
        chunks.append(source_text[cursor:start])
        if body is not None:
            text = replacement.decode("utf-8")
            body_bytes = _render_body(source_text, start, body).encode("utf-8")
            output_start = _byte_offset(source_text, start) + delta
            generated.append((output_start, output_start + len(body_bytes), body_bytes.decode("utf-8")))
            # ``replacement`` starts with the rendered body; this assertion
            # catches accidental comment placement changes in future edits.
            if not text.startswith(body_bytes.decode("utf-8")):
                raise _error(f"{module} generated invocation body is not exact")
        chunks.append(replacement.decode("utf-8"))
        delta += len(replacement) - len(source_text[start:end].encode("utf-8"))
        cursor = end
    chunks.append(source_text[cursor:])
    return LoweredModule(module, "".join(chunks).encode("utf-8"), definitions, tuple(invocations), tuple(generated))


def _comment_definition(command: str) -> bytes:
    lines = command.split("\n")
    return ("-- Original local macro definition:\n" + "\n".join("-- " + line for line in lines)).encode("utf-8")


def _render_body(source: str, start: int, body: str) -> str:
    body = textwrap.dedent(body)
    lines = body.split("\n")
    if len(lines) == 1:
        return body
    indent = " " * (_line_column(source, start) + 2)
    return lines[0] + "\n" + "\n".join(indent + line.lstrip() for line in lines[1:])


def _render_invocation(source: str, invocation: MacroInvocation) -> bytes:
    start_char = _char_offset(source, invocation.start)
    end_char = _char_offset(source, invocation.end)
    rendered = _render_body(source, start_char, invocation.body)
    line_end = source.find("\n", end_char)
    if line_end < 0:
        line_end = len(source)
    trailing = source[end_char:line_end]
    comment = f"Original local macro invocation: {invocation.original}"
    if trailing.strip():
        rendered += f" /- {comment} -/"
    else:
        rendered += "\n" + " " * _line_column(source, start_char) + "-- " + comment
    return rendered.encode("utf-8")


def _read_manifest(path: Path) -> tuple[bytes, Mapping[str, Any]]:
    try:
        raw = path.read_bytes()
        manifest = json.loads(raw)
    except (OSError, json.JSONDecodeError) as error:
        raise _error(f"cannot read manifest {path}: {error}") from error
    if not isinstance(manifest, dict) or manifest.get("kind") != MANIFEST_KIND or manifest.get("reportSchema") != MANIFEST_SCHEMA:
        raise _error("only schema-2 boundary manifests are accepted")
    if manifest.get("allowDirty") is not False or manifest.get("allowUnresolved") is not False:
        raise _error("manifest must be closed")
    if not isinstance(manifest.get("modules"), list):
        raise _error("manifest modules must be an array")
    return raw, manifest


def lower_manifest(
    manifest_path: Path,
    *,
    source_root: Path = MATHLIB,
    expected_definitions: int = EXPECTED_DEFINITIONS,
    expected_modules: int = EXPECTED_MODULES,
    expected_invocations: int = EXPECTED_INVOCATIONS,
) -> tuple[str, dict[str, LoweredModule]]:
    """Authenticate and lower the complete production macro set.

    The expected-count keyword arguments are only for small parser fixtures;
    production callers use the defaults and therefore cannot opt into partial
    lowering accidentally.
    """
    _raw, manifest = _read_manifest(manifest_path)
    modules = manifest["modules"]
    by_module: dict[str, Mapping[str, Any]] = {}
    for item in modules:
        if not isinstance(item, dict) or not isinstance(item.get("module"), str):
            raise _error("manifest module record is invalid")
        module = str(item["module"])
        if module in by_module:
            raise _error(f"manifest contains duplicate module {module}")
        by_module[module] = item
    selected = set()
    records_by_module: dict[str, list[Mapping[str, Any]]] = {}
    for module, item in by_module.items():
        occurrences = item.get("occurrences")
        if not isinstance(occurrences, list):
            raise _error(f"{module} occurrences are invalid")
        target = [
            record for record in occurrences
            if isinstance(record, dict)
            and record.get("executionRole") == "reusable_executable"
            and module.startswith(MACRO_PREFIX)
        ]
        if target:
            selected.add(module)
            records_by_module[module] = target
    if selected != TARGET_MODULES:
        raise _error(f"authenticated target modules differ: {sorted(selected)}")
    if expected_modules >= 0 and len(selected) != expected_modules:
        raise _error(f"expected {expected_modules} target modules, found {len(selected)}")
    total = sum(len(value) for value in records_by_module.values())
    if expected_definitions >= 0 and total != expected_definitions:
        raise _error(f"expected {expected_definitions} definitions, found {total}")
    lowered: dict[str, LoweredModule] = {}
    for module in sorted(selected):
        item = by_module[module]
        source_path = (source_root / Path(*module.split("/"))).resolve()
        try:
            source_path.relative_to(source_root.resolve())
            source = source_path.read_bytes()
        except (OSError, ValueError) as error:
            raise _error(f"cannot read pinned source for {module}") from error
        if item.get("sourceHash") != sha256(source):
            raise _error(f"canonical source hash changed for {module}")
        lowered[module] = _module_lowering(
            module, source, records_by_module[module],
            expected_definitions=-1, expected_invocations=-1,
        )
    invocation_count = sum(len(value.invocations) for value in lowered.values())
    if expected_invocations >= 0 and invocation_count != expected_invocations:
        raise _error(f"expected {expected_invocations} invocations, found {invocation_count}")
    return sha256(_raw), lowered
