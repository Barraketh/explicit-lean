"""Authenticated source-range lookup in Lean's tactic syntax tree.

Offsets passed by the pipeline are Unicode scalar indices into the exact
decoded source text.  This wrapper authenticates the source and site before
converting those indices to UTF-8 byte offsets for Lean's parser API.

The Lean helper installs imports, namespaces, opens, and source-local
syntax/notation needed by the incremental parser.  It deliberately has no
full-elaboration fallback: an unsupported parser-context command (currently a
source-local ``macro`` declaration) refuses the module instead of executing
arbitrary module commands or guessing a syntax tree.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any

if __package__:
    from . import sites as source_sites
else:
    import sites as source_sites  # type: ignore[no-redef]


ROOT = Path(__file__).resolve().parents[2]
EXTRACTOR = ROOT / "Experiment" / "TacticSyntaxExtractor.lean"


class SyntaxExtractionError(ValueError):
    """The requested authenticated site has no unique tactic syntax owner."""


def _char_to_byte(source: str, scalar_offset: int) -> int:
    if not isinstance(scalar_offset, int) or isinstance(scalar_offset, bool):
        raise ValueError("source offsets must be Unicode scalar indices")
    if scalar_offset < 0 or scalar_offset > len(source):
        raise ValueError(f"source offset is outside the source: {scalar_offset}")
    return len(source[:scalar_offset].encode("utf-8"))


def _byte_to_char(source_bytes: bytes, byte_offset: int) -> int:
    if (not isinstance(byte_offset, int) or isinstance(byte_offset, bool)
            or byte_offset < 0 or byte_offset > len(source_bytes)):
        raise ValueError(f"Lean syntax byte offset is outside the source: {byte_offset}")
    try:
        return len(source_bytes[:byte_offset].decode("utf-8", errors="strict"))
    except UnicodeDecodeError as error:
        raise ValueError(f"Lean syntax range splits a UTF-8 scalar at byte {byte_offset}") from error


def _annotate_scalar_ranges(value: Any, source_bytes: bytes) -> None:
    if isinstance(value, dict):
        if isinstance(value.get("startByte"), int) and isinstance(value.get("endByte"), int):
            value["startChar"] = _byte_to_char(source_bytes, value["startByte"])
            value["endChar"] = _byte_to_char(source_bytes, value["endByte"])
        for child in value.values():
            _annotate_scalar_ranges(child, source_bytes)
    elif isinstance(value, list):
        for child in value:
            _annotate_scalar_ranges(child, source_bytes)


def _validate_pinned_module(module: str, source_path: Path,
                            mathlib_root: Path | None) -> None:
    if not module.startswith("Mathlib."):
        raise ValueError("module must be a fully qualified pinned Mathlib module")
    if mathlib_root is None:
        mathlib_root = ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"
    expected = mathlib_root.joinpath(*module.split(".")[1:]).with_suffix(".lean")
    if source_path.resolve() != expected.resolve():
        raise ValueError("source path does not match the pinned Mathlib module")


def extract_tactic_ancestry(
    *,
    module: str,
    source_path: str | Path,
    start_char: int,
    end_char: int,
    expected_text: str,
    expected_source_sha256: str,
    mathlib_root: str | Path | None = None,
    repo_root: str | Path = ROOT,
    require_pinned_path: bool = True,
    raise_on_refusal: bool = True,
) -> dict[str, Any]:
    """Return unique tactic syntax ancestry for one authenticated source site.

    The digest authenticates the entire decoded module, while ``expected_text``
    authenticates the exact requested source slice.  The default mode also
    binds ``module`` to its canonical path inside the pinned Mathlib checkout.
    Synthetic parser fixtures may disable the path binding.  Diagnostic batch
    callers may set ``raise_on_refusal=False`` to inspect per-site refusals;
    the normal single-site API raises on any refusal.
    """
    results = extract_tactic_ancestries(
        module=module,
        source_path=source_path,
        sites=[{
            "start_char": start_char, "end_char": end_char,
            "expected_text": expected_text,
        }],
        expected_source_sha256=expected_source_sha256,
        mathlib_root=mathlib_root,
        repo_root=repo_root,
        require_pinned_path=require_pinned_path,
        raise_on_refusal=raise_on_refusal,
    )
    return results[0]


def extract_tactic_ancestries(
    *,
    module: str,
    source_path: str | Path,
    sites: list[dict[str, Any]],
    expected_source_sha256: str,
    mathlib_root: str | Path | None = None,
    repo_root: str | Path = ROOT,
    require_pinned_path: bool = True,
    raise_on_refusal: bool = True,
) -> list[dict[str, Any]]:
    """Batch extraction so Lean parses the authenticated module only once."""
    path = Path(source_path).resolve()
    source_bytes = path.read_bytes()
    try:
        source = source_bytes.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise ValueError("module source is not valid UTF-8") from error
    digest = hashlib.sha256(source_bytes).hexdigest()
    if digest != expected_source_sha256:
        raise ValueError("module source SHA-256 does not match authenticated digest")
    ranges: list[tuple[int, int, str]] = []
    for site in sites:
        start_char = site.get("start_char")
        end_char = site.get("end_char")
        expected_text = site.get("expected_text")
        if not isinstance(start_char, int) or isinstance(start_char, bool) or \
                not isinstance(end_char, int) or isinstance(end_char, bool):
            raise ValueError("source offsets must be Unicode scalar indices")
        if start_char < 0 or end_char <= start_char or end_char > len(source):
            raise ValueError("authenticated source range is invalid")
        actual_text = source[start_char:end_char]
        if actual_text != expected_text:
            raise ValueError("authenticated source slice does not match expected text")
        ranges.append((start_char, end_char, actual_text))
    if not ranges:
        raise ValueError("at least one authenticated site is required")
    if require_pinned_path:
        resolved_root = Path(mathlib_root).resolve() if mathlib_root else None
        _validate_pinned_module(module, path, resolved_root)

    with tempfile.TemporaryDirectory(prefix="lean-tactic-syntax-") as temp_dir:
        source_snapshot = Path(temp_dir) / path.name
        source_snapshot.write_bytes(source_bytes)
        command = [
            "lake", "env", "lean", "--run", str(EXTRACTOR), module,
            str(source_snapshot),
        ]
        for start_char, end_char, _text in ranges:
            command.extend((
                str(_char_to_byte(source, start_char)),
                str(_char_to_byte(source, end_char)),
            ))
        completed = subprocess.run(
            command, cwd=Path(repo_root), text=True,
            capture_output=True, check=False,
        )
    if completed.returncode != 0:
        raise RuntimeError(
            "Lean tactic syntax extraction failed: " +
            (completed.stderr.strip() or completed.stdout.strip())
        )
    try:
        results = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError("Lean tactic syntax extractor returned invalid JSON") from error
    if not isinstance(results, list) or len(results) != len(ranges):
        raise RuntimeError("Lean syntax extractor returned the wrong result count")
    for result, (start_char, end_char, actual_text) in zip(results, ranges):
        if result.get("status") != "ok" and raise_on_refusal:
            raise SyntaxExtractionError(
                f"Lean found no unique tactic syntax ancestry: {result.get('reason')} "
                f"(matches={result.get('matchCount')})"
            )
        result["moduleSourceSha256"] = digest
        result["targetStartChar"] = start_char
        result["targetEndChar"] = end_char
        result["targetText"] = actual_text
        _annotate_scalar_ranges(result, source_bytes)
    return results


def inventory_simp_tactics(
    *,
    module: str,
    source: str,
    expected_source_sha256: str,
    repo_root: str | Path = ROOT,
) -> dict[str, Any]:
    """Return every parsed ``Lean.Parser.Tactic.simp`` node with its command owner.

    The complete source is authenticated by its UTF-8 digest and parsed with
    Lean's module parser. Comments, strings, attributes, and tactic-configuration
    identifiers do not become ``Lean.Parser.Tactic.simp`` nodes. A parser or
    range refusal is an error; callers must not treat missing inventory as an
    empty inventory.
    """
    try:
        source_bytes = source.encode("utf-8", errors="strict")
    except UnicodeEncodeError as error:
        raise ValueError("module source is not valid UTF-8") from error
    digest = hashlib.sha256(source_bytes).hexdigest()
    if digest != expected_source_sha256:
        raise ValueError("module source SHA-256 does not match authenticated digest")
    if not module.startswith("Mathlib."):
        raise ValueError("module must be a fully qualified pinned Mathlib module")

    with tempfile.TemporaryDirectory(prefix="lean-simp-inventory-") as temp_dir:
        source_snapshot = Path(temp_dir) / (module.rsplit(".", 1)[-1] + ".lean")
        source_snapshot.write_bytes(source_bytes)
        request_id = hashlib.sha256(
            f"simp-inventory\0single\0{module}\0{digest}".encode("utf-8")
        ).hexdigest()
        command = [
            "lake", "env", "lean", "--run", str(EXTRACTOR), module,
            str(source_snapshot), request_id, "--simp-inventory",
        ]
        try:
            completed = subprocess.run(
                command, cwd=Path(repo_root), text=True,
                capture_output=True, check=False, timeout=300,
            )
        except subprocess.TimeoutExpired as error:
            raise RuntimeError("Lean simp syntax inventory timed out") from error
    if completed.returncode != 0:
        raise RuntimeError(
            "Lean simp syntax inventory failed closed: " +
            (completed.stderr.strip() or completed.stdout.strip())
        )
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError("Lean simp syntax inventory returned invalid JSON") from error
    return _validate_simp_inventory_result(
        result, module=module, source=source, source_bytes=source_bytes,
        digest=digest, request_id=request_id,
    )


def _validate_simp_inventory_result(
    result: Any,
    *,
    module: str,
    source: str,
    source_bytes: bytes,
    digest: str,
    request_id: str,
    allow_parse_failure: bool = False,
) -> dict[str, Any]:
    if (not isinstance(result, dict) or result.get("module") != module
            or result.get("requestId") != request_id
            or not isinstance(result.get("status"), str)):
        raise SyntaxExtractionError(
            "Lean simp syntax inventory was incomplete or malformed: " +
            json.dumps(result, ensure_ascii=False, sort_keys=True)[:2000]
        )
    if result.get("status") != "ok":
        if allow_parse_failure:
            if result.get("status") not in {"failed", "refused"} or not isinstance(
                    result.get("reason"), str) or not result["reason"]:
                raise SyntaxExtractionError("Lean simp syntax inventory has a malformed refusal")
            result["moduleSourceSha256"] = digest
            return result
        raise SyntaxExtractionError(
            "Lean simp syntax inventory was incomplete or malformed: " +
            json.dumps(result, ensure_ascii=False, sort_keys=True)[:2000]
        )
    if (result.get("reason") != "complete_simp_syntax_inventory"
            or result.get("refusals") != []):
        raise SyntaxExtractionError("Lean simp syntax inventory contains refusals or an invalid reason")
    if not isinstance(result.get("commands"), list):
        raise SyntaxExtractionError("Lean simp syntax inventory has no command array")
    _validate_raw_simp_ranges(result, len(source_bytes))
    _annotate_scalar_ranges(result, source_bytes)

    commands = result["commands"]
    all_sites: list[tuple[int, int, int]] = []
    previous_command_end = 0
    for ordinal, entry in enumerate(commands):
        if (not isinstance(entry, dict)
                or type(entry.get("commandOrdinal")) is not int
                or entry.get("commandOrdinal") != ordinal
                or not isinstance(entry.get("kind"), str)
                or not entry["kind"]
                or not isinstance(entry.get("simpSites"), list)):
            raise SyntaxExtractionError("Lean simp syntax inventory has malformed command ownership")
        start, stop = entry.get("startChar"), entry.get("endChar")
        if (not isinstance(start, int) or isinstance(start, bool)
                or not isinstance(stop, int) or isinstance(stop, bool)
                or not (previous_command_end <= start < stop <= len(source))):
            raise SyntaxExtractionError(
                f"Lean command range is invalid or overlapping at ordinal {ordinal}"
            )
        previous_command_end = stop
        theorem_body = entry.get("theoremBody")
        if theorem_body is not None:
            if not isinstance(theorem_body, dict):
                raise SyntaxExtractionError("Lean theorem body range is malformed")
            body_start = theorem_body.get("startChar")
            body_stop = theorem_body.get("endChar")
            if (not isinstance(body_start, int) or isinstance(body_start, bool)
                    or not isinstance(body_stop, int) or isinstance(body_stop, bool)
                    or not (start < body_start < body_stop <= stop)):
                raise SyntaxExtractionError(
                    f"Lean theorem body range is outside command ordinal {ordinal}"
                )
            if entry.get("theoremBodyForm") not in {"term", "whereStructInst"}:
                raise SyntaxExtractionError("Lean theorem body form is malformed")
        elif "theoremBodyForm" in entry:
            raise SyntaxExtractionError("Lean theorem body form has no range")
        for site in entry["simpSites"]:
            if (not isinstance(site, dict)
                    or site.get("kind") != "Lean.Parser.Tactic.simp"):
                raise SyntaxExtractionError("Lean simp syntax inventory contains an unexpected node")
            site_start, site_stop = site.get("startChar"), site.get("endChar")
            if (not isinstance(site_start, int) or isinstance(site_start, bool)
                    or not isinstance(site_stop, int) or isinstance(site_stop, bool)
                    or not (start <= site_start < site_stop <= stop)
                    or not source[site_start:site_stop].lstrip().startswith("simp")):
                raise SyntaxExtractionError(
                    f"Lean simp syntax range is invalid at command ordinal {ordinal}"
                )
            all_sites.append((site_start, site_stop, ordinal))
    if all_sites != sorted(all_sites) or len(all_sites) != len(set(all_sites)):
        raise SyntaxExtractionError("Lean simp syntax ranges are duplicate or not in source order")
    result["moduleSourceSha256"] = digest
    return result


def _validate_raw_simp_ranges(value: Any, source_size: int) -> None:
    """Reject malformed byte ranges before converting Lean offsets to scalars."""
    if isinstance(value, dict):
        has_start = "startByte" in value
        has_end = "endByte" in value
        if has_start != has_end:
            raise SyntaxExtractionError("Lean simp syntax inventory has a partial source range")
        if has_start:
            start, end = value["startByte"], value["endByte"]
            if (type(start) is not int or type(end) is not int
                    or not (0 <= start < end <= source_size)):
                raise SyntaxExtractionError("Lean simp syntax inventory has an invalid byte range")
        for child in value.values():
            _validate_raw_simp_ranges(child, source_size)
    elif isinstance(value, list):
        for child in value:
            _validate_raw_simp_ranges(child, source_size)


def inventory_simp_tactics_batch(
    modules: list[dict[str, str]],
    *,
    repo_root: str | Path = ROOT,
    timeout_seconds: int = 300,
) -> list[dict[str, Any]]:
    """Parse multiple authenticated module snapshots in one Lean process.

    Each entry has ``module``, ``source``, and ``expected_source_sha256``.
    Per-module parser refusals are returned with a non-``ok`` status so audit
    callers can report exactly which sources were not classifiable.
    """
    if not modules:
        return []
    if type(timeout_seconds) is not int or timeout_seconds <= 0:
        raise ValueError("batch simp inventory timeout must be a positive integer")
    snapshots: list[tuple[str, str, bytes, str, str]] = []
    for ordinal, entry in enumerate(modules):
        module = entry.get("module")
        source = entry.get("source")
        expected = entry.get("expected_source_sha256")
        if not isinstance(module, str) or not module.startswith("Mathlib."):
            raise ValueError(f"batch module {ordinal} is not a fully qualified Mathlib name")
        if not isinstance(source, str) or not isinstance(expected, str):
            raise ValueError(f"batch module {module} lacks source or authenticated digest")
        try:
            source_bytes = source.encode("utf-8", errors="strict")
        except UnicodeEncodeError as error:
            raise ValueError(f"module source is not valid UTF-8: {module}") from error
        digest = hashlib.sha256(source_bytes).hexdigest()
        if digest != expected:
            raise ValueError(f"module source SHA-256 does not match authenticated digest: {module}")
        request_id = hashlib.sha256(
            f"simp-inventory\0batch\0{ordinal}\0{module}\0{digest}".encode("utf-8")
        ).hexdigest()
        snapshots.append((module, source, source_bytes, digest, request_id))

    with tempfile.TemporaryDirectory(prefix="lean-simp-inventory-batch-") as temp_dir:
        arguments = ["lake", "env", "lean", "--run", str(EXTRACTOR),
                     "--simp-inventory-batch"]
        for ordinal, (module, _, source_bytes, _, request_id) in enumerate(snapshots):
            path = Path(temp_dir) / f"module-{ordinal:04}.lean"
            path.write_bytes(source_bytes)
            arguments.extend((module, str(path), request_id))
        try:
            completed = subprocess.run(
                arguments, cwd=Path(repo_root), text=True,
                capture_output=True, check=False, timeout=timeout_seconds,
            )
        except subprocess.TimeoutExpired as error:
            raise RuntimeError("Lean batched simp syntax inventory timed out") from error
    if completed.returncode != 0:
        raise RuntimeError(
            "Lean batched simp syntax inventory failed closed: " +
            (completed.stderr.strip() or completed.stdout.strip())
        )
    try:
        raw_results = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError("Lean batched simp syntax inventory returned invalid JSON") from error
    if not isinstance(raw_results, list) or len(raw_results) != len(snapshots):
        raise SyntaxExtractionError("Lean batched simp syntax inventory returned the wrong result count")
    return [
        _validate_simp_inventory_result(
            result, module=module, source=source,
            source_bytes=source_bytes, digest=digest,
            request_id=request_id,
            allow_parse_failure=True,
        )
        for result, (module, source, source_bytes, digest, request_id)
        in zip(raw_results, snapshots)
    ]


def assert_success_commands_have_no_simp(
    *,
    module: str,
    original_source: str,
    candidate_source: str,
    expected_source_sha256: str,
    command_rows: list[dict[str, Any]],
    success_ordinals: set[int],
    candidate_replacements: dict[int, str],
    repo_root: str | Path = ROOT,
) -> None:
    """Refuse success persistence while any owned command still parses simp.

    The original DB command rows must equal Lean's parsed original command
    ranges, kinds, and order. The candidate source is reconstructed using only
    those authenticated command ranges, the supplied replacements, and the
    deterministic recorder import. Its parsed command ranges must match that
    byte-level mapping exactly before simp nodes are checked. Configuration
    syntax such as ``aesop (add simp ...)`` is intentionally outside this
    predicate.
    """
    if not success_ordinals:
        return
    if (not isinstance(candidate_replacements, dict)
            or not success_ordinals.issubset(candidate_replacements)):
        raise SyntaxExtractionError(
            "every successful command must have an authenticated candidate replacement"
        )

    candidate = authenticated_candidate_simp_inventory(
        module=module,
        original_source=original_source,
        candidate_source=candidate_source,
        expected_source_sha256=expected_source_sha256,
        command_rows=command_rows,
        candidate_replacements=candidate_replacements,
        repo_root=repo_root,
    )
    candidate_commands = candidate["commands"]
    if any(type(ordinal) is not int or ordinal < 0 or ordinal >= len(candidate_commands)
           for ordinal in success_ordinals):
        raise SyntaxExtractionError("success ordinal is outside the authenticated command inventory")
    for ordinal in success_ordinals:
        after = candidate_commands[ordinal]
        if after["simpSites"]:
            sites = [
                {"startChar": site["startChar"], "endChar": site["endChar"]}
                for site in after["simpSites"]
            ]
            raise SyntaxExtractionError(
                f"success command {ordinal} still owns executable simp tactic node(s): "
                + json.dumps(sites, sort_keys=True)
            )


def authenticated_candidate_simp_inventory(
    *,
    module: str,
    original_source: str,
    candidate_source: str,
    expected_source_sha256: str,
    command_rows: list[dict[str, Any]],
    candidate_replacements: dict[int, str],
    repo_root: str | Path = ROOT,
) -> dict[str, Any]:
    """Bind source and candidate parser ranges to exact authenticated edits."""
    try:
        original_bytes = original_source.encode("utf-8", errors="strict")
        candidate_bytes = candidate_source.encode("utf-8", errors="strict")
    except UnicodeEncodeError as error:
        raise ValueError("module source is not valid UTF-8") from error
    if hashlib.sha256(original_bytes).hexdigest() != expected_source_sha256:
        raise ValueError("original module source SHA-256 does not match authenticated digest")
    if not isinstance(command_rows, list) or not isinstance(candidate_replacements, dict):
        raise SyntaxExtractionError("source-command identity or replacement map is malformed")

    candidate_digest = hashlib.sha256(candidate_bytes).hexdigest()
    inventories = inventory_simp_tactics_batch([
        {"module": module, "source": original_source,
         "expected_source_sha256": expected_source_sha256},
        {"module": module, "source": candidate_source,
         "expected_source_sha256": candidate_digest},
    ], repo_root=repo_root)
    if len(inventories) != 2 or any(item.get("status") != "ok" for item in inventories):
        raise SyntaxExtractionError("original or candidate Lean parser inventory refused")
    original_inventory, candidate = inventories
    original_commands = original_inventory["commands"]
    if len(original_commands) != len(command_rows):
        raise SyntaxExtractionError(
            "source-command DB row count differs from Lean's parsed original command count"
        )

    normalized_rows: list[dict[str, Any]] = []
    for ordinal, (row, parsed) in enumerate(zip(command_rows, original_commands)):
        if not isinstance(row, dict):
            raise SyntaxExtractionError(f"source-command DB row is malformed at ordinal {ordinal}")
        start = _row_int_alias(row, "start", "start_byte", ordinal)
        stop = _row_int_alias(row, "end", "end_byte", ordinal)
        digest = _row_string_alias(row, ("sha256", "source_sha256", "sha"), ordinal)
        kind = row.get("kind")
        if (type(row.get("ordinal")) is not int or row["ordinal"] != ordinal
                or start != parsed.get("startByte") or stop != parsed.get("endByte")
                or kind != parsed.get("kind")
                or not (0 <= start < stop <= len(original_bytes))
                or hashlib.sha256(original_bytes[start:stop]).hexdigest() != digest):
            raise SyntaxExtractionError(
                f"source-command DB identity/range differs from Lean parser at ordinal {ordinal}"
            )
        normalized_rows.append({
            "ordinal": ordinal, "start": start, "end": stop,
            "kind": kind, "digest": digest,
        })

    expected_candidate, expected_ranges = _candidate_from_authenticated_rows(
        original_source=original_source,
        command_rows=normalized_rows,
        candidate_replacements=candidate_replacements,
    )
    if candidate_source != expected_candidate:
        raise SyntaxExtractionError(
            "candidate source differs from authenticated command replacements and recorder import"
        )

    candidate_commands = candidate["commands"]
    if len(candidate_commands) != len(normalized_rows):
        raise SyntaxExtractionError(
            "candidate command count differs from authenticated source-command DB"
        )
    for ordinal, (row, after, expected_range) in enumerate(
            zip(normalized_rows, candidate_commands, expected_ranges)):
        expected_start, expected_end = expected_range
        if (after["commandOrdinal"] != ordinal or after["kind"] != row["kind"]
                or after["startByte"] != expected_start
                or after["endByte"] != expected_end):
            raise SyntaxExtractionError(
                f"candidate command identity/range differs from authenticated edit map at ordinal {ordinal}"
            )
    return candidate


def _row_int_alias(row: dict[str, Any], primary: str, alternate: str,
                   ordinal: int) -> int:
    values = [row[key] for key in (primary, alternate) if key in row]
    if (not values or any(type(value) is not int for value in values)
            or any(value != values[0] for value in values)):
        raise SyntaxExtractionError(f"source-command DB range is malformed at ordinal {ordinal}")
    return values[0]


def _row_string_alias(row: dict[str, Any], keys: tuple[str, ...], ordinal: int) -> str:
    values = [row[key] for key in keys if key in row]
    if (not values or any(not isinstance(value, str) for value in values)
            or any(value != values[0] for value in values)):
        raise SyntaxExtractionError(f"source-command DB digest is malformed at ordinal {ordinal}")
    return values[0]


def add_recorder_import(source: str) -> str:
    """Mirror the worker's deterministic ExplicitRw import insertion."""
    try:
        return source_sites.add_import(source)
    except ValueError:
        module_match = re.search(r"^module\s*$", source, re.M)
        import_line = ("public import ExplicitLean.ExplicitRw" if module_match
                       else "import ExplicitLean.ExplicitRw")
        if module_match:
            at = module_match.end()
            return source[:at] + "\n" + import_line + source[at:]
        return import_line + "\n" + source


def _candidate_from_authenticated_rows(
    *,
    original_source: str,
    command_rows: list[dict[str, Any]],
    candidate_replacements: dict[int, str],
) -> tuple[str, list[tuple[int, int]]]:
    original_bytes = original_source.encode("utf-8", errors="strict")
    if any(type(ordinal) is not int or ordinal < 0 or ordinal >= len(command_rows)
           for ordinal in candidate_replacements):
        raise SyntaxExtractionError(
            "candidate replacement ordinal is outside the parsed source commands"
        )
    replacement_bytes: dict[int, bytes] = {}
    for ordinal, replacement in candidate_replacements.items():
        if not isinstance(replacement, str) or not replacement.strip():
            raise SyntaxExtractionError(
                f"candidate replacement is blank or malformed at ordinal {ordinal}"
            )
        try:
            replacement_bytes[ordinal] = replacement.encode("utf-8", errors="strict")
        except UnicodeEncodeError as error:
            raise SyntaxExtractionError(
                f"candidate replacement is not valid UTF-8 at ordinal {ordinal}"
            ) from error

    edits = [
        (row["start"], row["end"], replacement_bytes[ordinal])
        for ordinal, row in enumerate(command_rows)
        if ordinal in replacement_bytes
    ]
    edited = original_bytes
    for start, stop, replacement in sorted(edits, reverse=True):
        edited = edited[:start] + replacement + edited[stop:]
    try:
        without_import = edited.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise SyntaxExtractionError("authenticated replacements produced invalid UTF-8") from error
    expected_source = add_recorder_import(without_import)
    expected_bytes = expected_source.encode("utf-8", errors="strict")
    header_delta = len(expected_bytes) - len(edited)
    if header_delta < 0:
        raise SyntaxExtractionError("generated recorder import has an invalid header offset")

    expected_ranges: list[tuple[int, int]] = []
    shift = header_delta
    for ordinal, row in enumerate(command_rows):
        start = row["start"] + shift
        if ordinal in replacement_bytes:
            length = len(replacement_bytes[ordinal])
            stop = start + length
            shift += length - (row["end"] - row["start"])
        else:
            stop = start + (row["end"] - row["start"])
        expected_ranges.append((start, stop))
    return expected_source, expected_ranges


def inspect_term_elaboration_boundary(
    *,
    module: str,
    source_path: str | Path,
    expected_source_sha256: str,
    mathlib_root: str | Path | None = None,
    repo_root: str | Path = ROOT,
    require_pinned_path: bool = True,
) -> dict[str, Any]:
    """Fail closed if parsed source defines an executable syntax/elaboration hook.

    This inventories Lean's authenticated command AST; it never searches the
    source text with regular expressions and never executes source commands.
    Syntax/notation declarations needed by the incremental parser are parsed
    by the existing extractor.  The source bytes and pinned Mathlib path are
    checked before the exact bytes are passed to Lean.
    """
    path = Path(source_path).resolve()
    source_bytes = path.read_bytes()
    try:
        source_bytes.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise ValueError("module source is not valid UTF-8") from error
    digest = hashlib.sha256(source_bytes).hexdigest()
    if digest != expected_source_sha256:
        raise ValueError("module source SHA-256 does not match authenticated digest")
    if require_pinned_path:
        resolved_root = Path(mathlib_root).resolve() if mathlib_root else None
        _validate_pinned_module(module, path, resolved_root)

    with tempfile.TemporaryDirectory(prefix="lean-term-elab-gate-") as temp_dir:
        source_snapshot = Path(temp_dir) / path.name
        source_snapshot.write_bytes(source_bytes)
        command = [
            "lake", "env", "lean", "--run", str(EXTRACTOR), module,
            str(source_snapshot), "--term-elab-gate",
        ]
        completed = subprocess.run(
            command, cwd=Path(repo_root), text=True,
            capture_output=True, check=False,
        )
    if completed.returncode != 0:
        raise RuntimeError(
            "Lean term-elaboration gate refused or failed to parse module: " +
            (completed.stderr.strip() or completed.stdout.strip())
        )
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError("Lean term-elaboration gate returned invalid JSON") from error
    if not isinstance(result, dict) or result.get("module") != module or \
            not isinstance(result.get("risks"), list):
        raise RuntimeError("Lean term-elaboration gate returned malformed inventory")
    result["moduleSourceSha256"] = digest
    _annotate_scalar_ranges(result, source_bytes)
    return result


def audit_executable_proof_holes(
    *,
    module: str,
    source: str,
    expected_source_sha256: str,
    repo_root: str | Path = ROOT,
) -> dict[str, Any]:
    """Find executable sorry/admit syntax in a complete candidate module.

    Lean's authenticated command AST excludes comments and string contents.
    ``sorry`` is recognized by its parser node; ``admit`` is conservatively
    recognized as an identifier token. Parser errors are refusals, never a
    clean audit. This is for generated candidate text, not a replacement for
    authenticating the original pinned module separately.
    """
    try:
        source_bytes = source.encode("utf-8", errors="strict")
    except UnicodeEncodeError as error:
        raise ValueError("candidate source is not valid UTF-8") from error
    digest = hashlib.sha256(source_bytes).hexdigest()
    if digest != expected_source_sha256:
        raise ValueError("candidate source SHA-256 does not match authenticated digest")
    with tempfile.TemporaryDirectory(prefix="lean-proof-hole-audit-") as temp_dir:
        source_snapshot = Path(temp_dir) / "Candidate.lean"
        source_snapshot.write_bytes(source_bytes)
        command = [
            "lake", "env", "lean", "--run", str(EXTRACTOR), module,
            str(source_snapshot), "--proof-hole-audit",
        ]
        completed = subprocess.run(
            command, cwd=Path(repo_root), text=True,
            capture_output=True, check=False,
        )
    if completed.returncode != 0:
        raise RuntimeError(
            "Lean proof-hole audit failed closed: " +
            (completed.stderr.strip() or completed.stdout.strip())
        )
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError("Lean proof-hole audit returned invalid JSON") from error
    if not isinstance(result, dict) or result.get("module") != module or \
            not isinstance(result.get("proofHoles"), list):
        raise RuntimeError("Lean proof-hole audit returned malformed inventory")
    result["moduleSourceSha256"] = digest
    _annotate_scalar_ranges(result, source_bytes)
    return result
