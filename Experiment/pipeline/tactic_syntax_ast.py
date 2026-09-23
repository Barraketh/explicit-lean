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
import subprocess
import tempfile
from typing import Any


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
    if byte_offset < 0 or byte_offset > len(source_bytes):
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
        command = [
            "lake", "env", "lean", "--run", str(EXTRACTOR), module,
            str(source_snapshot), "--simp-inventory",
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
        result, module=module, source=source, source_bytes=source_bytes, digest=digest,
    )


def _validate_simp_inventory_result(
    result: Any,
    *,
    module: str,
    source: str,
    source_bytes: bytes,
    digest: str,
    allow_parse_failure: bool = False,
) -> dict[str, Any]:
    if (not isinstance(result, dict) or result.get("module") != module
            or not isinstance(result.get("status"), str)):
        raise SyntaxExtractionError(
            "Lean simp syntax inventory was incomplete or malformed: " +
            json.dumps(result, ensure_ascii=False, sort_keys=True)[:2000]
        )
    if result.get("status") != "ok":
        if allow_parse_failure:
            result["moduleSourceSha256"] = digest
            return result
        raise SyntaxExtractionError(
            "Lean simp syntax inventory was incomplete or malformed: " +
            json.dumps(result, ensure_ascii=False, sort_keys=True)[:2000]
        )
    if not isinstance(result.get("commands"), list):
        raise SyntaxExtractionError("Lean simp syntax inventory has no command array")
    _annotate_scalar_ranges(result, source_bytes)

    commands = result["commands"]
    all_sites: list[tuple[int, int, int]] = []
    previous_command_end = 0
    for ordinal, entry in enumerate(commands):
        if (not isinstance(entry, dict) or entry.get("commandOrdinal") != ordinal
                or not isinstance(entry.get("kind"), str)
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
    if all_sites != sorted(all_sites):
        raise SyntaxExtractionError("Lean simp syntax ranges are not in source order")
    result["moduleSourceSha256"] = digest
    return result


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
    snapshots: list[tuple[str, str, bytes, str]] = []
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
        snapshots.append((module, source, source_bytes, digest))

    with tempfile.TemporaryDirectory(prefix="lean-simp-inventory-batch-") as temp_dir:
        arguments = ["lake", "env", "lean", "--run", str(EXTRACTOR),
                     "--simp-inventory-batch"]
        for ordinal, (module, _, source_bytes, _) in enumerate(snapshots):
            path = Path(temp_dir) / f"module-{ordinal:04}.lean"
            path.write_bytes(source_bytes)
            arguments.extend((module, str(path)))
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
            allow_parse_failure=True,
        )
        for result, (module, source, source_bytes, digest) in zip(raw_results, snapshots)
    ]


def assert_success_commands_have_no_simp(
    *,
    module: str,
    original_source: str,
    candidate_source: str,
    expected_source_sha256: str,
    command_rows: list[dict[str, Any]],
    success_ordinals: set[int],
    repo_root: str | Path = ROOT,
) -> None:
    """Refuse success persistence while any owned command still parses simp.

    The original DB command rows are authenticated against the complete source
    digest, exact byte ranges, command kinds, and per-command digests.  The
    candidate is parsed as a complete module and must preserve the DB command
    ordinal/kind sequence.  Only exact ``Lean.Parser.Tactic.simp`` nodes in
    commands being marked successful are forbidden.  Configuration syntax
    such as ``aesop (add simp ...)`` is intentionally outside this predicate.
    """
    if not success_ordinals:
        return

    candidate = authenticated_candidate_simp_inventory(
        module=module,
        original_source=original_source,
        candidate_source=candidate_source,
        expected_source_sha256=expected_source_sha256,
        command_rows=command_rows,
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
    repo_root: str | Path = ROOT,
) -> dict[str, Any]:
    """Parse a candidate and authenticate its command ordinals to source DB rows."""
    try:
        original_bytes = original_source.encode("utf-8", errors="strict")
    except UnicodeEncodeError as error:
        raise ValueError("original module source is not valid UTF-8") from error
    if hashlib.sha256(original_bytes).hexdigest() != expected_source_sha256:
        raise ValueError("original module source SHA-256 does not match authenticated digest")
    previous_end = 0
    for ordinal, row in enumerate(command_rows):
        start = row.get("start", row.get("start_byte"))
        stop = row.get("end", row.get("end_byte"))
        digest = row.get("sha256", row.get("source_sha256", row.get("sha")))
        kind = row.get("kind")
        if (type(row.get("ordinal")) is not int or row.get("ordinal") != ordinal
                or not isinstance(start, int) or isinstance(start, bool)
                or not isinstance(stop, int) or isinstance(stop, bool)
                or not (previous_end <= start < stop <= len(original_bytes))
                or not isinstance(kind, str) or not kind
                or not isinstance(digest, str)
                or hashlib.sha256(original_bytes[start:stop]).hexdigest() != digest):
            raise SyntaxExtractionError(
                f"source-command DB identity is not authenticated at ordinal {ordinal}"
            )
    candidate_digest = hashlib.sha256(candidate_source.encode("utf-8", errors="strict")).hexdigest()
    candidate = inventory_simp_tactics(
        module=module,
        source=candidate_source,
        expected_source_sha256=candidate_digest,
        repo_root=repo_root,
    )
    candidate_commands = candidate["commands"]
    if len(candidate_commands) != len(command_rows):
        raise SyntaxExtractionError(
            "candidate command count differs from authenticated source-command DB"
        )
    for ordinal, (row, after) in enumerate(zip(command_rows, candidate_commands)):
        if row["kind"] != after["kind"] or after["commandOrdinal"] != ordinal:
            raise SyntaxExtractionError(
                f"candidate command kind/ordinal differs from authenticated DB owner at ordinal {ordinal}"
            )
    return candidate


def inspect_term_elaboration_boundary(
    *,
    module: str,
    source_path: str | Path,
    expected_source_sha256: str,
    mathlib_root: str | Path | None = None,
    repo_root: str | Path = ROOT,
    require_pinned_path: bool = True,
) -> dict[str, Any]:
    """Fail closed if parsed source defines a term syntax/elaboration hook.

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
