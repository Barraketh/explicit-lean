#!/usr/bin/env python3
"""End-to-end replay harness: trace a Mathlib module, render it, compile it.

    python3 -B Experiment/pipeline/replay_module.py \
        --module Mathlib/Logic/IsEmpty/Basic.lean \
        --t1 <T1 worktree> --t2 <T2 worktree> --out <dir>

Per module, in five stages:

1. **Transcribe.** Reuse T1's committed traced copy and manifest, stage both in
   a fresh T4-owned run tree, redirect generated trace paths into that tree,
   compile with T1's Lean environment, and finalize only its raw outputs.
2. **Render.** Translate each trace into replacement source text for its site:
   the original call preserved as a comment, deterministic indexed local and
   introduced handles where provenance requires them, then one `explicit_rw`
   per location. Complete multi-invocation sites are expanded into the source
   branch spine's leaves.
3. **Splice.** Write the translated module with every site replaced and
   `import ExplicitLean.ExplicitRw` added after the existing imports.
4. **Compile.** `lake env lean` the translated file in the T2 worktree, whose
   build carries `ExplicitRw`; Mathlib oleans are shared. Parse diagnostics
   and attribute isolated probes only when the source line is in their
   replacement block.
5. **Report.** `report.json` and `summary.md`: per site a status, the error
   text and an attribution guess, plus totals, both worktrees' commit hashes,
   and runtimes.

Both driven worktrees are read-only: staging, raw and final outputs are owned
by T4 under `--out`; the harness never reads or writes T1's shared meas_out.
Every other output lands under `--out`.

A site is `replayed` only when the compile that covers it reported zero errors.
Which compile that was is recorded per module as `compile_mode`: `whole_module`
when the entire translated module compiled clean, `per_site` when the module did
not and each site was then retried on its own (every other site reverted to the
original call), so a clean per-site compile still isolates one site's replay.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import render as R  # noqa: E402
import sites as S  # noqa: E402
import simp_family_lint as L  # noqa: E402
import simp_manual_overrides as M  # noqa: E402

# The six modules T1 has traced copies for: (Mathlib path, traced module name).
MODULES = {
    "Mathlib/Data/Option/Basic.lean": "OptionBasicTraced",
    "Mathlib/Logic/IsEmpty/Basic.lean": "IsEmptyBasicTraced",
    "Mathlib/Logic/Nontrivial/Defs.lean": "NontrivialDefsTraced",
    "Mathlib/Logic/Function/Defs.lean": "FunctionDefsTraced",
    "Mathlib/Logic/ExistsUnique.lean": "ExistsUniqueTraced",
    "Mathlib/Logic/Function/Basic.lean": "FunctionBasicTraced",
    "Mathlib/Logic/Basic.lean": "LogicBasicTraced",
}

# `lake env lean` diagnostics: `<file>:<line>:<col>: <severity>: <message>`.
# A message body runs on until the next diagnostic header, which is where
# `explicit_rw` prints the expected and actual subterms, so the report keeps it.
#
# The file group excludes newlines as well as colons: `[^:]` matches `\n`, so
# without that a header could be "found" mid-message, starting on a body line
# several lines below the real one and truncating the body that precedes it.
DIAG_RE = re.compile(r"^(?P<file>[^\s:][^:\n]*):(?P<line>\d+):(?P<col>\d+): "
                     r"(?P<sev>error|warning): (?P<msg>.*)$", re.M)

COMPILE_TIMEOUT = 30 * 60  # The coordination protocol's escalation threshold.


def run(cmd: list[str], cwd: pathlib.Path, timeout: int = COMPILE_TIMEOUT,
        env: dict[str, str] | None = None
        ) -> tuple[int, str, str, float]:
    started = time.monotonic()
    proc = subprocess.run(
        cmd, cwd=str(cwd), capture_output=True, text=True, timeout=timeout,
        env=env
    )
    return proc.returncode, proc.stdout, proc.stderr, time.monotonic() - started


def git_hash(worktree: pathlib.Path) -> str:
    code, out, _, _ = run(["git", "rev-parse", "HEAD"], worktree, timeout=60)
    return out.strip() if code == 0 else "unknown"


def git_dirty(worktree: pathlib.Path) -> bool:
    code, out, _, _ = run(["git", "status", "--porcelain"], worktree, timeout=60)
    return code != 0 or bool(out.strip())


def _char_offset(source: str, byte_offset: int) -> int:
    """Translate an authenticated UTF-8 byte offset to a Python index."""
    encoded = source.encode("utf-8")
    if not 0 <= byte_offset <= len(encoded):
        raise ValueError(f"manual override byte offset is outside the source: {byte_offset}")
    try:
        return len(encoded[:byte_offset].decode("utf-8"))
    except UnicodeDecodeError as error:
        raise ValueError(f"manual override byte offset splits UTF-8: {byte_offset}") from error


def manual_overrides_for_sites(
    module: str, source: str, site_list: list[S.Site],
) -> dict[int, dict]:
    """Bind the authenticated source overlay to exact replay site identities.

    The override database is byte-addressed while the replay scanner and trace
    manifests use Python character offsets.  Convert only after validating the
    database range/hash/occurrence against the exact source bytes, then require
    a one-to-one match with the scanner's site range and call text.
    """
    _, entries = M.load_database()
    selected = [entry for entry in entries if entry["module"] == module]
    if not selected:
        return {}
    source_bytes = source.encode("utf-8")
    M.validate_against_source(module, source_bytes, selected)
    by_identity = {
        (site.start, site.end, site.text): site.index
        for site in site_list
    }
    result: dict[int, dict] = {}
    for entry in selected:
        start = _char_offset(source, int(entry["startByte"]))
        end = _char_offset(source, int(entry["endByte"]))
        actual = source[start:end]
        key = (start, end, actual)
        site_index = by_identity.get(key)
        if site_index is None:
            raise RuntimeError(
                "manual override is not exactly one replay site: "
                f"{module}:{entry['occurrence']}"
            )
        if site_index in result:
            raise RuntimeError(f"duplicate manual override replay site: {module}:{site_index}")
        result[site_index] = entry
    return result


def render_manual_override(site: S.Site, entry: dict, source: str) -> dict:
    """Render one validated source overlay as a normal replay record."""
    rendered = M.render(entry, source.encode("utf-8")).decode("utf-8")
    lines = rendered.splitlines()
    if not lines or not any(line.lstrip().startswith("-- Original simp:") for line in lines):
        raise RuntimeError(f"manual override dropped its original comment: {entry['occurrence']}")
    return {
        "site": site.index,
        "line": site.line,
        "column": site.column,
        "original": site.text,
        "alone_on_line": site.alone_on_line,
        "long_line_waiver": False,
        "status": "rendered",
        "attribution": "manual_override",
        "detail": "authenticated manual source override",
        "manual_override": entry["occurrence"],
        "lines": lines,
        "lint_lines": lines,
        "replace_start": site.start,
        "replace_end": site.end,
    }


# --------------------------------------------------------------------------
# Authenticated source-site identity (simp-trace-v2)


def build_manifest(module_path: str, source: str,
                   site_list: list[S.Site]) -> dict:
    """Build the v2 manifest from the exact original source text."""
    return {
        "modulePath": module_path,
        "sites": [
            {
                "siteOrdinal": site.index,
                "startChar": site.start,
                "endChar": site.end,
                "line": site.line,
                "column": site.column,
                "callText": source[site.start:site.end],
            }
            for site in site_list
        ],
    }


def _identity_descriptor(site: dict) -> dict:
    return {key: site.get(key) for key in (
        "siteOrdinal", "startChar", "endChar", "line", "column", "callText",
    )}


def validate_identity(module_path: str, source: str,
                      site_list: list[S.Site], trace_records: list[dict]
                      ) -> tuple[dict, dict[int, list[dict]]]:
    """Validate a complete v2 trace set before any rendering is attempted.

    Returns a machine-readable result and, only on acceptance, traces grouped
    by authenticated source site ordinal. Filenames, list indexes and generated
    occurrence positions are never used as identity matches.
    """
    manifest = build_manifest(module_path, source, site_list)
    expected_by_key = {
        (module_path, site["siteOrdinal"], site["startChar"],
         site["endChar"], site["callText"]): site
        for site in manifest["sites"]
    }
    expected_by_ordinal = {site["siteOrdinal"]: site for site in manifest["sites"]}
    missing = {site["siteOrdinal"]: site for site in manifest["sites"]}
    extra: list[dict] = []
    duplicates: list[dict] = []
    invalid: list[dict] = []
    mismatches: list[dict] = []
    grouped: dict[int, list[dict]] = {}
    seen: dict[tuple[int, int], dict] = {}

    for record_index, record in enumerate(trace_records):
        if not isinstance(record, dict):
            invalid.append({"recordIndex": record_index, "reason": "record_not_object"})
            continue
        if "__parseError" in record:
            invalid.append({"recordIndex": record_index,
                            "reason": "malformed_json",
                            "file": record["__parseError"],
                            "detail": record.get("__parseDetail", "")})
            continue
        if record.get("schema") != "simp-trace-v2":
            invalid.append({"recordIndex": record_index,
                            "reason": "unsupported_schema",
                            "schema": record.get("schema")})
            continue
        required = ("modulePath", "site", "occurrence", "invocation",
                    "invocations", "locations")
        missing_fields = [key for key in required if key not in record]
        if missing_fields:
            invalid.append({"recordIndex": record_index,
                            "reason": "missing_fields", "fields": missing_fields})
            continue
        if record["modulePath"] != module_path:
            extra.append({"recordIndex": record_index,
                          "reason": "module_mismatch",
                          "modulePath": record.get("modulePath")})
            continue
        site = record["site"]
        if not isinstance(site, dict):
            invalid.append({"recordIndex": record_index, "reason": "site_not_object"})
            continue
        identity_fields = ("siteOrdinal", "startChar", "endChar", "callText")
        if any(field not in site for field in identity_fields):
            invalid.append({"recordIndex": record_index,
                            "reason": "missing_site_identity_fields",
                            "fields": [field for field in identity_fields if field not in site]})
            continue
        if (not isinstance(site["siteOrdinal"], int)
                or isinstance(site["siteOrdinal"], bool)
                or not isinstance(site["startChar"], int)
                or isinstance(site["startChar"], bool)
                or not isinstance(site["endChar"], int)
                or isinstance(site["endChar"], bool)
                or site["startChar"] < 0
                or site["endChar"] < site["startChar"]
                or not isinstance(site["callText"], str)):
            invalid.append({"recordIndex": record_index,
                            "reason": "malformed_site_identity",
                            "site": _identity_descriptor(site)})
            continue
        try:
            identity_key = (module_path, site["siteOrdinal"], site["startChar"],
                            site["endChar"], site["callText"])
        except TypeError:
            invalid.append({"recordIndex": record_index,
                            "reason": "unhashable_site_identity",
                            "site": _identity_descriptor(site)})
            continue
        expected = expected_by_key.get(identity_key)
        if expected is None:
            ordinal_expected = expected_by_ordinal.get(site.get("siteOrdinal"))
            if ordinal_expected is not None:
                mismatches.append({"recordIndex": record_index,
                                   "reason": "site_range_or_call_mismatch",
                                   "site": _identity_descriptor(site),
                                   "expected": _identity_descriptor(ordinal_expected)})
            else:
                extra.append({"recordIndex": record_index,
                              "reason": "unmatched_site_identity",
                              "site": _identity_descriptor(site)})
            continue
        if site.get("siteOrdinal") != expected["siteOrdinal"]:
            extra.append({"recordIndex": record_index,
                          "reason": "unmatched_site_identity",
                          "site": _identity_descriptor(site)})
            continue
        invocation = record["invocation"]
        total = record["invocations"]
        if (not isinstance(invocation, int) or isinstance(invocation, bool)
                or not isinstance(total, int) or isinstance(total, bool)
                or total < 1 or invocation < 0 or invocation >= total):
            invalid.append({"recordIndex": record_index,
                            "reason": "invalid_invocation",
                            "invocation": invocation, "invocations": total})
            continue
        if not isinstance(record["occurrence"], str):
            invalid.append({"recordIndex": record_index,
                            "reason": "occurrence_not_string"})
            continue
        if not isinstance(record["locations"], list):
            invalid.append({"recordIndex": record_index,
                            "reason": "locations_not_array"})
            continue
        key = (expected["siteOrdinal"], invocation)
        if key in seen:
            duplicates.append({"siteOrdinal": key[0], "invocation": key[1]})
            continue
        seen[key] = record
        grouped.setdefault(expected["siteOrdinal"], []).append(record)
        missing.pop(expected["siteOrdinal"], None)

    incomplete: list[dict] = []
    for site in manifest["sites"]:
        ordinal = site["siteOrdinal"]
        records = grouped.get(ordinal, [])
        totals = {record["invocations"] for record in records}
        if len(totals) != 1:
            if records or ordinal in missing:
                incomplete.append({"siteOrdinal": ordinal,
                                   "expectedOrdinals": [],
                                   "observedOrdinals": sorted(record["invocation"] for record in records),
                                   "declaredTotals": sorted(totals)})
            continue
        total = next(iter(totals))
        expected_ordinals = list(range(total))
        observed_ordinals = sorted(record["invocation"] for record in records)
        if observed_ordinals != expected_ordinals:
            incomplete.append({"siteOrdinal": ordinal,
                               "expectedOrdinals": expected_ordinals,
                               "observedOrdinals": observed_ordinals,
                               "declaredTotals": [total]})

    expected_count = len(manifest["sites"])
    observed_count = len(trace_records)
    accepted = not (missing or extra or duplicates or invalid or mismatches
                    or incomplete or len(grouped) != expected_count)
    result = {
        "identity": "accepted" if accepted else "rejected",
        "expectedSites": expected_count,
        "observedTraceRecords": observed_count,
        "missingSites": [_identity_descriptor(site) for site in missing.values()],
        "extraTraces": extra,
        "duplicateSiteInvocations": duplicates,
        "invalidRecords": invalid,
        "identityMismatches": mismatches,
        "incompleteInvocationOrdinals": incomplete,
        "renderAttempted": False,
    }
    if accepted:
        result["renderAttempted"] = False
    return result, grouped


# --------------------------------------------------------------------------
# Stage 1: transcribe


TRACE_PATH_RE = re.compile(r'(?P<prefix>=>trace\s+")(?P<path>[^"]+)(?P<suffix>")')


def rewrite_trace_paths(source: str, raw_dir: pathlib.Path) -> str:
    """Point generated trace clauses at this run's private raw directory."""
    def replace(match: re.Match[str]) -> str:
        basename = pathlib.PurePath(match.group("path")).name
        return (match.group("prefix") + str(raw_dir / basename)
                + match.group("suffix"))
    return TRACE_PATH_RE.sub(replace, source)


def make_trace_run(out_dir: pathlib.Path, traced_name: str
                   ) -> tuple[pathlib.Path, pathlib.Path, pathlib.Path, pathlib.Path]:
    """Create an isolated, non-colliding T4-owned trace run tree."""
    runs = out_dir / "trace-runs"
    runs.mkdir(parents=True, exist_ok=True)
    run_root = pathlib.Path(tempfile.mkdtemp(prefix=traced_name + "-", dir=runs))
    stage = run_root / "stage"
    raw = run_root / "raw"
    final = run_root / "final"
    for directory in (stage, raw, final):
        directory.mkdir()
    return run_root, stage, raw, final


def transcribe(t1: pathlib.Path, mathlib: pathlib.Path, mathlib_rel: str,
               traced_name: str, out_dir: pathlib.Path, regenerate: bool,
               log: list[str]) -> tuple[pathlib.Path, dict]:
    """Compile a staged traced copy and finalize only its run-local outputs."""
    traced = t1 / "test" / "SimpTrace" / f"{traced_name}.lean"
    if regenerate:
        raise SystemExit(
            "--regenerate would write into the T1 worktree, which this harness "
            "drives read-only; use T1's own make_traced.py there instead"
        )
    if not traced.is_file():
        raise SystemExit(f"traced copy missing: {traced}")
    manifest = traced.with_suffix(".manifest.json")
    if not manifest.is_file():
        raise SystemExit(f"traced manifest missing: {manifest}")

    run_root, stage, raw, final = make_trace_run(out_dir, traced_name)
    staged = stage / traced.name
    staged_manifest = stage / manifest.name
    shutil.copy2(traced, staged)
    shutil.copy2(manifest, staged_manifest)
    staged.write_text(rewrite_trace_paths(staged.read_text(encoding="utf-8"), raw),
                      encoding="utf-8")
    log.append(f"trace run root: {run_root}")

    code, out, err, secs = run(
        [sys.executable, "-B", "test/SimpTrace/check_transcription.py"], t1
    )
    log.append(f"check_transcription.py: exit {code} in {secs:.1f}s")
    transcription_ok = code == 0
    if not transcription_ok:
        log.append((out + err).strip()[:2000])

    # Compile only the staged source. The recorder resolves its generated
    # absolute paths beneath this run root and never touches T1's meas_out.
    compile_env = os.environ.copy()
    compile_env["SIMP_TRACE_OUT_ROOT"] = str(run_root)
    code, out, err, compile_secs = run(
        ["lake", "env", "lean", str(staged)], t1, env=compile_env
    )
    log.append(f"trace compile of {traced_name}: exit {code} in {compile_secs:.1f}s")

    finalizer = t1 / "test" / "SimpTrace" / "finalize_traces.py"
    original = mathlib / mathlib_rel[len("Mathlib/"):]
    finalize_code, finalize_out, finalize_err, finalize_secs = run(
        [sys.executable, "-B", str(finalizer),
         "--traced-source", str(staged),
         "--manifest", str(staged_manifest),
         "--source", str(original),
         "--raw-dir", str(raw),
         "--out-dir", str(final)],
        t1,
    )
    log.append(f"trace finalization: exit {finalize_code} in {finalize_secs:.1f}s")
    if finalize_code != 0:
        log.append((finalize_out + finalize_err).strip()[:2000])

    # Consume only finalizer output. Raw v1 files are intentionally never fed
    # to the identity gate; a missing final file therefore fails closed.
    trace_records: list[dict] = []
    for path in sorted(final.glob("*.json")):
        try:
            parsed = json.loads(path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            # Keep a machine-readable malformed record. Dropping it would
            # misreport a malformed trace as only a missing site.
            log.append(f"malformed trace JSON: {path.name}: {exc}")
            parsed = {"__parseError": path.name, "__parseDetail": str(exc)}
        trace_records.append(parsed)
    return staged, {
        "trace_records": trace_records,
        "transcription_ok": transcription_ok,
        "compile_exit": code,
        "compile_seconds": round(compile_secs, 2),
        "finalize_exit": finalize_code,
        "finalize_seconds": round(finalize_secs, 2),
        "run_root": str(run_root),
        "stage": str(stage),
        "raw": str(raw),
        "final": str(final),
        "classified_lines": [
            m.group(0) for m in DIAG_RE.finditer(out + err)
        ][:50],
    }


# --------------------------------------------------------------------------
# Stage 2: render


_BRANCH_TACTICS = ("by_cases", "rcases", "obtain")


def _branch_spine(source: str, site: S.Site) -> tuple[int, int, list[str], str, str | None] | None:
    """Find a small, source-preserving binary ``<;>`` branch spine.

    This intentionally handles the four shapes in the T6 design only.  It is
    a structural parser, not a tactic evaluator: if the source is multiline,
    has another operator in the spine, or has a non-binary branch producer, it
    refuses so the caller cannot guess an invocation mapping.
    """
    line_start = source.rfind("\n", 0, site.start) + 1
    line_end = source.find("\n", site.start)
    if line_end < 0:
        line_end = len(source)
    if site.start < line_start or site.end > line_end:
        return None
    line = source[line_start:line_end]
    site_col = site.start - line_start
    rel_end = site.end - line_start
    before = line[:site_col]
    suffix = line[rel_end:]
    if suffix.strip() and not suffix.lstrip().startswith("<;>"):
        return None
    suffix = suffix.strip()
    if suffix.startswith("<;>"):
        suffix = suffix[3:].strip()
        if not suffix or "<;>" in suffix:
            return None
    candidates = list(re.finditer(r"(?<![\w.])(?:by_cases|rcases|obtain)\b", before))
    for candidate in candidates:
        prefix = before[candidate.start() :]
        prior = before[:candidate.start()].strip()
        if prior not in ("", "by", ":= by") and not prior.endswith("by"):
            continue
        pieces = [part.strip() for part in prefix.split("<;>")]
        if len(pieces) < 2 or pieces[-1]:
            continue
        branches = pieces[:-1]
        if not all(part.startswith(_BRANCH_TACTICS) for part in branches):
            continue
        valid = True
        for part in branches:
            keyword = part.split(None, 1)[0]
            if keyword == "rcases":
                if not re.search(r"\bwith\b", part) or "|" not in part:
                    valid = False
                    break
            elif keyword == "obtain" and "|" not in part:
                valid = False
                break
            elif keyword == "by_cases" and not part[len(keyword):].strip():
                valid = False
                break
        if not valid:
            continue
        # Replace from the first branch producer through the complete suffix.
        inline_prefix = line[:candidate.start()].rstrip() or None
        # A tactic following ``:= by`` shares its declaration line.  Move the
        # whole line into the replacement so the required original-call
        # comment remains a standalone line rather than commenting out code.
        replace_start = line_start if inline_prefix else line_start + candidate.start()
        return replace_start, line_end, branches, suffix, inline_prefix
    return None


def _invocation_records(trace: dict | list[dict] | None) -> list[dict] | None:
    """Normalize one authenticated site to its complete ordinal list."""
    if isinstance(trace, list):
        return trace
    if not isinstance(trace, dict):
        return None
    executions = trace.get("_executions")
    if isinstance(executions, list):
        return executions
    total = trace.get("invocations", trace.get("_invocations", 1))
    if isinstance(total, int) and total == 1:
        return [trace]
    return None


def _structural_replacement(source: str, site: S.Site,
                            executions: list[dict], base_indent: str
                            ) -> tuple[list[str], tuple[int, int], int, list[str]]:
    """Render complete invocation ordinals as leaves of the source branch tree."""
    parsed = _branch_spine(source, site)
    if parsed is None:
        raise R.RenderError("structural_refused", "source has no supported binary <;> branch spine",
                            side="harness")
    start, end, branches, suffix, inline_prefix = parsed
    count = 2 ** len(branches)
    if len(executions) != count:
        raise R.RenderError(
            "structural_refused",
            f"branch spine has {count} leaves but metadata has {len(executions)} invocations",
            side="harness",
        )
    ordinals = []
    totals = set()
    for record in executions:
        if not isinstance(record, dict):
            raise R.RenderError("structural_refused", "invocation metadata is not an object",
                                side="harness")
        ordinal = record.get("invocation")
        total = record.get("invocations")
        if not isinstance(ordinal, int) or isinstance(ordinal, bool) or not isinstance(total, int):
            raise R.RenderError("structural_refused", "missing or malformed invocation metadata",
                                side="harness")
        ordinals.append(ordinal)
        totals.add(total)
    if totals != {count} or sorted(ordinals) != list(range(count)):
        raise R.RenderError("structural_refused", "invocation ordinals are not complete and unique",
                            side="harness")
    rendered: list[list[str]] = []
    for record in sorted(executions, key=lambda item: item["invocation"]):
        if R.unresolved_reason(record) is not None:
            reason = R.unresolved_reason(record) or "unknown"
            raise R.RenderError("unresolved:" + reason,
                                "an invocation is unresolved: " + reason,
                                side="t1")
        bodies, inaccessible = R.render_trace(
            record, source_text=source,
            operational=(record.get("schema") == "simp-trace-v2")
        )
        if inaccessible:
            raise R.RenderError("structural_refused", "inaccessible locals need branch-specific names",
                                side="harness")
        leaf: list[str] = []
        for body in bodies:
            leaf.append(body)
        if suffix:
            leaf.append(suffix)
        rendered.append(leaf)

    if inline_prefix:
        lines = [inline_prefix]
        base_indent = (site.line_indent or "") + "  "
    else:
        lines = S.comment_original(site.text, base_indent)
    if inline_prefix:
        lines.extend(S.comment_original(site.text, base_indent))
    lines.append(base_indent + branches[0])
    leaf_index = 0

    def emit_children(tactic_index: int) -> None:
        """Emit two children of the tactic at ``tactic_index``."""
        nonlocal leaf_index
        bullet_indent = base_indent + "  " * tactic_index
        next_index = tactic_index + 1
        for _child in (0, 1):
            if next_index < len(branches):
                lines.append(bullet_indent + "· " + branches[next_index])
                emit_children(next_index)
            else:
                for line_no, body in enumerate(rendered[leaf_index]):
                    if line_no == 0:
                        lines.append(bullet_indent + "· " + body)
                    else:
                        lines.append(bullet_indent + "  " + body)
                leaf_index += 1

    emit_children(0)
    if leaf_index != count:
        raise R.RenderError("structural_refused", "renderer emitted the wrong number of leaves",
                            side="harness")
    # The copied non-tail suffix is existing source, not generated replacement
    # code.  Keep a separate lint view so an existing `simpa` is not mistaken
    # for a newly emitted simp-family tactic.
    generated = [line for line in lines if not line.lstrip().startswith("simpa")]
    return lines, (start, end), count, generated


def render_site(site: S.Site, trace: dict | list[dict] | None,
                source: str | None = None) -> dict:
    """Render one site, returning its record.

    Four outcomes, and the record's `lines` are what gets spliced in every one:

    * no trace at all -> `render_failed:no_trace`, original call kept;
    * a classified `unresolved:` outcome -> the original call unchanged plus a
      marker comment, so the module still compiles under stock simp and the site
      is counted as unresolved rather than hidden;
    * a `RenderError` -> `render_failed:<reason>`, original call kept;
    * otherwise the rendered replacement; a complete invocation list is
      rendered as a structural branch expansion when source is supplied.
    """
    indent = " " * site.column
    record: dict = {
        "site": site.index,
        "line": site.line,
        "column": site.column,
        "original": site.text,
        "alone_on_line": site.alone_on_line,
        "long_line_waiver": False,
    }
    line_indent = site.line_indent if site.line_indent is not None else indent

    def keep_original(status: str, detail: str, side: str, extra: str = "") -> dict:
        record["status"] = status
        record["detail"] = detail
        record["attribution"] = side
        if extra:
            # A marker must remain a standalone comment even when the call is
            # mid-line (notably after `<;>`). `splice` moves the comment to the
            # enclosing line's start while retaining the original call below.
            record["lines"] = [line_indent + extra, line_indent + site.text]
        else:
            record["lines"] = [site.text]
        return record

    if trace is None:
        return keep_original(
            "render_failed:no_trace",
            "no trace JSON was produced for this site",
            "t1",
        )

    # `_invocations` is the harness aggregate for legacy per-file traces;
    # spec-v1 traces carry `invocations` (and an ordinal `invocation`) directly.
    invocations = trace.get("_invocations", trace.get("invocations")) if isinstance(trace, dict) else None
    if invocations is not None and (
        not isinstance(invocations, int) or isinstance(invocations, bool) or invocations < 1
    ):
        return keep_original(
            "render_failed:bad_invocations",
            f"the trace declares invalid invocations count {invocations!r}",
            "t1",
        )
    executions = _invocation_records(trace)
    if executions is None and invocations and invocations > 1:
        return keep_original("structurally_refused", "complete invocation records are required for structural replay",
                             "harness", "-- explicit_rw: unresolved: structurally refused: incomplete invocation records")
    if isinstance(trace, list) or (executions is not None and len(executions) > 1):
        if source is None:
            return keep_original("structurally_refused", "source is required for structural replay", "harness",
                                 "-- explicit_rw: unresolved: structurally refused: no source")
        try:
            expanded, span, count, generated = _structural_replacement(
                source, site, executions, site.line_indent or indent)
        except R.RenderError as exc:
            if exc.reason.startswith("unresolved:"):
                reason = exc.reason[len("unresolved:"):]
                return keep_original(exc.reason, exc.detail, exc.side,
                                     "-- explicit_rw: unresolved: " + reason)
            if exc.reason != "structural_refused":
                return keep_original("render_failed:" + exc.reason, exc.detail, exc.side)
            return keep_original("structurally_refused", exc.detail, exc.side,
                                 "-- explicit_rw: unresolved: structurally refused: " + exc.detail)
        record["status"] = "rendered"
        record["lines"] = expanded
        record["replace_start"], record["replace_end"] = span
        record["structural_leaf_count"] = count
        record["invocation_ordinals"] = list(range(count))
        record["lint_lines"] = generated
        return record

    reason = R.unresolved_reason(trace)
    if reason is not None:
        return keep_original(
            f"unresolved:{reason}",
            f"the recorder classified this call as unresolved: {reason}",
            "t1",
            f"-- explicit_rw: unresolved: {reason}",
        )

    try:
        bodies, inaccessible = R.render_trace(
            trace, source_text=source, operational=(trace.get("schema") == "simp-trace-v2")
        )
    except R.RenderError as exc:
        return keep_original(
            f"render_failed:{exc.reason}", exc.detail, exc.side
        )

    if not site.alone_on_line:
        # A mid-line site is spliced in place, so the render must be one line
        # with no comment and no preceding `rename_i`.
        if inaccessible:
            return keep_original(
                "render_failed:inaccessible_midline",
                "the site is mid-line (after `;`, `<;>` or inside a term), so no "
                "`rename_i` line can precede the tactic",
                "harness",
            )
        if len(bodies) > 1:
            return keep_original(
                "render_failed:multi_location_midline",
                "the site is mid-line and the trace has several locations, which "
                "need one tactic each",
                "harness",
            )
        record["status"] = "rendered"
        record["lines"] = [bodies[0]]
        return record

    lines = S.comment_original(site.text, indent)
    if inaccessible:
        # The spec: a generator derives `rename_i` names from the order of the
        # inaccessible declarations in the context. Their `ctxIndex` identifies
        # the declaration but is not itself an argument, so the names are
        # positional and generated here.
        names = [f"hx{i + 1}" for i in range(len(inaccessible))]
        lines.append(indent + "rename_i " + " ".join(names))
        record["rename_i"] = names
        # Every inaccessible reference would have to be rewritten to the new
        # name, and the renderer refused those names already; reaching here
        # means the trace named the local some other way.
        return {
            **record,
            "status": "render_failed:inaccessible_unnamed",
            "detail": (
                f"{len(inaccessible)} inaccessible local(s) need `rename_i`, but the "
                "trace's steps do not carry a nameable reference to them"
            ),
            "attribution": "t1",
            "lines": [indent + site.text],
        }

    continuation = indent + "  "
    for body in bodies:
        head, rest = body.split("[", 1)
        steps_text, tail = rest.rsplit("]", 1)
        steps = split_steps(steps_text)
        lines.extend(
            S.wrap_step_list(head + "[", steps, "]" + tail, indent, continuation)
        )
    long = S.overlong(lines)
    if long:
        # A step whose own text exceeds the budget cannot be broken: the syntax
        # admits a line break only between steps. `set_option
        # linter.style.longLine false in` before the declaration is the remedy
        # if such a line ever has to ship, but that linter is a Mathlib CI
        # option and is not enabled by `lake env lean`, so the harness reports
        # the case instead of emitting an option nothing here checks.
        record["long_line_waiver"] = True
        record["long_lines"] = long
    record["status"] = "rendered"
    record["lines"] = lines
    return record


def split_steps(text: str) -> list[str]:
    """Split a step list on its top-level commas.

    Steps nest bracketed positions, `with [...]` clauses and `congr i [...]`
    lists, so a naive split on `,` would cut inside them.
    """
    parts: list[str] = []
    depth = 0
    current = ""
    for ch in text:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(current.strip())
            current = ""
        else:
            current += ch
    if current.strip():
        parts.append(current.strip())
    return parts


# --------------------------------------------------------------------------
# Stages 3 and 4: splice and compile


def build_module(source: str, site_list: list[S.Site],
                 records: list[dict], only: int | None = None) -> str:
    """Splice the module.

    With `only` set, every site but that one is left as its original call, so a
    clean compile attributes to that one site alone.
    """
    replacements = {
        rec["site"]: rec["lines"]
        for rec in records
        if only is None or rec["site"] == only
    }
    ranges = {
        rec["site"]: (rec["replace_start"], rec["replace_end"])
        for rec in records
        if "replace_start" in rec and "replace_end" in rec
        and (only is None or rec["site"] == only)
    }
    multiline_midline = {
        rec["site"] for rec in records
        if rec.get("manual_override")
        and (only is None or rec["site"] == only)
    }
    spliced = S.splice(source, replacements, site_list, ranges, multiline_midline)
    return S.add_import(spliced)


def compile_in_t2(t2: pathlib.Path, path: pathlib.Path
                  ) -> tuple[int, list[dict], float]:
    """Compile one file in the T2 worktree and return its errors."""
    code, out, err, secs = run(["lake", "env", "lean", str(path)], t2)
    text = out + err
    matches = list(DIAG_RE.finditer(text))
    diagnostics = []
    for i, match in enumerate(matches):
        if match.group("sev") != "error":
            continue
        # The message runs to the next diagnostic header, which is where
        # `explicit_rw` prints the expected and the actual subterm.
        stop = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[match.start("msg") : stop].strip()
        diagnostics.append(
            {
                "file": match.group("file"),
                "line": int(match.group("line")),
                "column": int(match.group("col")),
                "message": match.group("msg").strip(),
                "body": " ".join(body.split())[:600],
            }
        )
    return code, diagnostics, secs


def lint_replacement(record: dict) -> list[L.Finding]:
    """Return forbidden simp-family tokens in a rendered replacement block."""
    return L.findings("\n".join(record.get("lint_lines", record.get("lines") or [])))


def replacement_line_range(source: str, site_list: list[S.Site],
                           records: list[dict], only: int) -> tuple[int, int]:
    """Return 1-based inclusive lines occupied by one isolated replacement."""
    site = site_list[only]
    lines = records[only].get("lines") or [site.text]
    start = site.line
    import_matches = list(S.IMPORT_RE.finditer(source))
    if import_matches and import_matches[-1].end() <= site.start:
        start += 1
    return start, start + len(lines) - 1


def diagnostic_for_probe(diagnostics: list[dict], probe: pathlib.Path,
                         line_start: int, line_end: int) -> dict | None:
    """Choose the first diagnostic inside this probe's replacement block."""
    probe_path = probe.resolve()
    for diagnostic in diagnostics:
        try:
            diagnostic_path = pathlib.Path(diagnostic.get("file", "")).resolve()
        except (OSError, RuntimeError):
            continue
        if diagnostic_path == probe_path and line_start <= diagnostic["line"] <= line_end:
            return diagnostic
    return None


def clear_publication(target: pathlib.Path) -> None:
    """Remove only this module's prior publication and success marker."""
    marker = target.with_suffix(target.suffix + ".success")
    for path in (target, marker):
        if path.is_dir() and not path.is_symlink():
            raise RuntimeError(f"refusing to remove publication directory: {path}")
        path.unlink(missing_ok=True)


def attribute(record: dict, message: str) -> tuple[str, str]:
    """Guess which side a compile failure belongs to, with a justification.

    * `t1` when the trace lacks a field replay needs, or the field is malformed
      (a wrong position, a side goal in the wrong frame, a name that is syntax);
    * `t2` when the rendered syntax is what the spec prescribes but the tactic
      rejects it;
    * `harness` when the render itself is wrong (bad layout, wrong splice).
    """
    low = message.lower()
    if "does not match the subterm at position" in low:
        if ("eq_true" in message or "eq_false" in message) and "Expected ∀" in message:
            return (
                "t1",
                "a `prop` step names a quantified lemma and records no `args`, so "
                "`eq_true`/`eq_false` receives the ∀ rather than an instance of it",
            )
        return (
            "t1",
            "the tactic navigated to the recorded position and the lemma does not "
            "match there, so the position or the side-goal frame is wrong",
        )
    if ("eq_true" in message or "eq_false" in message) and (
        "is expected to have type" in low
    ):
        return (
            "t1",
            "the step's `prop` flag disagrees with the statement of the fact it "
            "names, so the wrong one of eq_true/eq_false was recorded",
        )
    if "unknown identifier" in low or "unknown constant" in low:
        return (
            "t1",
            "a name the trace recorded does not resolve at the replay site",
        )
    if "unknown free variable" in low:
        return (
            "t1",
            "the trace names a local that is not in scope at the replay site",
        )
    if "expected token" in low or "unexpected token" in low or "unexpected identifier" in low:
        if record.get("long_line_waiver"):
            return ("harness", "the render broke a line where the syntax does not admit it")
        return (
            "t1",
            "a trace field was spliced as syntax the tactic's grammar does not admit",
        )
    if "was applied where the head constant is" in low:
        return (
            "t1",
            "the recorded position does not hold the constant the step unfolds, so "
            "the position is wrong",
        )
    if "explicit_rw:" in low and "not implemented" in low:
        return ("t2", "the tactic recognises the step kind but does not implement it")
    if "function expected" in low or "application type mismatch" in low:
        return (
            "t1",
            "the recorded name and args do not apply as written, so one of the two "
            "fields carries the other's content",
        )
    if "explicit_rw:" in low:
        return (
            "t2",
            "the rendered step is spec-conformant and the tactic rejected it",
        )
    if low.startswith("the rfl tactic") or "rfl" in low and "failed" in low:
        return ("t1", "the recorded close does not discharge the goal the trace left")
    return (
        "harness",
        "the error is not an explicit_rw diagnostic, so the splice or the layout is "
        "the first thing to suspect",
    )


# --------------------------------------------------------------------------
# Driver


def replay_module(mathlib_rel: str, t1: pathlib.Path, t2: pathlib.Path,
                  out_dir: pathlib.Path, mathlib: pathlib.Path,
                  per_site_limit: int | None = None) -> dict:
    started = time.monotonic()
    traced_name = MODULES.get(mathlib_rel)
    if traced_name is None:
        raise SystemExit(f"no traced copy is known for {mathlib_rel}")
    target = out_dir / mathlib_rel
    # Clear a stale publication before any current run can fail. Only this
    # module's exact file and its tied marker are in scope.
    clear_publication(target)
    source_rel = mathlib_rel[len("Mathlib/") :]
    source_path = mathlib / source_rel
    # Decode the source bytes without changing character coordinates.
    source = source_path.read_bytes().decode("utf-8")

    log: list[str] = []
    site_list = S.find_sites(source)
    _, transcription = transcribe(t1, mathlib, mathlib_rel, traced_name,
                                  out_dir, False, log)
    identity, authenticated = validate_identity(
        mathlib_rel, source, site_list, transcription["trace_records"],
    )
    if identity["identity"] == "rejected":
        # Produce one diagnostic record per expected source site, but do not
        # render, splice, compile, or claim replay for any of them.
        records = [
            {
                "site": site.index, "line": site.line, "column": site.column,
                "original": site.text, "alone_on_line": site.alone_on_line,
                "status": "identity_failed", "attribution": "harness",
                "detail": "authenticated trace identity rejected",
            }
            for site in site_list
        ]
        return {
            "module": mathlib_rel, "traced_module": traced_name,
            "sites": len(site_list), "compile_mode": "identity_failed",
            "whole_module_exit": None, "whole_module_errors": [],
            "whole_module_seconds": 0, "transcription": {
                k: v for k, v in transcription.items() if k != "trace_records"
            },
            "trace_count": len(transcription["trace_records"]),
            "identity": identity, "published": False,
            "records": records, "log": log,
            "seconds": round(time.monotonic() - started, 2),
        }
    traces: dict[int, dict | list[dict]] = {}
    for ordinal, executions in authenticated.items():
        executions.sort(key=lambda record: record["invocation"])
        traces[ordinal] = (dict(executions[0]) if len(executions) == 1
                           else [dict(record) for record in executions])
    identity["renderAttempted"] = True
    manual_by_site = manual_overrides_for_sites(mathlib_rel, source, site_list)
    records = [
        render_manual_override(site, manual_by_site[site.index], source)
        if site.index in manual_by_site else render_site(site, traces.get(site.index), source)
        for site in site_list
    ]
    for rec in records:
        findings = lint_replacement(rec)
        if findings and rec["status"] == "rendered":
            rec["status"] = "render_failed:simp_family_lint"
            rec["attribution"] = "harness"
            rec["detail"] = "replacement contains forbidden simp-family token(s): " + "; ".join(
                finding.describe() for finding in findings
            )

    run_root = pathlib.Path(transcription["run_root"])
    translated_root = run_root / "translated"
    translated_target = translated_root / mathlib_rel
    translated_target.parent.mkdir(parents=True, exist_ok=True)
    translated_target.write_text(build_module(source, site_list, records),
                                 encoding="utf-8")

    code, diagnostics, compile_secs = compile_in_t2(t2, translated_target)
    compile_mode = "whole_module"

    if code == 0:
        for rec in records:
            if rec["status"] == "rendered":
                rec["status"] = "replayed"
                rec["attribution"] = ""
                rec["detail"] = ""
    else:
        # The module did not compile clean, so no site can be called replayed on
        # its strength. Retry each rendered site alone.
        compile_mode = "per_site"
        rendered = [r for r in records if r["status"] == "rendered"]
        if per_site_limit is not None:
            rendered = rendered[:per_site_limit]
        for rec in rendered:
            probe = translated_root / "per_site" / f"{traced_name}_{rec['site'] + 1:02}"
            probe = probe.with_suffix(".lean")
            probe.parent.mkdir(parents=True, exist_ok=True)
            probe.write_text(
                build_module(source, site_list, records, only=rec["site"]),
                encoding="utf-8",
            )
            pcode, pdiags, psecs = compile_in_t2(t2, probe)
            rec["compile_seconds"] = round(psecs, 2)
            if pcode == 0:
                rec["status"] = "replayed"
                rec["attribution"] = ""
                rec["detail"] = ""
            else:
                line_start, line_end = replacement_line_range(
                    source, site_list, records, rec["site"]
                )
                diagnostic = diagnostic_for_probe(pdiags, probe, line_start, line_end)
                rec["probe_line_start"] = line_start
                rec["probe_line_end"] = line_end
                if diagnostic is None:
                    rec["status"] = "probe_inconclusive"
                    rec["attribution"] = "harness"
                    rec["detail"] = (
                        "isolated probe failed without a diagnostic inside its "
                        f"replacement block (lines {line_start}-{line_end})"
                    )
                else:
                    rec["status"] = "compile_failed"
                    rec["error"] = diagnostic["message"]
                    rec["error_body"] = diagnostic.get("body", "")
                    rec["error_line"] = diagnostic["line"]
                    rec["attribution"], rec["detail"] = attribute(
                        rec, rec.get("error_body") or rec["error"]
                    )

    for rec in records:
        rec.pop("lines", None)

    published = False
    if code == 0 and all(rec["status"] == "replayed" for rec in records):
        target.parent.mkdir(parents=True, exist_ok=True)
        os.replace(translated_target, target)
        published = True

    return {
        "module": mathlib_rel,
        "traced_module": traced_name,
        "sites": len(site_list),
        "compile_mode": compile_mode,
        "whole_module_exit": code,
        "whole_module_errors": diagnostics[:20],
        "whole_module_seconds": round(compile_secs, 2),
        "transcription": {
            k: v for k, v in transcription.items() if k != "trace_records"
        },
        "trace_count": len(traces),
        "published": published,
        "identity": identity,
        "records": records,
        "log": log,
        "seconds": round(time.monotonic() - started, 2),
    }


STATUS_ORDER = (
    "replayed", "unresolved", "render_failed", "structurally_refused",
    "compile_failed", "probe_inconclusive", "identity_failed", "other",
)


def bucket(status: str) -> str:
    for prefix in STATUS_ORDER:
        if status == prefix or status.startswith(prefix + ":"):
            return prefix
    return "other"


def summarize(report: dict) -> str:
    lines = [
        "# End-to-end replay summary",
        "",
        f"Generated {report['generated']}.",
        f"T1 `{report['t1_branch']}` at `{report['t1_commit']}`"
        f"{' (dirty)' if report['t1_dirty'] else ''}; "
        f"T2 `{report['t2_branch']}` at `{report['t2_commit']}`"
        f"{' (dirty)' if report['t2_dirty'] else ''}.",
        "",
        "| module | sites | replayed | unresolved | render_failed | structurally_refused | compile_failed | probe_inconclusive | identity_failed | other | mode | s |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    totals = {k: 0 for k in STATUS_ORDER}
    total_sites = 0
    for mod in report["modules"]:
        counts = {k: 0 for k in STATUS_ORDER}
        for rec in mod["records"]:
            counts[bucket(rec["status"])] = counts.get(bucket(rec["status"]), 0) + 1
        for k in STATUS_ORDER:
            totals[k] += counts[k]
        total_sites += mod["sites"]
        name = mod["module"][len("Mathlib/") :]
        lines.append(
            f"| `{name}` | {mod['sites']} | {counts['replayed']} | "
            f"{counts['unresolved']} | {counts['render_failed']} | "
            f"{counts['structurally_refused']} | "
            f"{counts['compile_failed']} | {counts['probe_inconclusive']} | "
            f"{counts['identity_failed']} | {counts['other']} | "
            f"{mod['compile_mode']} | {mod['seconds']:.0f} |"
        )
    lines.append(
        f"| **total** | **{total_sites}** | **{totals['replayed']}** | "
        f"**{totals['unresolved']}** | **{totals['render_failed']}** | "
        f"**{totals['structurally_refused']}** | "
        f"**{totals['compile_failed']}** | **{totals['probe_inconclusive']}** | "
        f"**{totals['identity_failed']}** | **{totals['other']}** | | |"
    )

    lines += ["", "## Failures, per site", ""]
    lines.append("| module | site | line | status | attribution | detail |")
    lines.append("| --- | --- | --- | --- | --- | --- |")
    for mod in report["modules"]:
        name = mod["module"][len("Mathlib/") :]
        for rec in mod["records"]:
            if rec["status"] == "replayed":
                continue
            detail = (rec.get("error") or rec.get("detail") or "").replace("|", "\\|")
            detail = " ".join(detail.split())[:150]
            lines.append(
                f"| `{name}` | {rec['site'] + 1} | {rec['line']} | "
                f"`{rec['status']}` | {rec.get('attribution') or '-'} | {detail} |"
            )

    attribution: dict[str, int] = {}
    for mod in report["modules"]:
        for rec in mod["records"]:
            if rec["status"] == "replayed":
                continue
            key = rec.get("attribution") or "-"
            attribution[key] = attribution.get(key, 0) + 1
    lines += ["", "## Attribution of non-replayed sites", ""]
    for key in sorted(attribution):
        lines.append(f"- `{key}`: {attribution[key]}")

    waivers = [
        (mod["module"], rec["site"] + 1, rec.get("long_lines"))
        for mod in report["modules"]
        for rec in mod["records"]
        if rec.get("long_line_waiver")
    ]
    lines += ["", "## Lines over 100 characters that could not be broken", ""]
    lines.append("(none)" if not waivers else "")
    for module, site, long in waivers:
        lines.append(f"- `{module}` site {site}: {len(long or [])} line(s)")
    lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", action="append", required=True,
                        help="Mathlib path, e.g. Mathlib/Logic/IsEmpty/Basic.lean; "
                             "repeat for several, or pass `all`")
    parser.add_argument("--t1", required=True, type=pathlib.Path)
    parser.add_argument("--t2", required=True, type=pathlib.Path)
    parser.add_argument("--out", required=True, type=pathlib.Path)
    parser.add_argument("--per-site-limit", type=int, default=None,
                        help="cap the per-site retries (for quick runs)")
    args = parser.parse_args(argv)

    t1, t2, out_dir = args.t1.resolve(), args.t2.resolve(), args.out.resolve()
    for worktree in (t1, t2):
        if not (worktree / ".git").exists():
            raise SystemExit(f"not a worktree: {worktree}")
    if out_dir.is_relative_to(t1) or out_dir.is_relative_to(t2):
        raise SystemExit("--out must not be inside the T1 or T2 worktree")

    mathlib = (t1 / ".lake" / "packages" / "mathlib" / "Mathlib").resolve()
    if not mathlib.is_dir():
        raise SystemExit(f"Mathlib sources not found at {mathlib}")

    modules = list(MODULES) if args.module == ["all"] else args.module

    t1_dirty_before = git_dirty(t1)
    t2_dirty_before = git_dirty(t2)

    started = time.monotonic()
    report = {
        "generated": datetime.datetime.now().isoformat(timespec="seconds"),
        "t1_worktree": str(t1),
        "t1_commit": git_hash(t1),
        "t1_branch": subprocess.run(
            ["git", "branch", "--show-current"], cwd=str(t1),
            capture_output=True, text=True).stdout.strip(),
        "t1_dirty": t1_dirty_before,
        "t2_worktree": str(t2),
        "t2_commit": git_hash(t2),
        "t2_branch": subprocess.run(
            ["git", "branch", "--show-current"], cwd=str(t2),
            capture_output=True, text=True).stdout.strip(),
        "t2_dirty": t2_dirty_before,
        "modules": [],
    }
    for mathlib_rel in modules:
        print(f"== {mathlib_rel}", flush=True)
        mod = replay_module(mathlib_rel, t1, t2, out_dir, mathlib,
                            args.per_site_limit)
        report["modules"].append(mod)
        counts: dict[str, int] = {}
        for rec in mod["records"]:
            key = bucket(rec["status"])
            counts[key] = counts.get(key, 0) + 1
        print(f"   {mod['sites']} sites, {counts}", flush=True)

    report["seconds"] = round(time.monotonic() - started, 2)
    # Compiles run in the driven worktrees; prove they stayed clean.
    report["t1_dirty_after"] = git_dirty(t1)
    report["t2_dirty_after"] = git_dirty(t2)

    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "report.json").write_text(
        json.dumps(report, indent=1, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (out_dir / "summary.md").write_text(summarize(report), encoding="utf-8")
    print(f"\nwrote {out_dir / 'report.json'} and {out_dir / 'summary.md'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
