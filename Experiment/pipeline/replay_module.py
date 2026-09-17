#!/usr/bin/env python3
"""End-to-end replay harness: trace a Mathlib module, render it, compile it.

    python3 -B Experiment/pipeline/replay_module.py \
        --module Mathlib/Logic/IsEmpty/Basic.lean \
        --t1 <T1 worktree> --t2 <T2 worktree> --out <dir>

Per module, in five stages:

1. **Transcribe.** Reuse T1's committed traced copy of the module (or, with
   `--regenerate`, produce one by running its `make_traced.py`), run T1's
   `check_transcription.py`, compile the traced copy in the T1 worktree, and
   collect one JSON trace per simp site.
2. **Render.** Translate each trace into replacement source text for its site:
   the original call preserved as a comment, a `rename_i` line when any used
   local is inaccessible, then one `explicit_rw` per location.
3. **Splice.** Write the translated module with every site replaced and
   `import ExplicitLean.ExplicitRw` added after the existing imports.
4. **Compile.** `lake env lean` the translated file in the T2 worktree, whose
   build carries `ExplicitRw`; Mathlib oleans are shared. Parse the errors by
   line and map each one back to its site.
5. **Report.** `report.json` and `summary.md`: per site a status, the error
   text and an attribution guess, plus totals, both worktrees' commit hashes,
   and runtimes.

Both driven worktrees are read-only: nothing is written into them, and the
harness fails rather than compile a file it placed there. Every output lands
under `--out`.

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
import pathlib
import re
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import render as R  # noqa: E402
import sites as S  # noqa: E402

# The six modules T1 has traced copies for: (Mathlib path, traced module name).
MODULES = {
    "Mathlib/Logic/IsEmpty/Basic.lean": "IsEmptyBasicTraced",
    "Mathlib/Logic/Nontrivial/Defs.lean": "NontrivialDefsTraced",
    "Mathlib/Logic/Function/Defs.lean": "FunctionDefsTraced",
    "Mathlib/Logic/ExistsUnique.lean": "ExistsUniqueTraced",
    "Mathlib/Logic/Function/Basic.lean": "FunctionBasicTraced",
    "Mathlib/Logic/Basic.lean": "LogicBasicTraced",
}

# `lake env lean` diagnostics: `<file>:<line>:<col>: <severity>: <message>`.
DIAG_RE = re.compile(r"^(?P<file>[^\s:][^:]*):(?P<line>\d+):(?P<col>\d+): "
                     r"(?P<sev>error|warning): (?P<msg>.*)$")

COMPILE_TIMEOUT = 30 * 60  # The coordination protocol's escalation threshold.


def run(cmd: list[str], cwd: pathlib.Path, timeout: int = COMPILE_TIMEOUT
        ) -> tuple[int, str, str, float]:
    started = time.monotonic()
    proc = subprocess.run(
        cmd, cwd=str(cwd), capture_output=True, text=True, timeout=timeout
    )
    return proc.returncode, proc.stdout, proc.stderr, time.monotonic() - started


def git_hash(worktree: pathlib.Path) -> str:
    code, out, _, _ = run(["git", "rev-parse", "HEAD"], worktree, timeout=60)
    return out.strip() if code == 0 else "unknown"


def git_dirty(worktree: pathlib.Path) -> bool:
    code, out, _, _ = run(["git", "status", "--porcelain"], worktree, timeout=60)
    return code != 0 or bool(out.strip())


# --------------------------------------------------------------------------
# Stage 1: transcribe


def transcribe(t1: pathlib.Path, mathlib_rel: str, traced_name: str,
               regenerate: bool, log: list[str]) -> tuple[pathlib.Path, dict]:
    """Ensure the traced copy exists, check it, compile it, return its traces.

    The traced copy and its JSON outputs live in the T1 worktree, which this
    harness treats as read-only: by default the committed copy and the outputs
    its compile produces under T1's own `test/SimpTrace/meas_out/` are reused.
    `--regenerate` is refused for that reason; producing a fresh copy would
    write into T1.
    """
    traced = t1 / "test" / "SimpTrace" / f"{traced_name}.lean"
    if regenerate:
        raise SystemExit(
            "--regenerate would write into the T1 worktree, which this harness "
            "drives read-only; use T1's own make_traced.py there instead"
        )
    if not traced.is_file():
        raise SystemExit(f"traced copy missing: {traced}")

    code, out, err, secs = run(
        [sys.executable, "-B", "test/SimpTrace/check_transcription.py"], t1
    )
    log.append(f"check_transcription.py: exit {code} in {secs:.1f}s")
    transcription_ok = code == 0
    if not transcription_ok:
        log.append((out + err).strip()[:2000])

    # Compile the traced copy so the recorder writes one JSON per site. The
    # outputs land where the traced copy's own `=>trace` clauses name, inside
    # T1; they are that worktree's own gitignored measurement outputs.
    code, out, err, compile_secs = run(
        ["lake", "env", "lean", str(traced.relative_to(t1))], t1
    )
    log.append(f"trace compile of {traced_name}: exit {code} in {compile_secs:.1f}s")

    traces: dict[int, dict] = {}
    meas = t1 / "test" / "SimpTrace" / "meas_out"
    for path in sorted(meas.glob(f"{traced_name}_*.json")):
        index = int(path.stem.rsplit("_", 1)[1]) - 1
        traces[index] = json.loads(path.read_text(encoding="utf-8"))
    return traced, {
        "traces": traces,
        "transcription_ok": transcription_ok,
        "compile_exit": code,
        "compile_seconds": round(compile_secs, 2),
        "classified_lines": [
            m.group(0) for m in DIAG_RE.finditer(out + err)
        ][:50],
    }


# --------------------------------------------------------------------------
# Stage 2: render


def render_site(site: S.Site, trace: dict | None) -> dict:
    """Render one site, returning its record.

    Four outcomes, and the record's `lines` are what gets spliced in every one:

    * no trace at all -> `render_failed:no_trace`, original call kept;
    * a classified `unresolved:` outcome -> the original call unchanged plus a
      marker comment, so the module still compiles under stock simp and the site
      is counted as unresolved rather than hidden;
    * a `RenderError` -> `render_failed:<reason>`, original call kept;
    * otherwise the rendered replacement.
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

    def keep_original(status: str, detail: str, side: str, extra: str = "") -> dict:
        record["status"] = status
        record["detail"] = detail
        record["attribution"] = side
        if site.alone_on_line and extra:
            record["lines"] = [indent + extra, indent + site.text]
        else:
            # Mid-line sites take no comment line; the marker would break the
            # surrounding term or tactic sequence.
            record["lines"] = [site.text]
            if extra:
                record["marker_dropped"] = True
        return record

    if trace is None:
        return keep_original(
            "render_failed:no_trace",
            "no trace JSON was produced for this site",
            "t1",
        )

    reason = R.unresolved_reason(trace)
    if reason is not None:
        return keep_original(
            f"unresolved:{reason}",
            f"the recorder classified this call as unresolved: {reason}",
            "t1",
            f"-- explicit_rw: unresolved: {reason}",
        )

    try:
        bodies, inaccessible = R.render_trace(trace)
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
    spliced = S.splice(source, replacements, site_list)
    return S.add_import(spliced)


def compile_in_t2(t2: pathlib.Path, path: pathlib.Path
                  ) -> tuple[int, list[dict], float]:
    """Compile one file in the T2 worktree and return its errors."""
    code, out, err, secs = run(["lake", "env", "lean", str(path)], t2)
    diagnostics = []
    for match in DIAG_RE.finditer(out + err):
        if match.group("sev") != "error":
            continue
        diagnostics.append(
            {
                "line": int(match.group("line")),
                "column": int(match.group("col")),
                "message": match.group("msg").strip(),
            }
        )
    # A diagnostic's message can run over several lines; attach the tail of the
    # output to the last error so the report keeps the explanation.
    return code, diagnostics, secs


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
        return (
            "t1",
            "the tactic navigated to the recorded position and the lemma does not "
            "match there, so the position or the side-goal frame is wrong",
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
    source_rel = mathlib_rel[len("Mathlib/") :]
    source_path = mathlib / source_rel
    source = source_path.read_text(encoding="utf-8")

    log: list[str] = []
    _, transcription = transcribe(t1, mathlib_rel, traced_name, False, log)
    traces = transcription["traces"]

    site_list = S.find_sites(source)
    records = [render_site(s, traces.get(s.index)) for s in site_list]

    out_dir.mkdir(parents=True, exist_ok=True)
    target = out_dir / mathlib_rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(build_module(source, site_list, records), encoding="utf-8")

    code, diagnostics, compile_secs = compile_in_t2(t2, target)
    compile_mode = "whole_module"

    # Map each error line back to a site: the site whose replacement block
    # covers that line of the translated file.
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
            probe = out_dir / "per_site" / f"{traced_name}_{rec['site'] + 1:02}"
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
                rec["status"] = "compile_failed"
                rec["error"] = pdiags[0]["message"] if pdiags else "(no diagnostic)"
                rec["error_line"] = pdiags[0]["line"] if pdiags else None
                rec["attribution"], rec["detail"] = attribute(rec, rec["error"])

    for rec in records:
        rec.pop("lines", None)

    return {
        "module": mathlib_rel,
        "traced_module": traced_name,
        "sites": len(site_list),
        "compile_mode": compile_mode,
        "whole_module_exit": code,
        "whole_module_errors": diagnostics[:20],
        "whole_module_seconds": round(compile_secs, 2),
        "transcription": {
            k: v for k, v in transcription.items() if k != "traces"
        },
        "trace_count": len(traces),
        "records": records,
        "log": log,
        "seconds": round(time.monotonic() - started, 2),
    }


STATUS_ORDER = ("replayed", "unresolved", "render_failed", "compile_failed")


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
        "| module | sites | replayed | unresolved | render_failed | compile_failed | mode | s |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
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
            f"{counts['compile_failed']} | {mod['compile_mode']} | {mod['seconds']:.0f} |"
        )
    lines.append(
        f"| **total** | **{total_sites}** | **{totals['replayed']}** | "
        f"**{totals['unresolved']}** | **{totals['render_failed']}** | "
        f"**{totals['compile_failed']}** | | |"
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
