#!/usr/bin/env python3
"""Exercise selector rendering at the grammar boundaries used by callers."""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from boundary_protocol import (
    check_recording_abort_markers,
    check_replay_abort_markers,
    parse_framed_json_lines,
    recording_subprocess_environment,
    replay_subprocess_environment,
)
import check_simp_engine_boundary_source as renderer
from process_runner import run_process


ARTIFACT_MARKER = renderer.ARTIFACT_MARKER


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = (
    ROOT.parents[1]
    / "snapshots/declaration-branch-reservation-prototype"
    / ".lake/declaration-branch-reservation-handoff/evidence/inline-first-renderer-failure"
)
FROZEN_RECORD_SOURCE = (
    EVIDENCE.parents[3]
    / ".lake/reservation-failure-controls-y5g6nuu7/stock-record/Experiment/ReservationFailure.lean"
)
FROZEN_REPLAY_SOURCE = (
    EVIDENCE.parents[3]
    / ".lake/reservation-failure-controls-y5g6nuu7/stock-replay/Experiment/ReservationFailure.lean"
)
FROZEN_REPLAY_RECEIPT = EVIDENCE / "stock-replay-invocation.json"
TIMEOUT = 300


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], *, env: dict[str, str] | None = None) -> str:
    result = run_process(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=TIMEOUT,
        check=False,
        env=env,
    )
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def compile_source(
    dylib: str, source: Path, *, env: dict[str, str] | None = None
) -> str:
    return run(
        [
            "lake",
            "env",
            "lean",
            f"--load-dynlib={dylib}",
            "-R",
            str(source.parent.parent),
            str(source),
        ],
        env=env,
    )


def query_dylib() -> str:
    return json.loads(run(["lake", "query", "ExplicitLean:shared", "--json"]).splitlines()[-1])


def continuation_indent(source: str, start: int) -> str:
    line_start = source.rfind("\n", 0, start) + 1
    return " " * (len(source[line_start:start].expandtabs(8)) + 2)


def render_into_frozen_source(
    reports: list[dict[str, object]], frozen: str, *, original: str = "simp only []"
) -> str:
    marker = "first | "
    start = frozen.index(marker) + len(marker)
    fallback = frozen.index(" | exact h", start)
    indent = continuation_indent(frozen, start)
    replacement = renderer.preserve_original_call(
        renderer.format_report_variants(reports, indent), original, indent
    )
    return frozen[:start] + replacement + frozen[fallback:]


def compile_expected_failure(dylib: str, source: Path, env: dict[str, str]) -> str:
    try:
        compile_source(dylib, source, env=env)
    except RuntimeError as error:
        output = str(error)
        if "boundary_recorded_tactic_failure" not in output:
            raise RuntimeError(f"standalone failure took the wrong path:\n{output}") from error
        if "unexpected identifier" in output or "expected string literal" in output:
            raise RuntimeError(f"standalone selector was not parsed as a unit:\n{output}") from error
        return output
    raise RuntimeError("standalone recorded failure unexpectedly succeeded")


def main() -> None:
    # Keep the old handoff evidence immutable while checking that this test is
    # pointed at the exact source and receipt that documented the failure.
    receipt = json.loads(FROZEN_REPLAY_RECEIPT.read_text(encoding="utf-8"))
    if sha256(FROZEN_REPLAY_SOURCE) != receipt["sourceSha256"]:
        raise RuntimeError("frozen inline-first source changed")
    if not FROZEN_RECORD_SOURCE.is_file() or not FROZEN_REPLAY_SOURCE.is_file():
        raise RuntimeError("frozen inline-first source is missing")
    build = run(["lake", "build", "ExplicitLean:shared"])
    dylib = query_dylib()
    runtime_hash = sha256(Path(dylib))

    with tempfile.TemporaryDirectory(prefix="inline-first-renderer-", dir=ROOT / ".lake") as raw:
        work = Path(raw)
        record_source = work / "record" / "Experiment" / FROZEN_RECORD_SOURCE.name
        replay_source = work / "replay" / "Experiment" / FROZEN_REPLAY_SOURCE.name
        standalone_source = work / "standalone" / "Experiment" / "ReservationFailure.lean"
        nested_source = work / "nested" / "Experiment" / "ReservationFailure.lean"
        record_source.parent.mkdir(parents=True)
        replay_source.parent.mkdir(parents=True)
        standalone_source.parent.mkdir(parents=True)
        nested_source.parent.mkdir(parents=True)
        record_source.write_bytes(FROZEN_RECORD_SOURCE.read_bytes())
        frozen_replay = FROZEN_REPLAY_SOURCE.read_text(encoding="utf-8")

        record_env, record_nonce = recording_subprocess_environment()
        record_output = compile_source(dylib, record_source, env=record_env)
        record_log = work / "fresh-record.log"
        record_log.write_text(record_output, encoding="utf-8")
        check_recording_abort_markers(
            record_output,
            expected_nonce=record_nonce,
            expected_module="Experiment.ReservationFailure",
        )
        reports = parse_framed_json_lines(
            record_output,
            marker=ARTIFACT_MARKER,
            expected_nonce=record_nonce,
            label="fresh boundary artifact",
        )
        if len(reports) != 1 or reports[0].get("status") != "failure":
            raise RuntimeError(f"fresh stock failure changed shape: {reports}")
        fresh_report = reports[0]

        # This is the exact frozen inline-first source layout, with only the
        # selector evidence refreshed from a new recording nonce.
        rendered = render_into_frozen_source([fresh_report], frozen_replay)
        replay_source.write_text(rendered, encoding="utf-8")
        replay_env, replay_nonce = replay_subprocess_environment()
        replay_output = compile_source(dylib, replay_source, env=replay_env)
        replay_log = work / "fresh-replay.log"
        replay_log.write_text(replay_output, encoding="utf-8")
        check_replay_abort_markers(
            replay_output,
            expected_nonce=replay_nonce,
            expected_module="Experiment.ReservationFailure",
        )

        # A second, UTF-8 caller variant exercises the selector's complete
        # branch list while the real variant remains the selected failure.
        utf8_variant = copy.deepcopy(fresh_report)
        utf8_variant["selector"] = copy.deepcopy(fresh_report["selector"])
        utf8_variant["selector"]["caller"] = "«ü».caller"
        multi = render_into_frozen_source([utf8_variant, fresh_report], frozen_replay)
        multi_source = work / "multi" / "Experiment" / "ReservationFailure.lean"
        multi_source.parent.mkdir(parents=True)
        multi_source.write_text(multi, encoding="utf-8")
        multi_env, multi_nonce = replay_subprocess_environment()
        multi_output = compile_source(dylib, multi_source, env=multi_env)
        check_replay_abort_markers(
            multi_output,
            expected_nonce=multi_nonce,
            expected_module="Experiment.ReservationFailure",
        )

        selector = renderer.format_report_variants([fresh_report], "    ")
        standalone_source.write_text(
            "module\nimport Mathlib.Algebra.BigOperators.Finprod\n"
            "import ExplicitLean.SimpEngine.Boundary.Tactic\n"
            "example (p : Prop) (h : p) : p := by\n  "
            + selector
            + "\n",
            encoding="utf-8",
        )
        standalone_env, standalone_nonce = replay_subprocess_environment()
        standalone_output = compile_expected_failure(dylib, standalone_source, standalone_env)
        check_replay_abort_markers(
            standalone_output,
            expected_nonce=standalone_nonce,
            expected_module="Experiment.ReservationFailure",
        )

        # The same grouped selector must survive another first nested under
        # `try`; the authored fallback remains responsible for closing the
        # proof after the recorded failure is caught.
        nested_selector = renderer.format_report_variants([fresh_report], "      ")
        nested_source.write_text(
            "module\nimport Mathlib.Algebra.BigOperators.Finprod\n"
            "import ExplicitLean.SimpEngine.Boundary.Tactic\n"
            "example (p : Prop) (h : p) : p := by\n"
            "  first\n  | ((try "
            + nested_selector
            + "); fail)\n  | exact h\n",
            encoding="utf-8",
        )
        nested_env, nested_nonce = replay_subprocess_environment()
        nested_output = compile_source(dylib, nested_source, env=nested_env)
        check_replay_abort_markers(
            nested_output,
            expected_nonce=nested_nonce,
            expected_module="Experiment.ReservationFailure",
        )

        # Preserve the exact authored call, including delimiters and UTF-8,
        # while changing only the replacement's grouping.
        comments = renderer.preserve_original_call(
            selector, 'simp only [show "-/" = "-/" from rfl]\n    -- café', "    "
        )
        if '    -- simp only [show "-/" = "-/" from rfl]' not in comments:
            raise RuntimeError("original UTF-8/comment provenance was not retained")

        receipt_path = work / "fresh-receipt.json"
        receipt_path.write_text(
            json.dumps(
                {
                    "recordNonce": record_nonce,
                    "replayNonce": replay_nonce,
                    "recordSourceSha256": sha256(record_source),
                    "replaySourceSha256": sha256(replay_source),
                    "runtimeSha256": runtime_hash,
                    "recordLogSha256": sha256(record_log),
                    "replayLogSha256": sha256(replay_log),
                    "command": ["lake", "env", "lean", f"--load-dynlib={dylib}"],
                },
                sort_keys=True,
            ),
            encoding="utf-8",
        )
        handoff_root = ROOT / ".lake/inline-first-renderer-handoff"
        handoff_root.mkdir(parents=True, exist_ok=True)
        handoff = handoff_root / f"run-{record_nonce}"
        shutil.copytree(work, handoff)
        print(
            "inline-first renderer: frozen source, fresh record/replay nonce logs, "
            "grouped single/multi/nested selectors and standalone failure: ok"
        )
        print(f"fresh receipt: {handoff / receipt_path.name}")


if __name__ == "__main__":
    main()
