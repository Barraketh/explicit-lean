#!/usr/bin/env python3
"""Prove caught replay errors fail acceptance without changing stock failure.

The Lean matrix writes disposable sources/logs below .lake and requires every
case to compile successfully: rejection must come from the authenticated abort
scan, not from Lean's exit status. No generated replay imports the recorder.
"""

from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import tempfile

import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import check_simp_engine_boundary_source as source


ROOT = Path(__file__).resolve().parents[1]
MODULE = "Experiment.SimpEngineReplayAbort"
OCCURRENCE = "replay-abort-test"


def expect_rejection(action, fragment: str) -> None:
    try:
        action()
    except RuntimeError as error:
        if fragment not in str(error):
            raise RuntimeError(f"expected {fragment!r}, got {error}") from error
    else:
        raise RuntimeError(f"expected rejection containing {fragment!r}")


def protocol_checks() -> None:
    nonce = protocol.fresh_run_nonce()
    payload = {
        "kind": protocol.REPLAY_ABORT_KIND, "schema": 1,
        "occurrence": OCCURRENCE, "module": MODULE,
        "stage": "apply", "detail": "boundary_recorded_tactic_failure",
    }
    prefix = protocol.marker_prefix(protocol.REPLAY_ABORT_MARKER, nonce)
    valid = prefix + json.dumps(payload) + "\n"
    check = lambda output: protocol.check_replay_abort_markers(
        output, expected_nonce=nonce, expected_occurrence=OCCURRENCE,
        expected_module=MODULE,
    )
    check("ordinary diagnostic: " + valid)
    expect_rejection(lambda: check(valid), "boundary replay abort")
    for line, fragment in (
        (protocol.REPLAY_ABORT_MARKER + "wrong {}", "wrong nonce"),
        (prefix, "empty JSON"),
        (prefix + "{", "invalid boundary replay-abort"),
        (prefix + "{}", "marker fields"),
        (prefix + json.dumps(payload | {"schema": True}), "marker schema"),
        (prefix + json.dumps(payload | {"kind": "wrong"}), "marker kind"),
        (prefix + json.dumps(payload | {"occurrence": "wrong"}), "occurrence mismatch"),
        (prefix + json.dumps(payload | {"module": "wrong"}), "module mismatch"),
        (prefix + json.dumps(payload | {"detail": ""}), "nonempty string"),
    ):
        expect_rejection(lambda: check(line), fragment)
    # An earlier valid abort does not hide a later malformed event.
    expect_rejection(lambda: check(valid + prefix + "{}"), "marker fields")
    print("replay abort protocol: authenticated framing and complete scan: ok", flush=True)


def fixture(tactic: str, *, failure: bool = False, recording: bool = False,
            catcher: str = "first") -> str:
    imported = "ExplicitLean.SimpEngine.Boundary" + ("" if recording else ".Tactic")
    declaration = "(P : Prop) (h : P) : P" if failure else ": True"
    fallback = "exact h" if failure else "exact True.intro"
    if catcher == "first":
        body = f"  first\n  | {tactic}\n  | {fallback}\n"
    else:
        body = f"  {catcher} ({tactic})\n  {fallback}\n"
    return (
        f"module\nimport Lean\nimport {imported}\n\n"
        f"theorem replayGuardFixture {declaration} := by\n" + body
    )


def write_fixture(work: Path, case: str, text: str) -> Path:
    path = work / case / "Experiment" / "SimpEngineReplayAbort.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def record(work: Path, dylib: str, *, failure: bool = False) -> dict:
    path = write_fixture(
        work, "record-failure" if failure else "record-success",
        fixture(f'simp_engine_boundary_record "{OCCURRENCE}"' +
                (" only []" if failure else ""), failure=failure, recording=True),
    )
    output, nonce = source.compile_recording_source(dylib, path)
    path.with_suffix(".log").write_text(output, encoding="utf-8")
    protocol.check_recording_abort_markers(
        output, expected_nonce=nonce, expected_module=MODULE,
    )
    reports = protocol.parse_framed_json_lines(
        output, marker=materializer.ARTIFACT_MARKER,
        expected_nonce=nonce, label="boundary artifact",
    )
    if len(reports) != 1 or reports[0]["status"] != ("failure" if failure else "success"):
        raise RuntimeError(f"unexpected stock recording: {reports}")
    protocol.validate_report(reports[0], OCCURRENCE, MODULE)
    path.with_suffix(".artifact.json").write_text(json.dumps(reports[0], indent=2) + "\n")
    return reports[0]


def select(report: dict, *, outcome: str | None = None, duplicate: bool = False) -> str:
    branch = (
        f'      | "{OCCURRENCE}" {source.format_selector_values(report)} => '
        + (outcome if outcome is not None else source.format_variant_outcome(report, "        "))
    )
    return ("simp_engine_boundary_select " + source.format_artifact_header(report)
            + "\n" + branch + ("\n" + branch if duplicate else ""))


def lean_matrix(work: Path, dylib: str) -> None:
    success = record(work, dylib)
    failure = record(work, dylib, failure=True)
    missing = copy.deepcopy(success)
    missing["selector"]["preState"]["targetFingerprint"] = "unrecorded-target"
    encoded_true = json.dumps(["expr_dag_v1", [["c", [["s", "True"]], []]], 0])
    encoded_false = json.dumps(["expr_dag_v1", [["c", [["s", "False"]], []]], 0])
    encoded_nat_zero = json.dumps(["expr_dag_v1", [["c", [["s", "Nat"], ["s", "zero"]], []]], 0])
    q = source.lean_string
    same = f"({q(encoded_true)} ==> {q(encoded_true)})"
    cases = [
        ("valid-replay", select(success), False, "first", None),
        ("recorded-failure", select(failure), True, "first", None),
        ("missing", select(missing), False, "first", "boundary_variant_missing"),
        ("ambiguous", select(success, duplicate=True), False, "first", "ambiguous_boundary_variant"),
        ("invalid-header", select(success).replace("artifact_schema := 2", "artifact_schema := 999"),
         False, "first", "unsupported_boundary_artifact_schema"),
        ("invalid-dag", select(success, outcome=f'apply_encoded ("not-json" ==> {q(encoded_true)})'),
         False, "first", "boundary_expr_decode_error"),
        ("invalid-proof", select(success, outcome=f"apply_encoded ({q(encoded_true)} ==> {q(encoded_true)} using {q(encoded_nat_zero)})"),
         False, "first", "boundary_expr_proof_type_mismatch"),
        ("invalid-action", select(success, outcome=f'apply_encoded_with_actions [declare_equation "not-json" "bad"] {same}'),
         False, "first", "invalid encoded declaration name"),
        ("invalid-application", select(success, outcome=f"apply_encoded ({q(encoded_false)} ==> {q(encoded_false)})"),
         False, "first", "boundary_target_input_mismatch"),
        ("unobserved", "simp_engine_boundary_occurrence_unobserved", False, "first", "boundary_occurrence_unobserved"),
        ("try-missing", "simp_engine_boundary_variant_missing", False, "try", "boundary_variant_missing"),
        ("repeat-missing", "simp_engine_boundary_variant_missing", False, "repeat", "boundary_variant_missing"),
        ("spoofed-stock-failure", 'simp_engine_boundary_apply (True ==> True using by fail "boundary_recorded_tactic_failure")',
         False, "first", "boundary_recorded_tactic_failure"),
        ("partial-output", 'run_tac IO.print "partial-output"\n    simp_engine_boundary_variant_missing',
         False, "first", "boundary_variant_missing"),
    ]
    evidence = []
    for name, tactic, expected_failure, catcher, error_fragment in cases:
        path = write_fixture(work, name, fixture(tactic, failure=expected_failure, catcher=catcher))
        environment, nonce = protocol.replay_subprocess_environment()
        # compile_source raises on nonzero: every negative must be caught by Lean.
        output = source.compile_source(dylib, path, env=environment)
        if name == "partial-output" and "partial-output\nSIMP_ENGINE_BOUNDARY_REPLAY_ABORT " not in output:
            raise RuntimeError("replay abort was not framed after partial output\n" + output)
        log = path.with_suffix(".log")
        log.write_text(output, encoding="utf-8")
        scan = lambda: protocol.check_replay_abort_markers(
            output, expected_nonce=nonce, expected_module=MODULE,
        )
        if error_fragment is None:
            scan()
        else:
            events = protocol.parse_framed_json_lines(
                output, marker=protocol.REPLAY_ABORT_MARKER,
                expected_nonce=nonce, label="boundary replay-abort",
            )
            if len(events) != 1 or error_fragment not in events[0]["detail"]:
                raise RuntimeError(f"{name}: expected one {error_fragment} abort, found {events}")
            expect_rejection(scan, "boundary replay abort")
        evidence.append({
            "case": name, "compilerExit": 0, "accepted": error_fragment is None,
            "nonce": nonce, "source": str(path),
            "sourceSha256": materializer.sha256(path.read_bytes()),
            "log": str(log), "logSha256": materializer.sha256(log.read_bytes()),
        })
        print(f"replay abort Lean matrix: {name}: ok", flush=True)
    (work / "matrix.json").write_text(json.dumps(evidence, indent=2) + "\n")


def oracle_checks(work: Path, dylib: str) -> None:
    original = write_fixture(work, "oracle-original", fixture("simp"))
    positive_root = work / "oracle-valid"
    positive_root.mkdir()
    positive = materializer.run_declaration_oracle(
        "Experiment/SimpEngineReplayAbort.lean", original, original,
        positive_root, dylib, 300,
    )
    materializer._validate_oracle_wrapper(positive, "oracle fixture", MODULE)
    (positive_root / "wrapper.json").write_text(json.dumps(positive, indent=2) + "\n")
    negative_root = work / "oracle-caught"
    negative_root.mkdir()
    (negative_root / "declaration-oracle-report.json").write_text(
        json.dumps(positive["report"]) + "\n"
    )
    applied = write_fixture(work, "oracle-applied", fixture("simp_engine_boundary_occurrence_unobserved"))
    expect_rejection(
        lambda: materializer.run_declaration_oracle(
            "Experiment/SimpEngineReplayAbort.lean", original, applied,
            negative_root, dylib, 300,
        ),
        "boundary replay abort",
    )
    log = (negative_root / "declaration-oracle.log").read_text()
    oracle = materializer._parse_declaration_oracle(log, MODULE)
    if oracle["status"] != "success":
        raise RuntimeError("oracle negative must pass declaration comparison before guard rejection")
    if (negative_root / "declaration-oracle-report.json").exists():
        raise RuntimeError("aborted oracle published an acceptable oracle report")
    print("replay abort oracle: ordinary success accepted; caught replay error rejected despite oracle success: ok", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--protocol-only", action="store_true")
    args = parser.parse_args()
    protocol_checks()
    if args.protocol_only:
        return
    dylib = source.query_json_string(
        source.run(["lake", "query", "ExplicitLean:shared", "--json"]), "shared query"
    )
    parent = ROOT / ".lake" / "week-2026-08-31" / "replay-abort"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="matrix-", dir=parent))
    print(f"replay abort evidence: {work}", flush=True)
    lean_matrix(work, dylib)
    oracle_checks(work, dylib)


if __name__ == "__main__":
    main()
