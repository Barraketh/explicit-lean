#!/usr/bin/env python3
"""Record/replay controls for an imported realization with two local helpers.

The fixture deliberately exercises the mixed sequence contract.  The Python
wire validator is expected to enforce the same helper ordering and snapshots;
this control does not claim module or campaign coverage.
"""
from pathlib import Path
import copy
import hashlib
import json
import tempfile

import boundary_protocol as protocol
import boundary_expr_codec as wire
import boundary_materialize_shard as materializer
import check_simp_engine_boundary_source as source
import check_simp_engine_mixed_sequence as mixed

ROOT = Path(__file__).resolve().parents[1]
MODULE = "Mathlib.Control.Basic"
OCCURRENCE = "target"
SOURCE_ORIGINAL = "simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind]"
SIMP_CALL = f'simp_engine_boundary_record "{OCCURRENCE}" (disch := make_two_helpers) only [joinM, imported_multi_helper_rule p, id, ← bind_pure_comp, bind_assoc, pure_bind, and_true]'

CONDITIONAL_RULE = '''
public inductive ReviewBox : Prop where
  | intro : ReviewBox

public inductive MultiHelperMarkerA : Prop where
  | intro : MultiHelperMarkerA

public inductive MultiHelperMarkerB : Prop where
  | intro : MultiHelperMarkerB

public theorem imported_multi_helper_rule (p : Prop) (h : p) : ReviewBox ↔ True := by
  constructor
  · intro _
    exact True.intro
  · intro _
    exact ReviewBox.intro
'''


def replace_once(text, old, new, label):
    if text.count(old) != 1:
        raise RuntimeError(f"{label}: expected exactly one replacement target")
    return text.replace(old, new, 1)

HELPER = '''
open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary

elab "make_two_helpers" : tactic => withMainContext do
  let firstType := mkConst ``MultiHelperMarkerA
  let firstValue := mkConst ``MultiHelperMarkerA.intro
  let first ← withExporting (isExporting := false) <|
    mkAuxLemma [] firstType firstValue
  let secondType := mkConst ``MultiHelperMarkerB
  let secondValue := mkConst ``MultiHelperMarkerB.intro
  let type := mkApp2 (mkConst ``And) firstType secondType
  let value := mkApp4 (mkConst ``And.intro) firstType secondType
    firstValue secondValue
  discard <| withExporting (isExporting := false) <| mkAuxLemma [] type value
  IO.println "TWO_HELPERS_STOCK"
  evalTactic (← `(tactic| assumption))
'''


def main():
    parent = ROOT / ".lake/imported-multi-helpers"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="controls-", dir=parent))
    print(work, flush=True)
    dylib = source.query_json_string(source.run(["lake", "query", "ExplicitLean:shared", "--json"]), "shared")
    records = []

    def compile_case(label, text, *, recording=False, expected=None):
        path = materializer._copy_at_module_root(
            work / label, "Mathlib/Control/Basic.lean", text.encode("utf-8")
        )
        env, nonce = (protocol.recording_subprocess_environment() if recording else
                      protocol.replay_subprocess_environment())
        code, output, elapsed = materializer._compile_copy(
            path, dylib, 360, env=env
        )
        if expected is None and code != 0:
            raise RuntimeError(f"{label}: compiler exited {code}\n{output}")
        if expected is not None and code not in (0, 1):
            raise RuntimeError(f"{label}: compiler exited unexpected {code}\n{output}")
        log = path.with_suffix(".log")
        log.write_text(output)
        checker = protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers
        failure = None
        try:
            checker(output, expected_nonce=nonce, expected_module=MODULE,
                    expected_occurrence=OCCURRENCE)
        except RuntimeError as error:
            failure = str(error)
        if expected is None:
            if failure is not None:
                raise RuntimeError(f"{label}: {failure}")
        elif failure is None or expected not in failure:
            raise RuntimeError(f"{label}: expected {expected!r}, got {failure!r}")
        if recording and "TWO_HELPERS_STOCK" not in output:
            raise RuntimeError(f"{label}: discharger marker was not emitted")
        if not recording and "TWO_HELPERS_STOCK" in output:
            raise RuntimeError(f"{label}: replay reran the stock discharger")
        reports = protocol.parse_framed_json_lines(output, marker=source.ARTIFACT_MARKER,
            expected_nonce=nonce, label="imported multi-helper artifact")
        if expected is not None and reports:
            raise RuntimeError(f"{label}: rejected run emitted an artifact")
        records.append({"label": label, "recording": recording, "nonce": nonce,
                        "source": str(path),
                        "sourceSha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                        "log": str(log),
                        "logSha256": hashlib.sha256(log.read_bytes()).hexdigest(),
                        "compilerExit": code,
                        "elapsedSeconds": elapsed,
                        "expectedAbort": expected})
        print(f"imported multi-helper: {label}: passed", flush=True)
        return reports

    base, _ = mixed.source_text("control")
    target = "theorem joinM_map_joinM {α : Type u} (a : m (m (m α))) : joinM (joinM <$> a) = joinM (joinM a) := by"
    target_with_context = "theorem joinM_map_joinM {α : Type u} (a : m (m (m α))) (p : Prop) (hp : p) : joinM (joinM <$> a) = joinM (joinM a) := by"
    replacement = target_with_context.replace(" := by", " ∧ ReviewBox := by")
    if base.count(target) != 1:
        raise RuntimeError("control fixture target theorem shape changed")
    base = replace_once(base, target, target_with_context, "target theorem context")
    base = replace_once(base, target_with_context, replacement, "target theorem conjunction")
    recorded = replace_once(base,
        "import all Lean.OriginalConstKind\n",
        "import all Lean.OriginalConstKind\n" + CONDITIONAL_RULE + "\n" + HELPER,
        "conditional and helper declaration insertion")
    recorded = replace_once(recorded,
            'observe_mixed_sequence "target" ' + SOURCE_ORIGINAL,
            'observe_mixed_sequence "target" ' + SIMP_CALL,
            "conditional discharger call")
    reports = compile_case("record", recorded, recording=True)
    if len(reports) != 1:
        raise RuntimeError(f"expected one artifact, got {len(reports)}")
    report = protocol.validate_report(reports[0], OCCURRENCE, MODULE)
    action = report["environmentActions"]
    if len(action) != 1 or action[0]["kind"] != "realize_groups":
        raise RuntimeError("mixed imported realization was not captured as one realize_groups action")
    payload = json.loads(action[0]["declaration"])
    if payload[0] != "boundary_realization_sequence_v1":
        raise RuntimeError("fixture did not select the mixed realization sequence")
    helpers = [step for step in payload[12] if step[0] == "helper"]
    if len(helpers) < 2:
        raise RuntimeError(f"expected at least two helper steps, got {len(helpers)}")
    # The discharger deliberately creates a marker-A singleton and an
    # And(marker-A, marker-B) singleton.  Simp may add other helpers while
    # proving the conditional rule; retain and validate those too.
    def has_marker(step, marker):
        return marker in step[2]

    marker_a_only = [step for step in helpers
                     if has_marker(step, "MultiHelperMarkerA")
                     and not has_marker(step, "MultiHelperMarkerB")]
    marker_a_b = [step for step in helpers
                  if has_marker(step, "MultiHelperMarkerA")
                  and has_marker(step, "MultiHelperMarkerB")]
    if not marker_a_only or not marker_a_b:
        raise RuntimeError("deliberate marker-A and marker-A/B helper proofs were not captured")
    deliberate_helpers = [marker_a_only[0], marker_a_b[0]]
    registration_indices = [i for i, step in enumerate(payload[12]) if step[0] == "registration"]
    if not registration_indices:
        raise RuntimeError("fixture did not emit an authenticated imported registration")
    (work / "recorded-report.json").write_text(json.dumps(report, indent=2) + "\n")

    rendered = source.format_report_variants([report], "    ")
    applied = replace_once(recorded, "public meta import ExplicitLean.SimpEngine.Boundary\n",
        "public meta import ExplicitLean.SimpEngine.Boundary.Tactic\n",
        "replay tactic import")
    applied = replace_once(applied, SIMP_CALL, rendered, "replay artifact replacement")
    compile_case("replay", applied)

    # Exercise the authenticated registration gap independently of Lean replay:
    # the first helper snapshot omits a real registration, the second observes
    # it, and the registration is placed between those helpers. Then exercise
    # trailing, early, nonmonotone and owner-mismatch failures.
    registration_index = registration_indices[0]
    registration = payload[12][registration_index]
    registration_wire = json.loads(registration[2])
    registration_name = registration[1]
    registration_owner = registration_wire[1]
    helper_names = [step[1] for step in helpers]
    deliberate_names = [step[1] for step in deliberate_helpers]
    synthetic = copy.deepcopy(payload)
    steps = [step for step in synthetic[12] if step[0] != "registration"]
    second_index = next(i for i, step in enumerate(steps)
                        if step[0] == "helper" and step[1] == deliberate_names[1])
    # Every helper before the deliberate second helper must omit the mapping;
    # every helper from that point onward observes it.  This keeps any
    # incidental simp-generated helper accounted for in the monotone sequence.
    for index, step in enumerate(steps):
        if step[0] == "helper":
            step[4] = [entry for entry in step[4] if entry[0] != registration_name]
            if index >= second_index:
                step[4].append([registration_name, registration_owner])
    steps.insert(second_index, copy.deepcopy(registration))
    synthetic[12] = steps
    wire.validate_realization_payload(json.dumps(synthetic, separators=(",", ":")),
        action[0]["nameParts"], "synthetic-registration-gap")

    trailing = copy.deepcopy(synthetic)
    trailing[12].remove(next(step for step in trailing[12] if step[0] == "registration"))
    trailing[12].append(copy.deepcopy(registration))
    for step in trailing[12]:
        if step[0] == "helper":
            step[4] = [entry for entry in step[4] if entry[0] != registration_name]
    wire.validate_realization_payload(json.dumps(trailing, separators=(",", ":")),
        action[0]["nameParts"], "synthetic-trailing-registration")

    def expect_wire_reject(label, value, detail):
        try:
            wire.validate_realization_payload(json.dumps(value, separators=(",", ":")),
                action[0]["nameParts"], label)
        except RuntimeError as error:
            if detail not in str(error):
                raise RuntimeError(f"{label}: wrong rejection: {error}")
        else:
            raise RuntimeError(f"{label}: malformed payload was accepted")

    early = copy.deepcopy(synthetic)
    reg_step = next(step for step in early[12] if step[0] == "registration")
    early[12].remove(reg_step)
    early[12].insert(next(i for i, step in enumerate(early[12]) if step[0] == "helper"), reg_step)
    expect_wire_reject("registration-before-unobserving-helper", early, "registration order mismatch")

    nonmonotone = copy.deepcopy(synthetic)
    first = next(step for step in nonmonotone[12]
                 if step[0] == "helper" and step[1] == deliberate_names[0])
    second = next(step for step in nonmonotone[12]
                  if step[0] == "helper" and step[1] == deliberate_names[1])
    first[4].append([registration_name, registration_owner])
    second[4] = [entry for entry in second[4] if entry[0] != registration_name]
    reg_step = next(step for step in nonmonotone[12] if step[0] == "registration")
    nonmonotone[12].remove(reg_step)
    nonmonotone[12].insert(next(i for i, step in enumerate(nonmonotone[12]) if step[0] == "helper"), reg_step)
    expect_wire_reject("nonmonotone-helper-snapshots", nonmonotone, "nonmonotone helper equation snapshots")

    wrong_owner = copy.deepcopy(synthetic)
    second = next(step for step in wrong_owner[12]
                  if step[0] == "helper" and step[1] == deliberate_names[1])
    second[4] = [[entry[0], [["s", "Nat"]]] if entry[0] == registration_name else entry
                 for entry in second[4]]
    expect_wire_reject("helper-snapshot-owner-mismatch", wrong_owner,
                       "helper equation snapshot owner mismatch")
    structural_wire_checks = [
        "synthetic-registration-gap",
        "synthetic-trailing-registration",
        "registration-before-unobserving-helper",
        "nonmonotone-helper-snapshots",
        "helper-snapshot-owner-mismatch",
    ]

    def render_payload(value):
        old = source.lean_string(action[0]["declaration"])
        new = source.lean_string(json.dumps(value, separators=(",", ":")))
        if applied.count(old) != 1:
            raise RuntimeError("render source does not contain the recorded declaration once")
        return applied.replace(old, new)

    swapped = copy.deepcopy(payload)
    helper_indices = [i for i, step in enumerate(swapped[12]) if step[0] == "helper"]
    swapped[12][helper_indices[0]], swapped[12][helper_indices[1]] = (
        swapped[12][helper_indices[1]], swapped[12][helper_indices[0]])
    compile_case("swapped-helpers", render_payload(swapped), expected="boundary_sequence_")

    missing = copy.deepcopy(payload)
    missing[12].pop(helper_indices[1])
    compile_case("missing-helper", render_payload(missing), expected="boundary_sequence_")

    snapshot = copy.deepcopy(payload)
    snapshot[12][helper_indices[0]][4] = []
    compile_case("helper-snapshot", render_payload(snapshot),
                 expected="boundary_sequence_registration_order")

    (work / "report.json").write_text(json.dumps({
        "kind": "imported_multi_helper_sequence_regression",
        "status": "passed",
        "records": records,
        "helperCount": len(helpers),
        "acceptedCampaignCoverage": False,
        "structuralWireChecks": structural_wire_checks,
        "runtimeReplayChecks": ["swapped-helpers", "missing-helper", "helper-snapshot"],
        "limitations": [
            "No full Mathlib replay or module acceptance is claimed.",
            "The conditional rewrite requires hp : p, and make_two_helpers emits a marker while authentic registration interleaving is required in the recorded payload.",
        ],
    }, indent=2) + "\n")
    print(work / "report.json", flush=True)


if __name__ == "__main__":
    main()
