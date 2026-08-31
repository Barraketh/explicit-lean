#!/usr/bin/env python3
"""Fresh record/render/replay controls for independently closed matcher bundles."""
from pathlib import Path
import copy
import hashlib
import json
import shutil
import tempfile

import boundary_protocol as protocol
import check_simp_engine_boundary_source as source

ROOT = Path(__file__).resolve().parents[1]
MODULE = "Experiment.MultipleMatcherFixture"
OCCURRENCE = "multiple-matchers"
ORIGINAL = "simp (disch := realize_bundles) only [hpq]"
CALL = 'simp_engine_boundary_record "multiple-matchers" (disch := realize_bundles) only [hpq]'
TEMPLATE = r'''module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary
open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary

@[expose] public def aaChoice (n : Nat) : Nat :=
  match n with
  | 0 => 7
  | n + 1 => n

@[expose] public def midAlias (n : Nat) : Nat := n

@[expose] public def zzChoice (p q : Prop) (h : p ∨ q) : p ∨ q :=
  match h with
  | .inl hp => .inl hp
  | .inr hq => .inr hq

elab "warm_first_bundle" : tactic => do
  discard <| Match.getEquationsFor `aaChoice.match_1
elab "warm_both_bundles" : tactic => do
  discard <| Match.getEquationsFor `aaChoice.match_1
  discard <| Match.getEquationsFor `zzChoice.match_1

elab "realize_bundles" : tactic => withMainContext do
  let before := Match.matchEqnsExt.getState (← getEnv)
  -- Generate in reverse of deterministic replay order.
  let second ← Match.getEquationsFor `zzChoice.match_1
  MIXED
  let first ← Match.getEquationsFor `aaChoice.match_1
  MUTATION
  let env ← getEnv
  unless boundaryMatchEqnsStateEq before (Match.matchEqnsExt.getState env) do
    throwError "stock caller-local matcher state unexpectedly changed"
  for eqns in #[first, second] do
    let state := Match.matchEqnsExt.getState env
      (asyncMode := .async .asyncEnv) (asyncDecl := eqns.splitterName)
    unless eqns.eqnNames.all state.eqns.contains do throwError "stock async equations absent"
  IO.println "MULTIPLE_MATCHER_STOCK localUnchanged=true asyncPresent=true"
  evalTactic (← `(tactic| assumption))

elab "assert_both_bundles" : tactic => do
  let env ← getEnv
  for anchor in #[`aaChoice.match_1, `zzChoice.match_1] do
    let splitter := mkPrivateName env anchor ++ `splitter
    unless env.containsOnBranch splitter do throwError "continuation missing splitter"
    let state := Match.matchEqnsExt.getState env
      (asyncMode := .async .asyncEnv) (asyncDecl := splitter)
    let some eqns := state.map.find? anchor | throwError "continuation missing matcher map"
    unless eqns.eqnNames.size == 2 && eqns.eqnNames.all state.eqns.contains &&
        eqns.eqnNames.all env.containsOnBranch do throwError "continuation missing bundle members"
  let some (.defnInfo original) := env.find? ``aaChoice (skipRealize := true)
    | throwError "missing computational fixture"
  let function := original.value.replace fun expression => match expression with
    | .const name levels => if name == `aaChoice.match_1 then
        some (.const (mkPrivateName env name ++ `splitter) levels) else none
    | _ => none
  let expression := mkApp function (mkNatLit 5)
  checkWithKernel expression
  unless ← isDefEq expression (mkNatLit 4) do throwError "captured splitter changed computation"
  IO.println "MULTIPLE_MATCHER_CONTINUATION twoBundles=true computation=true"

private theorem sample (p q : Prop) (h : p) (hpq : p → q) : q := by
  CACHE
  first
  | CALL
  | exact hpq h
  assert_both_bundles
'''


def fixture(cache="", mixed=False, mutation="", registered=False):
    if registered:
        mutation = """  for (anchor, eqns) in #[(`aaChoice.match_1, first), (`zzChoice.match_1, second)] do
    modifyEnv fun env => eqnsExt.modifyState env fun state => { state with
      mapInv := eqns.eqnNames.foldl (init := state.mapInv) (fun map name => map.insert name anchor) }
""" + mutation
    return (TEMPLATE.replace("  CACHE\n", f"  {cache}\n" if cache else "")
            .replace("  MIXED\n", "  discard <| getEqnsFor? `midAlias\n" if mixed else "")
            .replace("  MUTATION\n", mutation).replace("CALL", CALL))


def main():
    parent = ROOT / ".lake/matcher-multiple"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="controls-", dir=parent))
    print(work, flush=True)
    dylib = source.query_json_string(source.run(["lake", "query", "ExplicitLean:shared", "--json"]), "shared")
    def immutable_inputs():
        paths = [ROOT / "lean-toolchain", Path(dylib).resolve()]
        paths += sorted((ROOT / "Experiment").glob("*.py"))
        paths += sorted((ROOT / "ExplicitLean").rglob("*.lean"))
        paths += sorted((ROOT / ".lake/build/lib/lean/ExplicitLean").rglob("*.olean*"))
        paths += sorted((ROOT / ".lake/build/lib/lean/ExplicitLean").rglob("*.ir"))
        return [{"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                for path in paths]
    inputs = immutable_inputs()
    archived_inputs = []
    for index, item in enumerate(inputs):
        path = Path(item["path"])
        destination = work / "inputs" / f"{index}-{path.name}"
        destination.parent.mkdir(exist_ok=True)
        shutil.copy2(path, destination)
        assert hashlib.sha256(destination.read_bytes()).hexdigest() == item["sha256"]
        archived_inputs.append({**item, "archivedPath": str(destination)})
    archived_runtime = next(item["archivedPath"] for item in archived_inputs
                            if item["path"] == str(Path(dylib).resolve()))
    records = []
    artifacts = []

    def compile_case(label, text, *, recording, expected_abort=None):
        path = work / label / "Experiment/MultipleMatcherFixture.lean"
        path.parent.mkdir(parents=True)
        path.write_text(text)
        env, nonce = (protocol.recording_subprocess_environment() if recording else
                      protocol.replay_subprocess_environment())
        try:
            output = source.compile_source(archived_runtime, path, env=env)
        except RuntimeError as error:
            path.with_suffix(".log").write_text(str(error))
            raise
        log = path.with_suffix(".log")
        log.write_text(output)
        checker = protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers
        try:
            checker(output, expected_nonce=nonce, expected_module=MODULE, expected_occurrence=OCCURRENCE)
        except RuntimeError as error:
            if expected_abort is None or expected_abort not in str(error): raise
        else:
            if expected_abort is not None: raise RuntimeError(f"{label}: swallowed failure accepted")
        if expected_abort is None and "MULTIPLE_MATCHER_CONTINUATION" not in output:
            raise RuntimeError(f"{label}: continuation did not observe exact bundles")
        reports = protocol.parse_framed_json_lines(output, marker=source.ARTIFACT_MARKER,
            expected_nonce=nonce, label="boundary artifact")
        if expected_abort is not None and reports: raise RuntimeError(f"{label}: rejected run emitted artifact")
        records.append({"label":label, "nonce":nonce, "recording":recording,
            "source":str(path), "sourceSha256":hashlib.sha256(path.read_bytes()).hexdigest(),
            "log":str(log), "logSha256":hashlib.sha256(log.read_bytes()).hexdigest(),
            "compilerExit":0, "expectedAbort":expected_abort})
        print(f"multiple matcher: {label}: passed", flush=True)
        return reports, output

    for label, cache, mixed, registered, names in [
        ("fresh", "", False, False, ["aaChoice.match_1", "zzChoice.match_1"]),
        ("mixed", "", True, False, ["aaChoice.match_1", "midAlias.eq_1", "zzChoice.match_1"]),
        ("registered", "", False, True, ["aaChoice.match_1", "zzChoice.match_1"]),
        ("one-cached", "warm_first_bundle", False, False, ["zzChoice.match_1"]),
        ("both-cached", "warm_both_bundles", False, False, [])]:
        recorded = fixture(cache, mixed, registered=registered)
        reports, _ = compile_case(label + "-record", recorded, recording=True)
        if len(reports) != 1: raise RuntimeError("unexpected artifact count")
        report = reports[0]
        protocol.validate_report(report, OCCURRENCE, MODULE)
        if [a["name"] for a in report["environmentActions"]] != names:
            raise RuntimeError(f"{label}: unexpected declaration ordering")
        artifact = work / f"{label}-artifact.json"
        artifact.write_text(json.dumps(report, indent=2) + "\n")
        artifacts.append(str(artifact))
        replacement = source.preserve_original_call(source.format_report_variants(reports, "      "), ORIGINAL, "      ")
        applied = recorded.replace("public meta import ExplicitLean.SimpEngine.Boundary\n",
            "public meta import ExplicitLean.SimpEngine.Boundary.Tactic\npublic meta import ExplicitLean.SimpEngine.Boundary.MatchState\n").replace(CALL, replacement)
        _, output = compile_case(label + "-replay", applied, recording=False)
        if "MULTIPLE_MATCHER_STOCK" in output: raise RuntimeError("replay reran discharger")
        if label in {"mixed", "registered"}:
            second = report["environmentActions"][-1]
            payload = json.loads(second["declaration"])
            if not payload[13]: raise RuntimeError("fixture lacks a preceding equation registration")
            mutations = [
                ("second-equation-set", lambda p: p[9][1].pop(), "boundary_matcher_state_conflict:payload-transition"),
                ("second-splitter-info", lambda p: p.__setitem__(6, copy.deepcopy(p[3][2])), "boundary_matcher_unexpected_splitter_info"),
                ("second-prior-registration", lambda p: p.__setitem__(13, []), "boundary_matcher_equation_state_conflict:caller-before")]
            for suffix, mutate, detail in mutations:
                changed = copy.deepcopy(payload); mutate(changed)
                raw = json.dumps(changed, separators=(",", ":"))
                old = source.lean_string(second["declaration"])
                assert applied.count(old) == 1
                corrupted = applied.replace(old, source.lean_string(raw)).replace("  assert_both_bundles\n", "")
                compile_case(label + "-" + suffix, corrupted, recording=False, expected_abort=detail)
            changed = copy.deepcopy(report["environmentActions"])
            changed.reverse()
            try: protocol.validate_environment_actions(changed, "reversed multiple matcher actions")
            except RuntimeError as error:
                if "sorted" not in str(error): raise
            else: raise RuntimeError("Python accepted out-of-order actions")

    extra = fixture(mutation='''  let extraName := mkPrivateNameCore (← getEnv).mainModule `sample.extraComputation
  addDecl <| .defnDecl {
    name := extraName, levelParams := [], type := mkConst ``Nat,
    value := mkNatLit 1, hints := .abbrev, safety := .safe }
''').replace("  assert_both_bundles\n", "")
    compile_case("extra-computation", extra, recording=True,
        expected_abort="boundary_comparison_unsupported_environment_delta")
    if immutable_inputs() != inputs:
        raise RuntimeError("multiple matcher control inputs changed during validation")
    (work / "report.json").write_text(json.dumps({"kind":"multiple_matcher_source_regression",
        "status":"passed", "records":records, "artifacts":artifacts,
        "acceptedCampaignCoverage":False, "immutableInputs":archived_inputs,
        "reversedActionProtocolNegative":True}, indent=2) + "\n")
    print(work / "report.json", flush=True)


if __name__ == "__main__":
    main()
