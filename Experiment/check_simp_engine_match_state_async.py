#!/usr/bin/env python3
"""Record/render/replay fresh Sort and Prop bundles with exact async state."""
from pathlib import Path
import copy
import hashlib
import json
import tempfile

import boundary_protocol as protocol
import check_simp_engine_boundary_source as source

ROOT = Path(__file__).resolve().parents[1]
MODULE = "Experiment.SimpEngineMatchStateAsync"


def fixture(cached: bool, kind: str = "prop") -> str:
    result = '''module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary
open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary

@[expose] public def propChoice (p q : Prop) (h : p ∨ q) : p ∨ q :=
  match h with
  | .inl hp => .inl hp
  | .inr hq => .inr hq

elab "warm_prop_cache" : tactic => do
  let _ ← Match.getEquationsFor `propChoice.match_1

elab "realize_prop_cache" : tactic => withMainContext do
  let before := Match.matchEqnsExt.getState (← getEnv)
  let eqns ← Match.getEquationsFor `propChoice.match_1
  let env ← getEnv
  let splitter ← getConstInfo eqns.splitterName
  unless isPrivateName eqns.splitterName && (← isProp splitter.type) do
    throwError "fixture splitter is not a private proof"
  unless boundaryMatchEqnsStateEq before (Match.matchEqnsExt.getState env) do
    throwError "fixture unexpectedly changed default local state"
  let snapshot := Match.matchEqnsExt.getState (asyncMode := .async .asyncEnv)
    (asyncDecl := eqns.splitterName) env
  unless snapshot.map.contains `propChoice.match_1 do
    throwError "fixture has no async matcher snapshot"
  IO.println "PROP_MATCH_FIXTURE private=true prop=true defaultLocalUnchanged=true asyncPresent=true"
  evalTactic (← `(tactic| assumption))

elab "assert_match_cache" : tactic => do
  let env ← getEnv
  let anchor := `propChoice.match_1
  let splitterName := mkPrivateName env anchor ++ `splitter
  unless env.containsOnBranch splitterName do
    throwError "replay continuation missing splitter"
  let state := Match.matchEqnsExt.getState env
    (asyncMode := .async .asyncEnv) (asyncDecl := splitterName)
  let some eqns := state.map.find? anchor | throwError "replay continuation missing async map"
  unless eqns.eqnNames.size == 2 && eqns.eqnNames.all state.eqns.contains &&
      eqns.eqnNames.all env.containsOnBranch do
    throwError "replay continuation missing equations"
  IO.println "MATCH_CACHE_PRESENT"

private theorem sample (p q : Prop) (h : p) (hpq : p → q) : q := by
CACHE
  first
  | simp_engine_boundary_record "async-match-test" (disch := realize_prop_cache) [hpq]
  | exact hpq h
  assert_match_cache
'''.replace("\nCACHE\n", "\n  warm_prop_cache\n" if cached else "\n")

    if kind == "mixed":
        result = result.replace("@[expose] public def propChoice", """@[expose] public def aaAlias (n : Nat) : Nat := n
@[expose] public def zzAlias (n : Nat) : Nat := n
@[expose] public def propChoice""")
        result = result.replace("  let env ← getEnv\n  let splitter ←", """  let some _ ← getEqnsFor? `aaAlias | throwError "missing first mixed equation"
  let some _ ← getEqnsFor? `zzAlias | throwError "missing last mixed equation"
  let env ← getEnv
  let splitter ←""")
    if kind == "nat":
        result = result.replace("""@[expose] public def propChoice (p q : Prop) (h : p ∨ q) : p ∨ q :=
  match h with
  | .inl hp => .inl hp
  | .inr hq => .inr hq""", """@[expose] public def propChoice (n : Nat) : Nat :=
  match n with
  | 0 => 7
  | n + 1 => n""")
        result = result.replace("&& (← isProp splitter.type)", "&& !(← isProp splitter.type)")
        result = result.replace("prop=true", "prop=false")
        result = result.replace('  IO.println "MATCH_CACHE_PRESENT"', '''  let some (.defnInfo original) := env.find? ``propChoice (skipRealize := true)
    | throwError "missing computation fixture"
  let function := original.value.replace fun expression => match expression with
    | .const name levels => if name == anchor then some (.const splitterName levels) else none
    | _ => none
  let expression := mkApp function (mkNatLit 5)
  checkWithKernel expression
  unless ← isDefEq expression (mkNatLit 4) do
    throwError "captured splitter changed computation"
  IO.println "MATCH_CACHE_PRESENT"''')
    return result


def main() -> None:
    parent = ROOT / ".lake/week-2026-08-31/match-state-async"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="fixture-", dir=parent))
    dylib = source.query_json_string(
        source.run(["lake", "query", "ExplicitLean:shared", "--json"]), "shared query")
    records = []

    def compile_case(label, text, *, recording, expected_abort=None):
        path = work / label / "Experiment/SimpEngineMatchStateAsync.lean"
        path.parent.mkdir(parents=True)
        path.write_text(text)
        env, nonce = (protocol.recording_subprocess_environment() if recording
                      else protocol.replay_subprocess_environment())
        try:
            output = source.compile_source(dylib, path, env=env)
        except RuntimeError as error:
            path.with_suffix(".log").write_text(str(error))
            raise
        path.with_suffix(".log").write_text(output)
        records.append({"label": label, "nonce": nonce, "source": str(path),
            "sourceSha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "log": str(path.with_suffix(".log")),
            "logSha256": hashlib.sha256(path.with_suffix(".log").read_bytes()).hexdigest(),
            "compilerExit": 0, "expectedAbort": expected_abort})
        checker = protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers
        try:
            checker(output, expected_nonce=nonce, expected_occurrence="async-match-test", expected_module=MODULE)
        except RuntimeError as error:
            if expected_abort is None or expected_abort not in str(error):
                raise
        else:
            if expected_abort is not None:
                raise RuntimeError(f"{label}: swallowed invalid matcher payload was accepted")
        if expected_abort is None and "MATCH_CACHE_PRESENT" not in output:
            raise RuntimeError(f"{label}: replay continuation did not observe complete bundle")
        reports = protocol.parse_framed_json_lines(output, marker=source.ARTIFACT_MARKER,
            expected_nonce=nonce, label="boundary artifact")
        if expected_abort is not None and reports:
            raise RuntimeError(f"{label}: rejected run emitted usable artifacts")
        print(f"matcher source: {label}: passed", flush=True)
        return reports, output

    for kind, cached in [("prop", False), ("prop", True), ("nat", False), ("mixed", False)]:
        label = kind + ("-cached" if cached else "-fresh")
        recorded = fixture(cached, kind)
        reports, output = compile_case(label + "-record", recorded, recording=True)
        if len(reports) != 1 or reports[0]["status"] != "success":
            raise RuntimeError(f"unexpected matcher result for {label}")
        protocol.validate_report(reports[0], "async-match-test", MODULE)
        expected = ([] if cached else ["declare_equation", "declare_matcher", "declare_equation"]
                    if kind == "mixed" else ["declare_matcher"])
        if [action["kind"] for action in reports[0]["environmentActions"]] != expected:
            raise RuntimeError(f"wrong matcher action delta for {label}")
        replacement = source.preserve_original_call(source.format_report_variants(reports, "      "),
            "simp (disch := realize_prop_cache) [hpq]", "      ")
        applied = recorded.replace("public meta import ExplicitLean.SimpEngine.Boundary\n",
                                   "public meta import ExplicitLean.SimpEngine.Boundary.Tactic\npublic meta import ExplicitLean.SimpEngine.Boundary.MatchState\n")
        applied = applied.replace('simp_engine_boundary_record "async-match-test" (disch := realize_prop_cache) [hpq]', replacement)
        _, replay_output = compile_case(label + "-replay", applied, recording=False)
        if "PROP_MATCH_FIXTURE" in replay_output:
            raise RuntimeError("replay reran the recording discharger")
        if kind == "prop" and not cached:
            extra = recorded.replace('  let env ← getEnv\n  let splitter ←', '''  let extraName := mkPrivateNameCore (← getEnv).mainModule `sample.extraComputation
  addDecl <| .defnDecl {
    name := extraName, levelParams := [], type := mkConst ``Nat,
    value := mkNatLit 1, hints := .abbrev, safety := .safe }
  let env ← getEnv
  let splitter ←''')
            extra = extra.replace("\n  assert_match_cache\n", "\n")
            compile_case(label + "-extra-computation", extra, recording=True,
                expected_abort="boundary_matcher_unsupported_extra_declaration")
            action = reports[0]["environmentActions"][0]
            original = action["declaration"]
            def corrupt_set(bundle):
                bundle[9][1].pop()
            def corrupt_group(bundle):
                theorem = json.loads(bundle[7][0][1]); theorem[2] = []
                bundle[7][0][1] = json.dumps(theorem, separators=(",", ":"))
            mutations = [("async-equation-set", corrupt_set, "boundary_matcher_state_conflict:payload-transition"),
                ("persistent-info", lambda bundle: bundle.__setitem__(6, copy.deepcopy(bundle[3][2])), "boundary_matcher_unexpected_splitter_info"),
                ("theorem-group", corrupt_group, "boundary_matcher_theorem_group")]
            for suffix, mutate, detail in mutations:
                bundle = json.loads(original); mutate(bundle)
                changed = json.dumps(bundle, separators=(",", ":"))
                try:
                    protocol.validate_environment_actions([{**action, "declaration": changed}], suffix)
                except RuntimeError:
                    pass
                else:
                    raise RuntimeError(f"Python accepted invalid {suffix}")
                old = source.lean_string(original)
                assert applied.count(old) == 1
                corrupted = applied.replace(old, source.lean_string(changed))
                # The outer `first` still compiles through its fallback. The
                # replay-abort scan, rather than a continuation assertion, must
                # reject the swallowed infrastructure failure.
                corrupted = corrupted.replace("\n  assert_match_cache\n", "\n")
                compile_case(label + "-" + suffix, corrupted, recording=False, expected_abort=detail)
    (work / "report.json").write_text(json.dumps({"kind": "captured_matcher_source_regression",
        "status": "passed", "records": records}, indent=2) + "\n")
    print(f"matcher source evidence: {work}", flush=True)


if __name__ == "__main__":
    main()
