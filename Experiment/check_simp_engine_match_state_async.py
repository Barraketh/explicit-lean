#!/usr/bin/env python3
"""Exercise a real private Prop splitter's local async extension snapshot."""
from pathlib import Path
import json
import tempfile

import boundary_protocol as protocol
import check_simp_engine_boundary_source as source

ROOT = Path(__file__).resolve().parents[1]
MODULE = "Experiment.SimpEngineMatchStateAsync"


def fixture(cached: bool) -> str:
    return '''module
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

private theorem sample (p q : Prop) (h : p) (hpq : p → q) : q := by
CACHE
  first
  | simp_engine_boundary_record "async-match-test" (disch := realize_prop_cache) [hpq]
  | exact hpq h
'''.replace("CACHE", "  warm_prop_cache" if cached else "")


def main() -> None:
    parent = ROOT / ".lake/week-2026-08-31/match-state-async"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="fixture-", dir=parent))
    dylib = source.query_json_string(
        source.run(["lake", "query", "ExplicitLean:shared", "--json"]), "shared query")
    for cached in (False, True):
        label = "cached" if cached else "new-realization"
        path = work / label / "Experiment/SimpEngineMatchStateAsync.lean"
        path.parent.mkdir(parents=True)
        path.write_text(fixture(cached))
        output, nonce = source.compile_recording_source(dylib, path)
        path.with_suffix(".log").write_text(output)
        path.with_suffix(".nonce.json").write_text(json.dumps({"nonce": nonce}) + "\n")
        if "PROP_MATCH_FIXTURE private=true prop=true defaultLocalUnchanged=true asyncPresent=true" not in output:
            raise RuntimeError("real Prop matcher did not exercise the async-only snapshot")
        reports = protocol.parse_framed_json_lines(
            output, marker=source.ARTIFACT_MARKER, expected_nonce=nonce, label="boundary artifact")
        try:
            protocol.check_recording_abort_markers(output, expected_nonce=nonce,
                expected_occurrence="async-match-test", expected_module=MODULE)
        except RuntimeError as error:
            if cached or "boundary_comparison_local_match_eqns_state:" not in str(error):
                raise
            if reports:
                raise RuntimeError("unreplayed matcher snapshot emitted usable artifacts")
        else:
            if not cached or len(reports) != 1 or reports[0]["status"] != "success":
                raise RuntimeError(f"unexpected matcher result for {label}")
            protocol.validate_report(reports[0], "async-match-test", MODULE)
        print(f"async matcher state: {label}: passed", flush=True)
    print(f"async matcher evidence: {work}", flush=True)


if __name__ == "__main__":
    main()
