#!/usr/bin/env python3
"""Exercise the local MatchEqns guard around a caught boundary failure.

Each fixture preinstalls a private matcher/equation state before the observed
boundary.  The positive case leaves it unchanged.  The two negative
dischargers mutate either the cached matcher map or the independent equation
set; the outer ``first`` must still compile through its fallback, while the
authenticated recording-abort scan rejects the run and no artifact is usable.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile

import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import check_simp_engine_boundary_source as source


ROOT = Path(__file__).resolve().parents[1]
MODULE = "Experiment.SimpEngineMatchStateRuntime"
ARTIFACT_ROOT = ROOT / ".lake" / "week-2026-08-31" / "match-state"
OCCURRENCIES = {
    "unchanged": "match-state-unchanged",
    "map": "match-state-map",
    "eqns": "match-state-eqns",
}


def fixture(case: str) -> str:
    occurrence = OCCURRENCIES[case]
    discharger = {
        "unchanged": "match_state_default_discharge",
        "map": "match_state_map_discharge",
        "eqns": "match_state_eqns_discharge",
    }[case]
    return f"""module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary

open Lean Meta Elab Tactic

namespace match_state_fixture

-- Keep all names and namespaces outside the observed boundary.  The theorem
-- is private so the fixture does not exercise the public_aux declaration rule.
private theorem sample : True := True.intro
private def sampleMatcher (n : Nat) : Nat := n
private theorem sampleEqn (n : Nat) : sampleMatcher n = n := rfl
private theorem sampleExtraEqn : True := True.intro
private def sampleSplitter (n : Nat) : Nat := n

private meta def sampleMatcherInfo : MatcherInfo := {{
  numParams := 0, numDiscrs := 1, altInfos := #[], uElimPos? := none,
  discrInfos := #[{{ hName? := none }}], overlaps := {{}} }}

private meta def installSampleMatchEqns : CoreM Unit :=
  Match.registerMatchEqns ``sampleMatcher {{
    eqnNames := #[``sampleEqn], splitterName := ``sampleSplitter,
    splitterMatchInfo := sampleMatcherInfo }}

run_cmd Lean.Elab.Command.liftCoreM installSampleMatchEqns

elab "match_state_default_discharge" : tactic => withMainContext do
  evalTactic (← `(tactic| assumption))

elab "match_state_map_discharge" : tactic => withMainContext do
  liftMetaTactic fun goal => do
    liftM (m := CoreM) <| Match.registerMatchEqns ``sampleMatcher {{
      eqnNames := #[``sampleEqn], splitterName := ``sampleSplitter,
      splitterMatchInfo := {{ sampleMatcherInfo with numParams := 1 }} }}
    pure [goal]
  evalTactic (← `(tactic| assumption))

elab "match_state_eqns_discharge" : tactic => withMainContext do
  modifyEnv fun env => Match.matchEqnsExt.modifyState env fun state =>
    {{ state with eqns := state.eqns.insert ``sampleExtraEqn }}
  evalTactic (← `(tactic| assumption))

private theorem sampleTarget (p q : Prop) (h : p) (hpq : p → q) : q := by
  first
  | simp_engine_boundary_record "{occurrence}"
      (disch := {discharger}) [hpq]
  | exact hpq h

end match_state_fixture
"""


def write_fixture(work: Path, case: str) -> Path:
    path = work / case / "Experiment" / "SimpEngineMatchStateRuntime.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(fixture(case), encoding="utf-8")
    return path


def check_case(work: Path, dylib: str, case: str) -> dict[str, object]:
    path = write_fixture(work, case)
    output, nonce = source.compile_recording_source(dylib, path)
    path.with_suffix(".log").write_text(output, encoding="utf-8")
    artifacts = protocol.parse_framed_json_lines(
        output,
        marker=materializer.ARTIFACT_MARKER,
        expected_nonce=nonce,
        label=f"{case} boundary artifact",
    )
    aborts = protocol.parse_framed_json_lines(
        output,
        marker=protocol.RECORDING_ABORT_MARKER,
        expected_nonce=nonce,
        label=f"{case} recording abort",
    )
    if case == "unchanged":
        protocol.check_recording_abort_markers(
            output, expected_nonce=nonce, expected_module=MODULE,
        )
        if len(aborts) != 0:
            raise RuntimeError(f"unchanged case emitted aborts: {aborts}")
        if len(artifacts) != 1 or artifacts[0].get("status") != "success":
            raise RuntimeError(f"unchanged case did not produce one artifact: {artifacts}")
        protocol.validate_report(artifacts[0], OCCURRENCIES[case], MODULE)
        expected = "valid artifact"
    else:
        if len(aborts) != 1:
            raise RuntimeError(f"{case} case expected one abort, found {aborts}")
        if artifacts:
            raise RuntimeError(f"{case} case emitted a usable artifact: {artifacts}")
        try:
            protocol.check_recording_abort_markers(
                output, expected_nonce=nonce, expected_module=MODULE,
                expected_occurrence=OCCURRENCIES[case],
            )
        except RuntimeError as error:
            expected = "authenticated abort"
            if "boundary recording abort" not in str(error):
                raise RuntimeError(f"{case} abort was not authenticated: {error}") from error
        else:
            raise RuntimeError(f"{case} abort was accepted by the protocol scan")
        if "boundary_comparison_local_match_eqns_state" not in aborts[0]["detail"]:
            raise RuntimeError(f"{case} abort has wrong detail: {aborts}")
    return {
        "case": case,
        "sourcePath": str(path),
        "sourceSha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "logPath": str(path.with_suffix(".log")),
        "logSha256": hashlib.sha256(path.with_suffix(".log").read_bytes()).hexdigest(),
        "compilerExit": 0,
        "nonce": nonce,
        "artifactCount": len(artifacts),
        "abortCount": len(aborts),
        "result": expected,
        "abort": aborts,
    }


def main() -> int:
    ARTIFACT_ROOT.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="fixture-", dir=ARTIFACT_ROOT))
    dylib = source.query_json_string(
        source.run(["lake", "query", "ExplicitLean:shared", "--json"]),
        "shared query",
    )
    evidence = [check_case(work, dylib, case) for case in OCCURRENCIES]
    report = {
        "kind": "simp_engine_match_state_check",
        "schema": 1,
        "status": "passed",
        "module": MODULE,
        "evidenceRoot": str(work),
        "cases": evidence,
    }
    (work / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
