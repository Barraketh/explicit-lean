#!/usr/bin/env python3
"""Reject lost auxiliary-cache effects, including caught tactic failures."""
from pathlib import Path
import hashlib
import json
import tempfile

import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import check_simp_engine_boundary_source as source

ROOT = Path(__file__).resolve().parents[1]
MODULE = "Experiment.SimpEngineAuxState"
KEY = "({ type := mkConst ``True, isPrivate := false, defeq := false } : AuxLemmaKey)"
PRIVATE_KEY = KEY.replace("isPrivate := false", "isPrivate := true")


def fixture(case: str) -> str:
    if case.startswith("async-"):
        return async_fixture(case)
    before = ""
    if case in ("unchanged", "erase-public", "levels", "erase-private"):
        name = "privateSample" if case == "erase-private" else "sample"
        before = f'''run_cmd Lean.Elab.Command.liftTermElabM do
  modifyEnv fun env => auxLemmasExt.modifyState env fun state =>
    {{ state with lemmas := state.lemmas.insert {KEY} (``{name}, []) }}
'''
    private_creation = "  let name ← withExporting (isExporting := false) <| mkAuxLemma [] (mkConst ``True) (mkConst ``True.intro)\n  unless isPrivateName name do throwError \"fixture expected private proof\""
    private_cache = lambda key, levels: private_creation + f"\n  modifyEnv fun env => auxLemmasExt.modifyState env fun state =>\n    {{ state with lemmas := state.lemmas.insert {key} (name, {levels}) }}"
    mutation = {
        "unchanged": "  pure ()",
        "insert-public": f"  modifyEnv fun env => auxLemmasExt.modifyState env fun state =>\n    {{ state with lemmas := state.lemmas.insert {KEY} (``sample, []) }}",
        "public-private-key": f"  modifyEnv fun env => auxLemmasExt.modifyState env fun state =>\n    {{ state with lemmas := state.lemmas.insert {{ {KEY} with isPrivate := true }} (``sample, []) }}",
        "erase-public": f"  modifyEnv fun env => auxLemmasExt.modifyState env fun state =>\n    {{ state with lemmas := state.lemmas.erase {KEY} }}",
        "erase-private": f"  modifyEnv fun env => auxLemmasExt.modifyState env fun state =>\n    {{ state with lemmas := state.lemmas.erase {KEY} }}",
        "levels": f"  modifyEnv fun env => auxLemmasExt.modifyState env fun state =>\n    {{ state with lemmas := state.lemmas.insert {KEY} (``sample, [`u]) }}",
        "fresh-private-proof": private_creation,
        "private-wrong-type": private_cache(PRIVATE_KEY.replace("``True", "``False"), "[]"),
        "private-wrong-levels": private_cache(PRIVATE_KEY, "[`u]"),
        "private-wrong-tag": private_cache(PRIVATE_KEY.replace("defeq := false", "defeq := true"), "[]"),
        "private-public-key": private_cache(KEY, "[]"),
    }[case]
    return f'''module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary
open Lean Meta Elab Tactic
namespace aux_state_fixture
theorem sample : True := True.intro
private theorem privateSample : True := True.intro
{before}
elab "cache_discharge" : tactic => withMainContext do
{mutation}
  evalTactic (← `(tactic| assumption))
private theorem target (p q : Prop) (h : p) (hpq : p → q) : q := by
  first
  | simp_engine_boundary_record "aux-state-{case}" (disch := cache_discharge) [hpq]
  | exact hpq h
end aux_state_fixture
'''


def async_fixture(case: str) -> str:
    text = fixture("unchanged")
    # Do not preinstall the public cache key: it must occur only in the
    # realizer's async snapshot, while the returned caller state is unchanged.
    start = text.index("run_cmd")
    end = text.index("private theorem target")
    text = text[:start] + '''private theorem asyncAnchor : True := True.intro
run_cmd Lean.Elab.Command.liftCoreM <| enableRealizationsForConst ``asyncAnchor
private meta def realizeSampleCache : MetaM Unit := do
  let key : AuxLemmaKey := { type := mkConst ``True, isPrivate := false, defeq := false }
  let before := (auxLemmasExt.getState (← getEnv)).lemmas.find? key
  let name := Name.str ``asyncAnchor "cacheSnapshot"
  realizeConst ``asyncAnchor name do
    addDecl (.thmDecl { name, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [name] })
    modifyEnv fun env => auxLemmasExt.modifyState env fun state =>
      { state with lemmas := state.lemmas.insert key (``sample, []) }
  let env ← getEnv
  unless (auxLemmasExt.getState env).lemmas.find? key == before do
    throwError "fixture changed caller-local cache"
  let snapshot := auxLemmasExt.getState (asyncMode := .async .asyncEnv) (asyncDecl := name) env
  unless snapshot.lemmas.find? key == some (``sample, []) do
    throwError "fixture has no async cache"
  IO.println "AUX_ASYNC_FIXTURE callerUnchanged=true asyncPresent=true"
elab "warm_aux_cache" : tactic => realizeSampleCache
elab "cache_discharge" : tactic => withMainContext do
  realizeSampleCache
  evalTactic (← `(tactic| assumption))
''' + text[end:]
    text = text.replace("aux-state-unchanged", f"aux-state-{case}")
    if case == "async-cached":
        text = text.replace("  first\n", "  warm_aux_cache\n  first\n")
    return text


def main() -> None:
    parent = ROOT / ".lake/week-2026-08-31/aux-state"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="fixture-", dir=parent))
    dylib = source.query_json_string(
        source.run(["lake", "query", "ExplicitLean:shared", "--json"]), "shared query")
    records = []
    for case in ("unchanged", "insert-public", "public-private-key", "erase-public",
                 "erase-private", "levels", "fresh-private-proof", "private-wrong-type",
                 "private-wrong-levels", "private-wrong-tag", "private-public-key",
                 "async-fresh", "async-cached"):
        path = work / case / "Experiment/SimpEngineAuxState.lean"
        path.parent.mkdir(parents=True)
        path.write_text(fixture(case))
        output, nonce = source.compile_recording_source(dylib, path)
        log = path.with_suffix(".log"); log.write_text(output)
        artifacts = protocol.parse_framed_json_lines(output, marker=materializer.ARTIFACT_MARKER,
            expected_nonce=nonce, label="auxiliary state artifact")
        aborts = protocol.parse_framed_json_lines(output, marker=protocol.RECORDING_ABORT_MARKER,
            expected_nonce=nonce, label="auxiliary state abort")
        if case.startswith("async-"):
            assert "AUX_ASYNC_FIXTURE callerUnchanged=true asyncPresent=true" in output
        if case in ("unchanged", "fresh-private-proof", "async-cached"):
            protocol.check_recording_abort_markers(output, expected_nonce=nonce,
                expected_module=MODULE)
            assert len(artifacts) == 1 and artifacts[0]["status"] == "success", artifacts
            protocol.validate_report(artifacts[0], f"aux-state-{case}", MODULE)
        else:
            assert not artifacts and len(aborts) == 1, (artifacts, aborts)
            assert "boundary_comparison_local_aux_lemmas_state:" in aborts[0]["detail"], aborts
            try:
                protocol.check_recording_abort_markers(output, expected_nonce=nonce,
                    expected_occurrence=f"aux-state-{case}", expected_module=MODULE)
            except RuntimeError as error:
                assert "boundary recording abort" in str(error), error
            else:
                raise AssertionError("caught auxiliary state mutation was accepted")
        sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
        records.append({"case": case, "source": str(path), "sourceSha256": sha(path),
            "log": str(log), "logSha256": sha(log), "nonce": nonce,
            "artifactCount": len(artifacts), "abortCount": len(aborts)})
        print(f"auxiliary cache state: {case}: passed", flush=True)
    report = {"kind": "auxiliary_cache_state_controls", "runtime": dylib,
        "runtimeSha256": sha(dylib), "records": records}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"auxiliary cache evidence: {work}", flush=True)


if __name__ == "__main__":
    main()
