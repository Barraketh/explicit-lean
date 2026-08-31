#!/usr/bin/env python3
"""Fresh-process grouped producer and completed-cache activation controls."""
from pathlib import Path
import copy
import hashlib
import json
import tempfile

import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import check_simp_engine_boundary_source as source

ROOT = Path(__file__).resolve().parents[1]
MODULE = "Experiment.RealizationGroups"
ORIGINAL = "simp [List.lookmap.go, List.lookmap]"
TEMPLATE = r'''module
public import Batteries.Data.List.Basic
public import Mathlib.Init
import Lean
public meta import ExplicitLean.SimpEngine.Boundary
import all Lean.Environment
import all Lean.Meta.Basic
open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary

meta section
private unsafe def mutateCacheImpl (env : Environment) (mode : String) : IO Unit := do
  if mode == "none" then return
  discard <| IO.wait env.checked
  let some ctx := env.importRealizationCtx? | throw <| IO.userError "fixture missing imports"
  let mut map ← ctx.realizeMapRef.get
  let some raw := map.find? (TypeName.typeName Environment.RealizeConstKey)
    | throw <| IO.userError "fixture missing map"
  let entries := unsafeCast (β := PHashMap Environment.RealizeConstKey (Task Dynamic)) raw
  let key : Environment.RealizeConstKey := { constName := `List.lookmap.go.eq_def }
  let some task := entries.find? key | throw <| IO.userError "fixture missing key"
  unless ← IO.hasFinished task do throw <| IO.userError "fixture producer unfinished"
  let entries ← match mode with
    | "absent" => pure (entries.erase key)
    | "pending" => do
      let promise ← IO.Promise.new
      -- Fixture-only untyped slot keeps the deliberately unresolved promise alive.
      map := map.insert `RealizationFixtureHeldPromise (unsafeCast promise)
      pure (entries.insert key promise.result!)
    | "wrong-type" => pure (entries.insert key (.pure (.mk (default : AsyncConsts))))
    | "missing-child" => do
      let child : Environment.RealizeConstKey := {
        constName := mkPrivateName env `List.lookmap.go.match_1 ++ `splitter }
      unless (entries.find? child).isSome do throw <| IO.userError "fixture missing child key"
      pure (entries.erase child)
    | "nonquiet" => do
      let some result := task.get.get? Environment.RealizeConstResult
        | throw <| IO.userError "fixture result type"
      let some status := result.dyn.get? Lean.Meta.RealizeConstantResult
        | throw <| IO.userError "fixture meta result type"
      let some snapshot := status.snap? | throw <| IO.userError "fixture missing snapshot"
      let status := { status with snap? := some { snapshot with
        element := { snapshot.element with isFatal := true } } }
      pure (entries.insert key (.pure (.mk { result with dyn := .mk status })))
    | "wrong-computation" => do
      let some result := task.get.get? Environment.RealizeConstResult
        | throw <| IO.userError "fixture result type"
      let mut changed := false
      let mut privateMembers := []
      for member in result.newConsts.private do
        let member ← match member.constInfo.constInfo.get with
          | .defnInfo info =>
            changed := true
            pure { member with constInfo := AsyncConstantInfo.ofConstantInfo (.defnInfo { info with value := mkNatLit 37 }) }
          | _ => pure member
        privateMembers := privateMembers.concat member
      unless changed do throw <| IO.userError "fixture no computational member"
      pure (entries.insert key (.pure (.mk { result with newConsts.private := privateMembers })))
    | _ => throw <| IO.userError "fixture invalid mutation"
  ctx.realizeMapRef.set (map.insert (TypeName.typeName Environment.RealizeConstKey) (unsafeCast entries))
  IO.println s!"CACHE_MUTATION {mode}"
@[implemented_by mutateCacheImpl]
private opaque mutateCache (env : Environment) (mode : String) : IO Unit
end

elab "mutate_cache " mode:str : tactic => do
  mutateCache (← getEnv) mode.getString

public section

private theorem fresh (α : Type) (f : α → Option α) (acc : Array α) :
    List.lookmap.go f [] acc = acc.toListAppend (List.lookmap f []) := by
  first
  | FRESH
  | exact (Array.toListAppend_eq.trans (List.append_nil _)).symm

private theorem cached (α : Type) (f : α → Option α) (acc : Array α) :
    List.lookmap.go f [] acc = acc.toListAppend (List.lookmap f []) := by
  mutate_cache "MUTATION"
  first
  | CACHED
  | exact (Array.toListAppend_eq.trans (List.append_nil _)).symm
'''


def main():
    parent = ROOT / ".lake/cached-activation"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="controls-", dir=parent))
    print(work, flush=True)
    dylib = str(ROOT / ".lake/build/lib/libexplicitLean_ExplicitLean.dylib")
    records = []

    def compile_case(label, text, recording=False, expected=None):
        path = materializer._copy_at_module_root(work / label, "Experiment/RealizationGroups.lean", text.encode())
        env, nonce = (protocol.recording_subprocess_environment() if recording else protocol.replay_subprocess_environment())
        code, output, _ = materializer._run_command(["lake", "env", "lean", f"--load-dynlib={dylib}", "-R", str(path.parent.parent), str(path)], 300, env=env)
        log = work / f"{label}.log"
        log.write_text(output)
        assert code == 0, output[-5000:]
        check = protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers
        try:
            check(output, expected_nonce=nonce)
        except RuntimeError as error:
            if expected is None or expected not in str(error):
                raise
        else:
            assert expected is None, f"{label}: missing required abort {expected}"
        records.append({"label":label,"nonce":nonce,"recording":recording,"compilerExit":code,
                        "expectedAbort":expected,"source":str(path),"log":str(log)})
        print(label + ": passed", flush=True)
        return protocol.parse_framed_json_lines(output, marker=materializer.ARTIFACT_MARKER,
            expected_nonce=nonce, label="realization controls")

    text = TEMPLATE.replace('"MUTATION"', '"none"')
    recorded = text.replace("FRESH", 'simp_engine_boundary_record "fresh" [List.lookmap.go, List.lookmap]').replace(
        "CACHED", 'simp_engine_boundary_record "cached" [List.lookmap.go, List.lookmap]')
    reports = compile_case("record", recorded, recording=True)
    assert len(reports) == 2
    by_id = {r["occurrence"]:r for r in reports}
    for occurrence, report in by_id.items():
        protocol.validate_report(report, occurrence, MODULE)
        assert len(report["environmentActions"]) == 1
        action = report["environmentActions"][0]
        assert action["kind"] == "realize_groups"
        assert json.loads(action["declaration"])[1] == (occurrence == "cached")
    def rendered(values):
        applied = text
        for occurrence, placeholder in [("fresh", "FRESH"), ("cached", "CACHED")]:
            call = source.preserve_original_call(source.format_report_variants([values[occurrence]], "    "), ORIGINAL, "    ")
            applied = applied.replace(placeholder, call)
        return applied
    applied = rendered(by_id)
    assert applied.count("-- " + ORIGINAL) == 2
    compile_case("fresh-and-cached", applied)
    for mode, detail in [("absent", "activation_cache_absent"), ("pending", "activation_cache_pending"),
                         ("wrong-type", "activation_cache_type"), ("missing-child", "activation_cache_absent"),
                         ("nonquiet", "activation_nonquiet_snapshot"),
                         ("wrong-computation", "activation_checked_member_conflict")]:
        compile_case(mode, applied.replace('mutate_cache "none"', f'mutate_cache "{mode}"'), expected=detail)
    mutated = copy.deepcopy(by_id)
    payload = json.loads(mutated["fresh"]["environmentActions"][0]["declaration"])
    payload[1] = True
    for root in payload[10]:
        for child in root[3]: child[2] = None
    mutated["fresh"]["environmentActions"][0]["declaration"] = json.dumps(payload, separators=(",", ":"))
    compile_case("cold-cache-only", rendered(mutated), expected="activation_cache_absent")
    mutated = copy.deepcopy(by_id)
    action = mutated["cached"]["environmentActions"][0]
    payload = json.loads(action["declaration"])
    member = payload[10][0][4][4][0]
    encoded = member[1][3][0][1]
    member[1][3][0][1] = ("0" if encoded[0] != "0" else "1") + encoded[1:]
    member[2][2] = copy.deepcopy(member[1])
    action["declaration"] = json.dumps(payload, separators=(",", ":"))
    compile_case("payload-metadata", rendered(mutated),
                 expected="boundary_realization_cached_descriptor_conflict")
    wire_rejections = []
    for label, mutate in [
        ("old-arity", lambda p: p.pop(9)),
        ("wrong-mode", lambda p: p.__setitem__(1, "cached")),
        ("duplicate-root", lambda p: p[10].append(copy.deepcopy(p[10][0]))),
        ("wrong-order", lambda p: p[2].reverse()),
        ("duplicate-sparse-key", lambda p: p[8].extend([
            [[[["s", "Nat"]], [], True], [["s", "Nat"]]],
            [[[["s", "Nat"]], [], True], [["s", "Nat"]]]])),
    ]:
        action = copy.deepcopy(by_id["cached"]["environmentActions"][0])
        payload = json.loads(action["declaration"])
        mutate(payload)
        action["declaration"] = json.dumps(payload, separators=(",", ":"))
        report = copy.deepcopy(by_id["cached"])
        report["environmentActions"] = [action]
        try:
            protocol.validate_report(report, "cached", MODULE)
        except RuntimeError:
            wire_rejections.append(label)
        else:
            raise AssertionError("accepted invalid wire mutation: " + label)
    report = {"kind":"realization_group_controls", "status":"passed", "acceptedCampaignCoverage":False,
              "records":records, "artifacts":reports, "wireRejections": wire_rejections,
              "hashes":{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in work.rglob("*") if p.is_file()}}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(work / "report.json", flush=True)


if __name__ == "__main__":
    main()
