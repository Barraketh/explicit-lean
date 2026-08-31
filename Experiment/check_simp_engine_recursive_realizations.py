#!/usr/bin/env python3
"""Truncated original ModifyLast: fresh and cached recursive group replay."""
from pathlib import Path
import copy
import hashlib
import shutil
import subprocess
import json
import tempfile

import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import check_simp_engine_boundary_source as formatter

ROOT = Path(__file__).resolve().parents[1]
MODULE = "Mathlib.Data.List.ModifyLast"
ORIGINAL = "simp only [nil_append, modifyLast.go]"

MARKER = "SINGLE_CHILD_STOCK "
PROBE = r'''
public meta import ExplicitLean.SimpEngine.Boundary
import all ExplicitLean.SimpEngine.Boundary.RealizationCodec
import all Lean.Environment
import all Lean.Meta.Basic
meta import all Lean.Meta.Constructions.SparseCasesOn
open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary

meta section
private unsafe def mutateRecursiveCacheImpl (env : Environment) (mode : String) : IO Unit := do
  if mode == "none" then return
  discard <| IO.wait env.checked
  let some ctx := env.importRealizationCtx? | throw <| IO.userError "fixture missing imports"
  let mut map ← ctx.realizeMapRef.get
  let some raw := map.find? (TypeName.typeName Environment.RealizeConstKey)
    | throw <| IO.userError "fixture missing map"
  let entries := unsafeCast (β := PHashMap Environment.RealizeConstKey (Task Dynamic)) raw
  let key : Environment.RealizeConstKey := { constName := `List.modifyLast.go.eq_def }
  let some task := entries.find? key | throw <| IO.userError "fixture missing key"
  unless ← IO.hasFinished task do throw <| IO.userError "fixture producer unfinished"
  let entries ← match mode with
    | "absent" => pure (entries.erase key)
    | "pending" => do
      let promise ← IO.Promise.new
      -- Fixture-only untyped slot keeps the deliberately unresolved promise alive.
      map := map.insert `RecursiveFixtureHeldPromise (unsafeCast promise)
      pure (entries.insert key promise.result!)
    | "wrong-type" => pure (entries.insert key (.pure (.mk (default : AsyncConsts))))
    | "missing-child" => do
      let child : Environment.RealizeConstKey := {
        constName := mkPrivateName env `List.modifyLast.go.match_1 ++ `splitter }
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
    | "corrupt-sparse" => do
      let some result := task.get.get? Environment.RealizeConstResult
        | throw <| IO.userError "fixture result type"
      let helper := mkPrivateName env `List.modifyLast.go.match_1 ++ `splitter._sparseCasesOn_3
      let mut changed := false
      let mut privateMembers := []
      for member in result.newConsts.private do
        let member ← if member.constInfo.name == helper then do
          let view ← memberEnvironment env member
          unless !(sparseCasesOnCacheExt.getState view).isEmpty do
            throw <| IO.userError "fixture missing sparse metadata"
          let view := sparseCasesOnCacheExt.modifyState view fun _ => {}
          changed := true
          pure { member with exts? := some (.pure view.base.private.extensions) }
        else pure member
        privateMembers := privateMembers.concat member
      unless changed do throw <| IO.userError "fixture no sparse helper"
      pure (entries.insert key (.pure (.mk { result with newConsts.private := privateMembers })))
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
@[implemented_by mutateRecursiveCacheImpl]
private opaque mutateRecursiveCache (env : Environment) (mode : String) : IO Unit
end

elab "mutate_recursive_cache " mode:str : tactic => do
  mutateRecursiveCache (← getEnv) mode.getString

open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary in
elab "observe_realization_groups " label:str inner:tactic : tactic => do
  let before ← getEnv
  let checkedBefore := before.constants.foldStage2
    (fun names name _ => names.insert name) ({} : NameSet)
  let genBefore ← getDeclNGen
  evalTactic inner
  let after ← getEnv
  let genAfter ← getDeclNGen
  discard <| IO.wait after.checked
  let added ← branchDelta before after
  let publicAdded ← branchDelta before after true
  let groups ← candidateGroups after
  let eligible := groups.filter fun group => !group.members.isEmpty &&
    group.members.all added.contains && group.members.all (!before.containsOnBranch ·)
  let covers := groupCovers eligible added
  let checkedAdded := after.constants.foldStage2
    (fun names name _ => if checkedBefore.contains name then names else names.push name)
    (#[] : Array Name)
  let mut diagnostics := #[]
  for group in groups do
    if group.owner == `List.modifyLast.go || group.owner == `List.modifyLast.go.match_1 then
      let descriptor ← completedCacheDescriptor after group.owner group.key
      diagnostics := diagnostics.push <| Json.mkObj [
        ("owner", toJson group.owner.toString), ("key", toJson group.key.toString),
        ("members", toJson (group.members.map Name.toString)),
        ("publicMembers", toJson (group.publicMembers.map Name.toString)),
        ("descriptor", descriptor)]
  let genJson := fun (g : DeclNameGenerator) => Json.mkObj [
    ("namePrefix", encodeBoundaryName g.namePrefix), ("idx", toJson g.idx),
    ("parentIdxs", toJson g.parentIdxs)]
  let report := Json.mkObj [
    ("label", toJson label.getString),
    ("beforeGenerator", genJson genBefore), ("afterGenerator", genJson genAfter),
    ("branchAdded", toJson (added.map Name.toString)),
    ("publicBranchAdded", toJson (publicAdded.map Name.toString)),
    ("checkedBeforeMembership", toJson (added.map checkedBefore.contains)),
    ("checkedAdded", toJson (checkedAdded.map Name.toString)),
    ("disjointCoverCount", toJson covers.size), ("groups", .arr diagnostics)]
  let some nonce ← IO.getEnv "SIMP_ENGINE_BOUNDARY_RUN_NONCE"
    | throwError "missing diagnostic nonce"
  IO.println s!"\nSINGLE_CHILD_STOCK {nonce} {report.compress}"
'''


def source_text():
    original = (ROOT / ".lake/packages/mathlib/Mathlib/Data/List/ModifyLast.lean").read_text()
    prefix, rest = original.split("private theorem modifyLast.go_concat", 1)
    body = "private theorem modifyLast.go_concat" + rest.split("\ntheorem modifyLast_concat", 1)[0]
    fresh = body.replace("    simp only [nil_append, modifyLast.go]; rfl",
                         "    -- simp only [nil_append, modifyLast.go]\n"
                         '    observe_realization_groups "fresh" simp only [nil_append, modifyLast.go]; rfl', 1)
    cached = body.replace("private theorem modifyLast.go_concat", "private theorem modifyLast.go_concat_cached", 1)
    cached = cached.replace(":= by\n", ':= by\n  mutate_recursive_cache "none"\n', 1)
    cached = cached.replace("    simp only [nil_append, modifyLast.go]; rfl",
                            "    -- simp only [nil_append, modifyLast.go]\n"
                            '    observe_realization_groups "cached" simp only [nil_append, modifyLast.go]; rfl', 1)
    header, declarations = prefix.split("/-! ### List.modifyLast -/", 1)
    return header + PROBE + "\n/-! ### List.modifyLast -/" + declarations + fresh + "\nrun_meta do\n  discard <| IO.wait (← getEnv).checked\n\n" + cached + "\nend List\n"



def input_hashes():
    paths = list((ROOT / "ExplicitLean").rglob("*.lean"))
    paths += list((ROOT / "Experiment").glob("*.py"))
    paths += [ROOT / "lean-toolchain", ROOT / "lake-manifest.json",
              ROOT / ".lake/packages/mathlib/Mathlib/Data/List/ModifyLast.lean",
              ROOT / ".lake/build/lib/libexplicitLean_ExplicitLean.dylib"]
    paths += [p for p in (ROOT / ".lake/build/lib/lean/ExplicitLean").rglob("*")
              if p.is_file() and p.suffix in {".olean", ".private", ".server", ".ir"}]
    paths += [Path(subprocess.check_output(["lake", "env", "which", "lean"], cwd=ROOT, text=True).strip())]
    return {str(p.resolve()): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))}


def main():
    parent = ROOT / ".lake/single-child"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="recursive-", dir=parent))
    print(work, flush=True)
    original = source_text()
    before = input_hashes()
    runs = []

    def run(label, text, recording=False, expected=None):
        path = materializer._copy_at_module_root(work / label, "Mathlib/Data/List/ModifyLast.lean", text.encode())
        env, nonce = (protocol.recording_subprocess_environment() if recording else protocol.replay_subprocess_environment())
        code, output, elapsed = materializer._compile_copy(path,
            str(ROOT / ".lake/build/lib/libexplicitLean_ExplicitLean.dylib"), 240, env=env)
        log = work / f"{label}.log"
        log.write_text(output)
        check = protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers
        failure = None
        try:
            check(output, expected_nonce=nonce)
        except RuntimeError as error:
            failure = str(error)
        assert code != 124, f"{label}: compiler timeout is not an accepted result"
        if expected is None:
            assert code == 0 and failure is None, (failure or output[-5000:])
        else:
            assert failure is not None and expected in failure, failure or output[-5000:]
        runs.append({"label": label, "source": str(path), "log": str(log), "nonce": nonce,
                     "compilerExit": code, "recording": recording, "expectedAbort": expected,
                     "elapsedSeconds": elapsed})
        print(label + ": passed", flush=True)
        return output, nonce

    recorded = original
    for label in ("fresh", "cached"):
        recorded = recorded.replace(f'observe_realization_groups "{label}" {ORIGINAL}',
            f'observe_realization_groups "{label}" simp_engine_boundary_record "{label}" only [nil_append, modifyLast.go]')
    output, nonce = run("record", recorded, recording=True)
    reports = protocol.parse_framed_json_lines(output, marker=materializer.ARTIFACT_MARKER,
        expected_nonce=nonce, label="recursive artifacts")
    assert len(reports) == 2
    by_id = {r["occurrence"]: r for r in reports}
    for label, report in by_id.items():
        protocol.validate_report(report, label, MODULE)
        assert len(report["environmentActions"]) == 1
        action = report["environmentActions"][0]
        assert action["kind"] == "realize_groups"
        payload = json.loads(action["declaration"])
        assert payload[0] == "boundary_realization_batch_v2"
        assert payload[1] == (label == "cached")
        assert len(payload[10]) == 5 and payload[11] == [1, 2, 3, 4]
        assert [n[4] for n in payload[10]] == [[], [0], [], [], [1]]
    (work / "artifacts.json").write_text(json.dumps(by_id, indent=2) + "\n")

    def rendered(values):
        result = original
        for label in ("fresh", "cached"):
            call = formatter.format_report_variants([values[label]], "      ")
            line = f'    observe_realization_groups "{label}" {ORIGINAL}; rfl'
            replacement = f'    observe_realization_groups "{label}"\n      {call}\n    rfl'
            assert result.count(line) == 1
            result = result.replace(line, replacement)
        assert result.count("-- " + ORIGINAL) == 2
        return result

    output, nonce = run("fresh-cached", rendered(by_id))
    observations = protocol.parse_framed_json_lines(output, marker=MARKER,
        expected_nonce=nonce, label="recursive source observations")
    assert len(observations) == 2
    for observation in observations:
        assert observation["beforeGenerator"]["idx"] == 1
        assert observation["afterGenerator"]["idx"] == 5
        assert len(observation["branchAdded"]) == 9
        assert len(observation["checkedAdded"]) == (9 if observation["label"] == "fresh" else 0)
    for label, mutate, detail in [
        ("missing-equation-child", lambda p: p[10][4].__setitem__(4, []), "boundary_realization_v2_nested_closure"),
        ("cyclic-child", lambda p: p[10][1].__setitem__(4, [1]), "boundary_realization_v2_non_topological_children"),
        ("missing-helper", lambda p: p[10][0][5][4].pop(2), "boundary_realization_matcher_members_conflict"),
        ("unused-node", lambda p: p[11].pop(), "boundary_realization_v2_unused_node"),
        ("mutated-final-descriptor", lambda p: p[10][0][5][4][0][2].__setitem__(1, False),
         "boundary_realization_cached_descriptor_conflict"),
    ]:
        values = copy.deepcopy(by_id)
        action = values["fresh"]["environmentActions"][0]
        payload = json.loads(action["declaration"])
        mutate(payload)
        action["declaration"] = json.dumps(payload, separators=(",", ":"))
        # Deliberately bypass the wire validator to exercise the Lean abort path.
        # Format the valid source first, then replace its exact quoted payload.
        text = rendered(by_id)
        old = by_id["fresh"]["environmentActions"][0]["declaration"]
        assert json.dumps(old, ensure_ascii=False) in text
        text = text.replace(json.dumps(old, ensure_ascii=False), json.dumps(action["declaration"], ensure_ascii=False), 1)
        run(label, text, expected=detail)
    for mode, detail in [("absent", "activation_cache_absent"),
                         ("pending", "activation_cache_pending"),
                         ("wrong-type", "activation_cache_type"),
                         ("missing-child", "activation_cache_absent"),
                         ("corrupt-sparse", "boundary_realization_cached_descriptor_conflict")]:
        text = rendered(by_id)
        needle = 'mutate_recursive_cache "none"'
        assert text.count(needle) == 1
        text = text.replace(needle, f'mutate_recursive_cache "{mode}"')
        # The deliberately poisoned memo must not be queried by unrelated stock
        # tactics in the other case. Reuse the preceding checked theorem there;
        # the selected nil goal/caller is unchanged, and originals stay visible.
        before_cached, cached = text.split("private theorem modifyLast.go_concat_cached", 1)
        head, tail = cached.split("\n  | cons hd tl =>", 1)
        assert tail.endswith("\nend List\n")
        original_tail = tail.removesuffix("\nend List\n")
        cached = (head + "\n  | cons hd tl =>\n    /-" + original_tail + "\n    -/\n"
                  "    exact modifyLast.go_concat f a (hd :: tl) r\n\nend List\n")
        text = before_cached + "private theorem modifyLast.go_concat_cached" + cached
        run("cached-" + mode, text, expected=detail)
    after = input_hashes()
    assert before == after, "runtime/source inputs changed during recursive controls"
    archive = work / "evidence"
    archive.mkdir()
    paths = set(before) | {str(work / "artifacts.json")}
    paths |= {run[field] for run in runs for field in ("source", "log")}
    files = []
    for index, name in enumerate(sorted(paths)):
        path = Path(name)
        target = archive / f"{index}-{path.name}"
        shutil.copy2(path, target)
        files.append({"source": name, "archive": str(target),
                      "sha256": hashlib.sha256(target.read_bytes()).hexdigest()})
    (work / "report.json").write_text(json.dumps({"kind": "recursive-realization-controls",
        "acceptedCoverage": False, "artifactSchema": protocol.ARTIFACT_SCHEMA, "reportSchema": materializer.REPORT_SCHEMA, "runs": runs,
        "inputsBefore": before, "inputsAfter": after, "files": files}, indent=2) + "\n")
    print(work / "report.json", flush=True)


if __name__ == "__main__":
    main()
