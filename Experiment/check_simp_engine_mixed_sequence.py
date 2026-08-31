#!/usr/bin/env python3
"""Original-source mixed sequence recording and fresh replay controls."""
from pathlib import Path
import argparse, copy, hashlib, json, tempfile
import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import boundary_expr_codec as wire
import check_simp_engine_boundary_source as formatter
import check_simp_engine_recursive_realizations as recursive
ROOT = Path(__file__).resolve().parents[1]
MARKER = "MIXED_STOCK "

STATE_PROBE = r'''
namespace MixedFixture
open Lean Meta Elab Tactic
meta section
private unsafe def corruptMixedCacheImpl (env : Environment) (mode : String) : IO (IO Unit) := do
  discard <| IO.wait env.checked
  let some ctx := env.importRealizationCtx? | throw <| IO.userError "missing imports"
  let map ← ctx.realizeMapRef.get
  let some raw := map.find? (TypeName.typeName Environment.RealizeConstKey)
    | throw <| IO.userError "missing cache"
  let entries := unsafeCast (β := PHashMap Environment.RealizeConstKey (Task Dynamic)) raw
  let key : Environment.RealizeConstKey := { constName :=
    if env.mainModule == `Mathlib.Control.Basic then `joinM.eq_1 else `List.modifyLast.go.eq_def }
  let some task := entries.find? key | throw <| IO.userError "missing target cache"
  unless ← IO.hasFinished task do throw <| IO.userError "original producer pending"
  let mut finish : IO Unit := ctx.realizeMapRef.set map
  let entries ← if mode == "cache-absent" then pure (entries.erase key)
    else if mode == "cache-wrong-type" then pure (entries.insert key (.pure (.mk (default : AsyncConsts))))
    else if mode == "cache-pending" then do
      let promise ← IO.Promise.new
      finish := do
        promise.resolve task.get
        ctx.realizeMapRef.set map
      pure (entries.insert key promise.result!)
    else throw <| IO.userError "unknown cache mutation"
  ctx.realizeMapRef.set (map.insert (TypeName.typeName Environment.RealizeConstKey) (unsafeCast entries))
  return finish
@[implemented_by corruptMixedCacheImpl]
private opaque corruptMixedCache (env : Environment) (mode : String) : IO (IO Unit)
end
open Lean Meta Elab Tactic in
elab "with_pending_mixed " inner:tactic : tactic => do
  let finish ← corruptMixedCache (← getEnv) "cache-pending"
  try
    IO.println "MIXED_MUTATION cache-pending"
    evalTactic inner
  finally
    finish
open Lean Meta Elab Tactic in
elab "mutate_mixed_state " mode:str : tactic => do
  let mode := mode.getString
  if mode == "raw-axiom" || mode == "changed-kind" then
    let kind := if mode == "raw-axiom" then ConstantKind.axiom else .defn
    let some idx := (← getEnv).getModuleIdxFor? `id.eq_1
      | throwError "fixture target is not imported"
    modifyEnv fun env => privateConstKindsExt.toEnvExtension.modifyState env fun state =>
      let entries := state.importedEntries[idx]!.map fun (name, oldKind) =>
        (name, if name == `id.eq_1 then kind else oldKind)
      { state with importedEntries := state.importedEntries.set! idx entries }
    unless getOriginalConstKind? (← getEnv) `id.eq_1 == some kind do
      throwError "fixture original-kind mutation did not take effect"
  else if mode == "registration-collision" then
    modifyEnv fun env => eqnsExt.modifyState env fun state =>
      { state with mapInv := state.mapInv.insert `id.eq_1 `id }
  else if mode == "assert-nonactive" then
    let env ← getEnv
    unless env.isImportedConst `Bind.kleisliRight &&
        (env.constants.find? `Bind.kleisliRight.eq_1).isSome &&
        !env.containsOnBranch `Bind.kleisliRight.eq_1 do
      throwError "fixture expected checked imported equation off caller branch"
  else
    discard <| corruptMixedCache (← getEnv) mode
  IO.println s!"MIXED_MUTATION {mode}"
end MixedFixture
'''

CASES = {
    "control": ("Mathlib/Control/Basic.lean", "05514633fc5cec8c",
                "simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind]", 3),
    "modify": ("Mathlib/Data/List/ModifyLast.lean", "f33a950d34557463",
               "simp only [nil_append, modifyLast, modifyLast.go, Array.toListAppend_eq]", 6),
}


def source_text(case):
    module, occurrence, original, _ = CASES[case]
    source = (ROOT / ".lake/packages/mathlib" / module).read_text()
    if case == "control":
        source = source.split("\n@[simp]\ntheorem joinM_map_pure", 1)[0] + "\nend\n"
        header, declarations = source.split("/-!\n# Basic control operations", 1)
        prior, body = declarations.split("theorem joinM_map_joinM", 1)
        before = header + PROBE + STATE_PROBE + "\n/-!\n# Basic control operations" + prior + "theorem joinM_map_joinM"
        indent = "  "
    else:
        source = source.split("\ntheorem modifyLast_append_of_right_ne_nil", 1)[0] + "\nend List\n"
        header, declarations = source.split("/-! ### List.modifyLast -/", 1)
        prior, body = declarations.split("theorem modifyLast_concat", 1)
        before = header + PROBE + STATE_PROBE + "\n/-! ### List.modifyLast -/" + prior + "theorem modifyLast_concat"
        indent = "    "
    assert body.count(original) == 1
    body = body.replace(indent + original, indent + "-- " + original + "\n" + indent +
                        'observe_mixed_sequence "target" ' + original, 1)
    return before + body, indent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=CASES, default="control")
    parser.add_argument("--positive-only", action="store_true")
    args = parser.parse_args()
    module, occurrence, original, expected_idx = CASES[args.case]
    compiled_module = module[:-5].replace("/", ".")
    parent = ROOT / ".lake/mixed-sequence"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix=args.case + "-", dir=parent))
    print(work, flush=True)
    (work / "driver.py").write_bytes(Path(__file__).read_bytes())
    inputs = recursive.input_hashes()
    original_path = ROOT / ".lake/packages/mathlib" / module
    inputs[str(original_path.resolve())] = hashlib.sha256(original_path.read_bytes()).hexdigest()
    (work / "inputs-before.json").write_text(json.dumps(inputs, indent=2) + "\n")
    source, indent = source_text(args.case)
    runs = []

    def run(label, text, recording=False, expected=None):
        path = materializer._copy_at_module_root(work / label, module, text.encode())
        env, nonce = (protocol.recording_subprocess_environment() if recording else protocol.replay_subprocess_environment())
        code, output, elapsed = materializer._compile_copy(path,
            str(ROOT / ".lake/build/lib/libexplicitLean_ExplicitLean.dylib"), 360, env=env)
        log = work / (label + ".log"); log.write_text(output)
        check = protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers
        failure = None
        try:
            check(output, expected_nonce=nonce)
        except RuntimeError as error:
            failure = str(error)
        assert code in (0, 1), "timeout/signal termination is never a successful negative"
        if expected is None:
            assert code == 0 and failure is None, failure or output[-5000:]
        else:
            assert failure is not None and expected in failure, failure or output[-5000:]
        runs.append(dict(label=label, source=str(path), log=str(log), nonce=nonce,
                         compilerExit=code, recording=recording, expectedAbort=expected, elapsedSeconds=elapsed))
        print(label + ": passed", flush=True)
        return output, nonce

    record_source = source.replace('observe_mixed_sequence "target" ' + original,
        'observe_mixed_sequence "target" simp_engine_boundary_record ' + json.dumps(occurrence) + original[len("simp"):])
    output, nonce = run("record", record_source, recording=True)
    reports = protocol.parse_framed_json_lines(output, marker=materializer.ARTIFACT_MARKER,
        expected_nonce=nonce, label="mixed sequence artifacts")
    assert len(reports) == 1
    report = protocol.validate_report(reports[0], occurrence, compiled_module)
    stock_observations = protocol.parse_framed_json_lines(output, marker=MARKER,
        expected_nonce=nonce, label="original mixed observations")
    assert len(stock_observations) == 1
    stock = stock_observations[0]
    (work / "stock-observation.json").write_text(json.dumps(stock, indent=2) + "\n")
    assert len(report["environmentActions"]) == 1
    action = report["environmentActions"][0]
    payload = json.loads(action["declaration"])
    assert action["kind"] == "realize_groups" and payload[0] == "boundary_realization_sequence_v1"
    assert len(payload[3]) == 1
    (work / "artifact.json").write_text(json.dumps(report, indent=2) + "\n")

    def render(value):
        call = formatter.format_report_variants([value], indent + "  ")
        old = indent + 'observe_mixed_sequence "target" ' + original
        assert source.count(old) == 1
        return source.replace(old, indent + 'observe_mixed_sequence "target"\n' + indent + "  " + call, 1)

    output, nonce = run("fresh-replay", render(report))
    observed = protocol.parse_framed_json_lines(output, marker=MARKER, expected_nonce=nonce, label="mixed replay")
    assert len(observed) == 1
    assert observed[0]["beforeGenerator"]["idx"] == 1
    assert observed[0]["afterGenerator"]["idx"] == expected_idx
    assert len(observed[0]["checkedAdded"]) == 1
    for field in ("beforeGenerator", "afterGenerator", "branchAdded", "publicBranchAdded",
                  "checkedBeforeMembership", "checkedAdded", "beforeAuxCache", "afterAuxCache"):
        assert observed[0][field] == stock[field], field
    (work / "replay-observation.json").write_text(json.dumps(observed[0], indent=2) + "\n")
    def render_payload(payload):
        base = render(report)
        old = json.dumps(report["environmentActions"][0]["declaration"], ensure_ascii=False)
        new = json.dumps(json.dumps(payload, separators=(",", ":")), ensure_ascii=False)
        assert base.count(old) == 1
        return base.replace(old, new)

    if not args.positive_only:
        wire_checks = []
        wire.validate_realization_payload(action["declaration"], action["nameParts"], "sequence-positive")
        wire_checks.append("valid")
        wire_mutations = [
            ("integer-mode", lambda p: p[11].__setitem__(0, 1)),
            ("unknown-step", lambda p: p[12].append(["unknown", 0])),
            ("forward-child", lambda p: p[10][0][4].append(0)),
            ("missing-root", lambda p: p[12].pop(0)),
            ("duplicate-root", lambda p: p[12].append(copy.deepcopy(p[12][0]))),
            ("wrong-header-arity", lambda p: p.append(None)),
        ]
        for label, mutate in wire_mutations:
            value = copy.deepcopy(payload); mutate(value)
            try:
                wire.validate_realization_payload(json.dumps(value), action["nameParts"], label)
            except RuntimeError:
                wire_checks.append(label)
            else:
                raise AssertionError("wire mutation accepted: " + label)
        (work / "wire-checks.json").write_text(json.dumps(wire_checks, indent=2) + "\n")
        mutations = [
            ("swapped-roots", lambda p: p[12].reverse(), "boundary_sequence_"),
            ("missing-root", lambda p: p[12].pop(0), "boundary_sequence_"),
            ("flipped-mode", lambda p: p[11].__setitem__(0, not p[11][0]), "boundary_sequence_"),
            ("duplicate-root", lambda p: p[12].append(copy.deepcopy(p[12][0])), "boundary_sequence_"),
            ("final-descriptor", lambda p: p[10][-1][5][4][-1][1][0][1].append(p[10][-1][2]),
             "boundary_realization_cached_descriptor_conflict"),
        ]
        for label, mutate, expected in mutations:
            payload = json.loads(report["environmentActions"][0]["declaration"])
            mutate(payload)
            # Renderer validates wire first; direct malformed evidence is routed
            # through the same Lean syntax by replacing only its quoted payload.
            run(label, render_payload(payload), expected=expected)
        if args.case == "control":
            payload = json.loads(report["environmentActions"][0]["declaration"])
            registration = next(x for x in payload[12] if x[0] == "registration")
            assert [x[0] for x in payload[12]] == ["group", "registration", "helper"]
            missing_helper = copy.deepcopy(payload); missing_helper[12].pop()
            run("missing-helper", render_payload(missing_helper), expected="boundary_sequence_cover_or_delta")
            duplicate_registration = copy.deepcopy(payload)
            duplicate_registration[12].insert(1, copy.deepcopy(registration))
            run("duplicate-registration", render_payload(duplicate_registration),
                expected="boundary_sequence_registration_overlap")
            nonactive = copy.deepcopy(payload)
            name = [["s", "Bind"], ["s", "kleisliRight"], ["s", "eq_1"]]
            part = json.loads(nonactive[12][1][2])
            part[1], part[2], part[3][1] = name[:-1], name, name
            nonactive[12][1][1] = name
            nonactive[12][1][2] = json.dumps(part, separators=(",", ":"))
            for entry in nonactive[7]:
                if entry[0] == [["s", "id"], ["s", "eq_1"]]:
                    entry[:] = [name, name[:-1]]
            text = render_payload(nonactive)
            line = indent + 'observe_mixed_sequence "target"\n'
            text = text.replace(line, indent + 'mutate_mixed_state "assert-nonactive"\n' + line)
            run("nonactive-registration", text, expected="boundary_sequence_registration_not_active_import")
            early = copy.deepcopy(payload)
            early[12][0], early[12][1] = early[12][1], early[12][0]
            early_output, early_nonce = run("registration-before-activation", render_payload(early))
            early_obs = protocol.parse_framed_json_lines(early_output, marker=MARKER,
                expected_nonce=early_nonce, label="commuted registration")
            for field in ("beforeGenerator", "afterGenerator", "branchAdded", "publicBranchAdded",
                          "checkedAdded", "beforeAuxCache", "afterAuxCache"):
                assert early_obs[0][field] == stock[field], field
            late = copy.deepcopy(payload)
            late[12][1], late[12][2] = late[12][2], late[12][1]
            run("registration-after-helper", render_payload(late), expected="boundary_sequence_helper_equation_snapshot")
            for label, change in [
                ("registration-tag", lambda r: r.__setitem__(4, not r[4])),
                ("registration-owner", lambda r: r.__setitem__(1, [["s", "Nat"]])),
                ("registration-type", lambda r: r[3].__setitem__(3, '["expr_struct_dag_v1",[["s",["z"]]],0]')),
            ]:
                value = copy.deepcopy(payload)
                part = json.loads(value[12][1][2]); change(part)
                value[12][1][2] = json.dumps(part, separators=(",", ":"))
                run(label, render_payload(value), expected="boundary_sequence_registration_")
            changed = copy.deepcopy(payload)
            target = next(x for x in changed[7] if x[0] == [["s", "id"], ["s", "eq_1"]])
            target[1] = [["s", "Nat"]]
            run("registration-final-mapping", render_payload(changed), expected="boundary_sequence_caller_after:equations")
        mutations = [("cache-absent", "activation_cache_absent"),
                     ("cache-wrong-type", "activation_cache_type"),
                     ("cache-pending", "activation_cache_pending")]
        if args.case == "control":
            mutations += [("raw-axiom", "boundary_sequence_registration_not_original_theorem"),
                          ("changed-kind", "boundary_sequence_registration_not_original_theorem"),
                          ("registration-collision", "boundary_sequence_caller_before")]
        for label, expected in mutations:
            text = render(report)
            line = indent + 'observe_mixed_sequence "target"\n'
            assert text.count(line) == 1
            if label == "cache-pending":
                text = text.replace(line, indent + 'with_pending_mixed observe_mixed_sequence "target"\n')
            else:
                text = text.replace(line, indent + "mutate_mixed_state " + json.dumps(label) + "\n" + line)
            run(label, text, expected=expected)
    after = recursive.input_hashes()
    after[str(original_path.resolve())] = hashlib.sha256(original_path.read_bytes()).hexdigest()
    assert inputs == after, "source/runtime changed during controls"
    (work / "inputs-after.json").write_text(json.dumps(after, indent=2) + "\n")
    result = dict(kind="mixed-original-source-controls", case=args.case, artifactSchema=protocol.ARTIFACT_SCHEMA,
                  reportSchema=materializer.REPORT_SCHEMA, acceptedCampaignCoverage=False,
                  runs=runs, inputsBefore=inputs, inputsAfter=after,
                  hashes={str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in work.rglob("*") if p.is_file()})
    (work / "report.json").write_text(json.dumps(result, indent=2) + "\n")
    print(work / "report.json", flush=True)


PROBE = '\npublic meta import ExplicitLean.SimpEngine.Boundary\nimport all ExplicitLean.SimpEngine.Boundary.RealizationCodec\nimport all Lean.Environment\nimport all Lean.Meta.Basic\nimport all Lean.OriginalConstKind\nopen Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary in\nelab "observe_mixed_sequence " label:str inner:tactic : tactic => do\n  let before ← getEnv\n  let checkedBefore := before.constants.foldStage2\n    (fun names name _ => names.insert name) ({} : NameSet)\n  let genBefore ← getDeclNGen\n  evalTactic inner\n  let after ← getEnv\n  let genAfter ← getDeclNGen\n  discard <| IO.wait after.checked\n  let added ← branchDelta before after\n  let publicAdded ← branchDelta before after true\n  let groups ← candidateGroups after\n  let checkedAdded := after.constants.foldStage2\n    (fun names name _ => if checkedBefore.contains name then names else names.push name)\n    (#[] : Array Name)\n  let mut diagnostics := #[]\n  for group in groups do\n    diagnostics := diagnostics.push <| Json.mkObj [\n      ("owner", toJson group.owner.toString), ("key", toJson group.key.toString),\n      ("members", toJson (group.members.map Name.toString)),\n      ("publicMembers", toJson (group.publicMembers.map Name.toString))]\n  let genJson := fun (g : DeclNameGenerator) => Json.mkObj [\n    ("namePrefix", encodeBoundaryName g.namePrefix), ("idx", toJson g.idx),\n    ("parentIdxs", toJson g.parentIdxs)]\n  let mut declarations := #[]\n  for name in checkedAdded do\n    let some info := after.constants.find? name | throwError "missing checked declaration"\n    declarations := declarations.push <| Json.mkObj [\n      ("name", toJson name.toString),\n      ("type", toJson (← encodeBoundaryExpr info.type)),\n      ("body", toJson (← info.value?.mapM fun value => encodeBoundaryExpr value))]\n  let auxJson := fun (env : Environment) => (auxLemmasExt.getState env).lemmas.toArray.map fun (key, value) =>\n    Json.mkObj [("name", toJson value.1.toString), ("type", toJson (reprStr key.type)),\n      ("isPrivate", toJson key.isPrivate), ("defeq", toJson key.defeq)]\n  let report := Json.mkObj [\n    ("label", toJson label.getString), ("module", toJson before.mainModule.toString),\n    ("beforeGenerator", genJson genBefore), ("afterGenerator", genJson genAfter),\n    ("branchAdded", toJson (added.map Name.toString)),\n    ("publicBranchAdded", toJson (publicAdded.map Name.toString)),\n    ("checkedBeforeMembership", toJson (added.map checkedBefore.contains)),\n    ("checkedAdded", toJson (checkedAdded.map Name.toString)),\n    ("checkedDeclarations", .arr declarations), ("groups", .arr diagnostics),\n    ("beforeAuxCache", .arr (auxJson before)), ("afterAuxCache", .arr (auxJson after))]\n  let some nonce ← IO.getEnv "SIMP_ENGINE_BOUNDARY_RUN_NONCE" | throwError "missing diagnostic nonce"\n  IO.println s!"\\nMIXED_STOCK {nonce} {report.compress}"\n'

if __name__ == "__main__":
    main()
