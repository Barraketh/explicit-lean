#!/usr/bin/env python3
"""Fresh-process ordinary theorem capture, state isolation, and routing controls."""
from pathlib import Path
import copy
import hashlib
import json
import tempfile

import boundary_protocol as protocol
import check_simp_engine_boundary_source as source

ROOT = Path(__file__).resolve().parents[1]
MODULE = 'Experiment.LocalTheoremFixture'
OCCURRENCE = 'local-theorem-test'
CALL = 'simp_engine_boundary_record "local-theorem-test" (disch := make_helpers) only [hpq]'
TEMPLATE = '''module
public import Lean
public meta import ExplicitLean.SimpEngine.Boundary
open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary

elab "make_helpers" : tactic => withMainContext do
  let first ← withExporting (isExporting := PUBLIC) <|
    mkAuxLemma [] (mkConst ``True) (mkConst ``True.intro)
      (forceExpose := EXPOSE) (defeq := TAGGED)
  if SECOND then
    let type := mkApp2 (mkConst ``And) (mkConst ``True) (mkConst ``True)
    let value := mkApp4 (mkConst ``And.intro) (mkConst ``True) (mkConst ``True)
      (mkConst first) (mkConst first)
    discard <| withExporting (isExporting := PUBLIC) <| mkAuxLemma [] type value
  IO.println "STOCK_HELPER_CREATION"
  evalTactic (← `(tactic| assumption))

elab "inspect_helpers" : tactic => do
  let env ← getEnv
  let key : AuxLemmaKey := {type := mkConst ``True, isPrivate := !PUBLIC, defeq := TAGGED}
  let some (first, _) := (auxLemmasExt.getState env).lemmas.find? key
    | throwError "continuation missing first helper cache"
  let some (.thmInfo info) := (env.setExporting false).find? first (skipRealize := true)
    | throwError "continuation missing first helper theorem"
  unless info.value == mkConst ``True.intro do throwError "continuation changed raw first body"
  unless ((env.setExporting true).find? first (skipRealize := true)).any (fun info =>
      match info with | .thmInfo _ => true | _ => false) == (PUBLIC && EXPOSE) do
    throwError "continuation changed exported theorem body"
  unless defeqAttr.hasTag env first == TAGGED do throwError "continuation changed tag"
  if SECOND then
    let type := mkApp2 (mkConst ``And) (mkConst ``True) (mkConst ``True)
    let key : AuxLemmaKey := {type, isPrivate := !PUBLIC, defeq := false}
    let some (second, _) := (auxLemmasExt.getState env).lemmas.find? key
      | throwError "continuation missing second helper cache"
    let some (.thmInfo info) := (env.setExporting false).find? second (skipRealize := true)
      | throwError "continuation missing second helper theorem"
    unless info.value == mkApp4 (mkConst ``And.intro) (mkConst ``True) (mkConst ``True)
        (mkConst first) (mkConst first) do throwError "continuation inlined helper body"
  let reused ← withExporting (isExporting := PUBLIC) <|
    mkAuxLemma [] (mkConst ``True) (mkConst ``True.intro) (defeq := TAGGED)
  unless reused == first do throwError "continuation failed to reuse helper"
  let next ← withExporting (isExporting := true) <|
    mkAuxLemma [] (mkApp2 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat) (mkNatLit 7) |>.app (mkNatLit 7))
      (mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) (mkNatLit 7))
  let gen ← getDeclNGen
  IO.println s!"HELPER_CONTINUATION {first} {next} {gen.namePrefix}/{gen.idx}/{gen.parentIdxs}"

public theorem sample (p q : Prop) (h : p) (hpq : p → q) : q := by
  first
  | CALL
  | exact hpq h
  inspect_helpers
'''


def main():
    parent = ROOT / '.lake/aux-name-state'
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix='helper-controls-', dir=parent))
    print(work, flush=True)
    dylib = source.query_json_string(source.run(['lake', 'query', 'ExplicitLean:shared', '--json']), 'shared')
    records = []

    def compile_case(label, text, recording=False, abort=None):
        path = work / label / 'Experiment/LocalTheoremFixture.lean'
        path.parent.mkdir(parents=True)
        path.write_text(text)
        env, nonce = protocol.recording_subprocess_environment() if recording else protocol.replay_subprocess_environment()
        try:
            output = source.compile_source(dylib, path, env=env)
        except RuntimeError as error:
            path.with_suffix('.log').write_text(str(error))
            raise
        log = path.with_suffix('.log'); log.write_text(output)
        records.append({'label': label, 'source': str(path), 'sourceSha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'log': str(log), 'logSha256': hashlib.sha256(log.read_bytes()).hexdigest(), 'nonce': nonce,
            'compilerExit': 0, 'expectedAbort': abort})
        checker = protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers
        try:
            checker(output, expected_nonce=nonce)
        except RuntimeError as error:
            if abort is None or abort not in str(error): raise
        else:
            if abort is not None: raise RuntimeError(f'{label}: expected abort absent')
        reports = protocol.parse_framed_json_lines(output, marker=source.ARTIFACT_MARKER,
            expected_nonce=nonce, label='helper artifact')
        if abort and reports: raise RuntimeError(f'{label}: rejected execution emitted artifacts')
        print(f'local theorem control {label}: passed', flush=True)
        return reports, output

    positive = {}
    for label, public, expose, second, tagged in [
        ('private', False, False, False, False), ('public', True, False, False, False),
        ('exposed', True, True, False, False), ('topological', False, False, True, True)]:
        text = TEMPLATE.replace('PUBLIC', str(public).lower()).replace('EXPOSE', str(expose).lower())
        text = text.replace('SECOND', str(second).lower()).replace('TAGGED', str(tagged).lower()).replace('CALL', CALL)
        reports, recorded = compile_case(label + '-record', text, recording=True)
        assert len(reports) == 1 and reports[0]['status'] == 'success'
        protocol.validate_report(reports[0], OCCURRENCE, MODULE)
        assert [a['kind'] for a in reports[0]['environmentActions']] == ['declare_local_theorems']
        replacement = source.preserve_original_call(source.format_report_variants(reports, '    '),
            'simp (disch := make_helpers) only [hpq]', '    ')
        applied = text.replace('public meta import ExplicitLean.SimpEngine.Boundary\n',
            'public meta import ExplicitLean.SimpEngine.Boundary.Tactic\n').replace(CALL, replacement)
        _, replayed = compile_case(label + '-replay', applied)
        _, original = compile_case(label + '-original', text.replace(CALL, 'simp (disch := make_helpers) only [hpq]'))
        observations = [next(line for line in out.splitlines() if line.startswith('HELPER_CONTINUATION '))
                        for out in [recorded, replayed, original]]
        assert len(set(observations)) == 1, observations
        assert 'STOCK_HELPER_CREATION' not in replayed
        positive[label] = (text, applied, reports)

    # A computation helper is still unsupported; caught failures cannot hide it.
    text = positive['private'][0].replace('  IO.println "STOCK_HELPER_CREATION"', '''  addDecl <| .defnDecl {
    name := mkPrivateNameCore (← getEnv).mainModule `sample.extraComputation,
    levelParams := [], type := mkConst ``Nat, value := mkNatLit 2,
    hints := .abbrev, safety := .safe }
  IO.println "STOCK_HELPER_CREATION"''').replace('  inspect_helpers\n', '')
    compile_case('unsupported-computation', text, recording=True,
                 abort='boundary_comparison_unsupported_environment_delta')

    # No declaration accounts for this stock naming effect: strict comparator
    # must reject it rather than resetting a counter to make replay succeed.
    start = TEMPLATE.index('  let first ←')
    end = TEMPLATE.index('\nelab "inspect_helpers"')
    text = TEMPLATE[:start] + '''  let gen ← getDeclNGen
  setDeclNGen {gen with idx := gen.idx + 1}
  evalTactic (← `(tactic| assumption))
''' + TEMPLATE[end:]
    text = text[:text.index('elab "inspect_helpers"')] + TEMPLATE[TEMPLATE.index('public theorem sample'):]
    text = text.replace('CALL', CALL).replace('  inspect_helpers\n', '')
    compile_case('uncaptured-counter-effect', text, recording=True, abort='core.auxDeclNGen')
    failed = text.replace('evalTactic (← `(tactic| assumption))', 'throwError "deliberate discharge failure"')
    failed = failed.replace('(disch := make_helpers)', '+failIfUnchanged (disch := make_helpers)')
    compile_case('failed-stock-counter-effect', failed, recording=True,
                 abort='boundary_stock_failure_aux_decl_name_effect_unsupported')

    # Pure wire negatives and cached canonical-body/metadata checks.
    _, applied, reports = positive['private']
    action = reports[0]['environmentActions'][0]
    original_bundle = json.loads(action['declaration'])
    mutations = []
    bundle = copy.deepcopy(original_bundle); bundle[2] = []; mutations.append(('empty', bundle))
    bundle = copy.deepcopy(original_bundle); bundle[2].append(copy.deepcopy(bundle[2][0])); mutations.append(('duplicate', bundle))
    bundle = copy.deepcopy(original_bundle); thm = json.loads(bundle[2][0][1]); thm[1] = not thm[1]
    bundle[2][0][1] = json.dumps(thm); mutations.append(('privacy', bundle))
    for label, bundle in mutations:
        payload = json.dumps(bundle, separators=(',', ':'))
        try: protocol.validate_environment_actions([{**action, 'declaration': payload}], label)
        except RuntimeError: pass
        else: raise RuntimeError(f'wire accepted {label}')
        changed = applied.replace(source.lean_string(action['declaration']), source.lean_string(payload))
        changed = changed.replace('  inspect_helpers\n', '')
        compile_case('invalid-' + label, changed, abort='boundary_local_theorem')

    # A different closed proof of True is kernel-valid but cannot replace an
    # already captured helper body. Check cached bodies/tags/cache/exposure.
    changed_body = copy.deepcopy(original_bundle)
    helper = json.loads(changed_body[2][0][1]); theorem = json.loads(helper[3])
    theorem[5] = json.dumps(["expr_dag_v1", [
        ["c", [["s", "True"]], []], ["c", [["s", "True"], ["s", "intro"]], []],
        ["c", [["s", "id"]], [["z"]]], ["a", 2, 0], ["a", 3, 1]], 4], separators=(",", ":"))
    helper[3] = json.dumps(theorem, separators=(",", ":")); changed_body[2][0][1] = json.dumps(helper, separators=(",", ":"))
    cached = [("body", changed_body, "existing_declaration_conflict")]
    for label, change, detail in [
        ("tag", lambda h: h.__setitem__(4, not h[4]), "tag_conflict"),
        ("export", lambda h: h.__setitem__(2, "axiom"), "exported_kind_conflict"),
        ("cache", lambda h: h[6].__setitem__(3, [[["s", "foreignPrevious"]], []]), "cache_state_conflict")]:
        bundle = copy.deepcopy(original_bundle); helper = json.loads(bundle[2][0][1]); change(helper)
        bundle[2][0][1] = json.dumps(helper, separators=(",", ":")); cached.append((label, bundle, detail))
    # The cache corruption needs an absent key to prevent the explicitly allowed
    # idempotent cache hit from ignoring an irrelevant old-state precondition.
    helper = json.loads(cached[-1][1][2][0][1]); helper[6][2] = not helper[6][2]
    cached[-1][1][2][0][1] = json.dumps(helper, separators=(",", ":"))
    code = """module
public import Lean
public meta import ExplicitLean.SimpEngine.Boundary.Tactic
open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary
elab "cached_checks" : tactic => do
  let name ← ofExcept <| decodeBoundaryName (← ofExcept <| Json.parse NAME)
  let saved ← Tactic.saveState
  executeBoundaryLocalTheorems name DIFFERENT
  saved.restore
  executeBoundaryLocalTheorems name ORIGINAL
CHECKS
  IO.println "CANONICAL_CACHE_CONTROLS body=true tag=true exposure=true cache=true"
public theorem sample : True := by
  cached_checks
  exact True.intro
"""
    checks = []
    for label, bundle, detail in cached:
        payload = json.dumps(bundle, separators=(",", ":"))
        protocol.validate_environment_actions([{**action, 'declaration': payload}], label)
        checks.append('  let rejected ← try\n    executeBoundaryLocalTheorems name ' + source.lean_string(payload) +
                      '\n    pure false\n  catch error =>\n    unless (← error.toMessageData.toString).contains ' +
                      source.lean_string(detail) + ' do throw error\n    pure true\n  unless rejected do throwError ' +
                      source.lean_string('cached ' + label + ' mutation accepted'))
    code = code.replace('NAME', source.lean_string(json.dumps(action['nameParts'])))
    code = code.replace('DIFFERENT', source.lean_string(json.dumps(changed_body, separators=(",", ":"))))
    code = code.replace('ORIGINAL', source.lean_string(action['declaration'])).replace('CHECKS', '\n'.join(checks))
    compile_case('cached-canonical-controls', code)

    (work / 'report.json').write_text(json.dumps({'kind': 'ordinary_local_theorem_regression',
        'status': 'passed', 'records': records}, indent=2) + '\n')
    print(work / 'report.json', flush=True)


if __name__ == '__main__':
    main()
