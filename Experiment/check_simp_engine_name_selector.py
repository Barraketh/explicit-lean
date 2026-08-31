#!/usr/bin/env python3
"""Exact generator selector fields, two-state routing, and caught misses."""
from pathlib import Path
import hashlib
import json
import tempfile

import boundary_protocol as protocol
import check_simp_engine_boundary_source as source

ROOT = Path(__file__).resolve().parents[1]
CALL = 'simp_engine_boundary_record "generator-routing" only'
FIXTURE = '''module
public import Lean
public meta import ExplicitLean.SimpEngine.Boundary
open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary

elab "dual_route" : tactic => do
  let saved ← Tactic.saveState
  let generator ← getDeclNGen
  let action : TacticM Unit := do
    try
      evalTactic (← `(tactic| CALL))
    catch _ =>
      evalTactic (← `(tactic| exact True.intro))
  action
  saved.restore
  setDeclNGen {generator with idx := generator.idx + 1}
  action
  IO.println "ROUTING_DONE"

public theorem sample : True := by dual_route
'''
UNIT = '''module
public import Lean
public meta import ExplicitLean.SimpEngine.Boundary.Selector
open Lean Meta ExplicitLean.SimpEngine.Boundary
run_meta do
  let goal ← mkFreshExprMVar (mkConst ``True)
  let original ← getDeclNGen
  let base := { original with namePrefix := .str `same "1", idx := 3, parentIdxs := [5, 7] }
  setDeclNGen base
  let before ← boundaryProofStateFingerprint [goal.mvarId!]
  for changed in #[{base with namePrefix := .num `same 1}, {base with idx := 4},
      {base with parentIdxs := [7, 5]}, {base with parentIdxs := [5, 7, 0]}] do
    setDeclNGen changed
    let after ← boundaryProofStateFingerprint [goal.mvarId!]
    unless before.targetFingerprint == after.targetFingerprint &&
        before.localContextFingerprint == after.localContextFingerprint &&
        before.goalCount == after.goalCount &&
        before.metavariableContextFingerprint != after.metavariableContextFingerprint do
      throwError "generator change did not change only routing state"
    let current ← getDeclNGen
    unless current.namePrefix == changed.namePrefix && current.idx == changed.idx &&
        current.parentIdxs == changed.parentIdxs do throwError "selector changed generator"
  setDeclNGen base
  unless (← boundaryProofStateFingerprint [goal.mvarId!]) == before do
    throwError "restored generator selector not stable"
  setDeclNGen original
  IO.println "GENERATOR_SELECTOR_UNIT fourMutations=true observational=true"
'''


def main():
    parent = ROOT / '.lake/aux-name-state'; parent.mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix='selector-controls-', dir=parent))
    print(work, flush=True)
    dylib = source.query_json_string(source.run(['lake', 'query', 'ExplicitLean:shared', '--json']), 'shared')
    records = []
    def compile_case(label, text, recording=False, abort=None):
        path = work / label / 'Experiment/NameSelectorFixture.lean'; path.parent.mkdir(parents=True)
        path.write_text(text)
        env, nonce = protocol.recording_subprocess_environment() if recording else protocol.replay_subprocess_environment()
        try: out = source.compile_source(dylib, path, env=env)
        except RuntimeError as error:
            path.with_suffix('.log').write_text(str(error)); raise
        log = path.with_suffix('.log'); log.write_text(out)
        records.append({'label': label, 'source': str(path), 'sourceSha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'log': str(log), 'logSha256': hashlib.sha256(log.read_bytes()).hexdigest(), 'nonce': nonce,
            'compilerExit': 0, 'expectedAbort': abort})
        checker = protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers
        try: checker(out, expected_nonce=nonce)
        except RuntimeError as error:
            if abort is None or abort not in str(error): raise
        else:
            if abort: raise RuntimeError('caught selector miss was accepted')
        reports = protocol.parse_framed_json_lines(out, marker=source.ARTIFACT_MARKER, expected_nonce=nonce, label='selector artifact')
        print(label + ': passed', flush=True)
        return reports
    compile_case('unit', UNIT)
    text = FIXTURE.replace('CALL', CALL)
    reports = compile_case('record-two-states', text, recording=True)
    assert len(reports) == 2
    for report in reports: protocol.validate_report(report, 'generator-routing', 'Experiment.NameSelectorFixture')
    assert reports[0]['selector']['caller'] == reports[1]['selector']['caller']
    assert reports[0]['selector']['options'] == reports[1]['selector']['options']
    assert protocol.selector_key(reports[0]) != protocol.selector_key(reports[1])
    for field in ['targetFingerprint', 'localContextFingerprint', 'goalCount']:
        assert reports[0]['selector']['preState'][field] == reports[1]['selector']['preState'][field]
    replacement = source.preserve_original_call(source.format_report_variants(reports, '      '), 'simp only', '      ')
    applied = text.replace('public meta import ExplicitLean.SimpEngine.Boundary\n', 'public meta import ExplicitLean.SimpEngine.Boundary.Tactic\n')
    applied = applied.replace(CALL, replacement)
    compile_case('replay-two-states', applied)
    compile_case('caught-third-state', applied.replace('generator.idx + 1', 'generator.idx + 2'),
                 abort='boundary_variant_missing')
    old = json.loads(json.dumps(reports[0])); old['selector']['selectorSchema'] = 1
    try: protocol.validate_report(old, 'generator-routing')
    except RuntimeError: pass
    else: raise RuntimeError('legacy selector schema was accepted')
    (work / 'report.json').write_text(json.dumps({'kind': 'decl_name_generator_selector_controls',
        'status': 'passed', 'records': records}, indent=2) + '\n')
    print(work / 'report.json', flush=True)


if __name__ == '__main__': main()
