#!/usr/bin/env python3
"""Distinguish pre-existing checked declarations from actual tactic effects."""
from pathlib import Path
import hashlib
import json
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'Experiment'))
import boundary_protocol as protocol
import check_simp_engine_boundary_source as source
import check_simp_engine_private_declarations as private

ARTIFACT_ROOT = ROOT / '.lake/week-2026-08-31/checked-delta'
ARTIFACT_ROOT.mkdir(parents=True, exist_ok=True)
WORK = Path(tempfile.mkdtemp(prefix='fixture-', dir=ARTIFACT_ROOT))
DYLIB = source.query_json_string(
    source.run(['lake', 'query', 'ExplicitLean:shared', '--json']), 'shared query')
results = {}

def compile_phase(label, text, module, *, recording=True):
    path = WORK / label / (module.replace('.', '/') + '.lean')
    path.parent.mkdir(parents=True)
    path.write_text(text)
    env, nonce = protocol.recording_subprocess_environment() if recording else protocol.replay_subprocess_environment()
    output = source.compile_source(DYLIB, path, env=env)
    log = path.with_suffix('.log')
    log.write_text(output)
    results[label] = {'source': str(path), 'sourceSha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'log': str(log), 'logSha256': hashlib.sha256(log.read_bytes()).hexdigest(), 'nonce': nonce}
    return output, nonce

module = 'Experiment.PriorChecked'
text = '''module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary
public section
open Lean Meta Elab Tactic
@[expose] def priorAlias (n : Nat) : Nat := n
theorem warmup (n : Nat) : priorAlias n = n := by simp only [priorAlias]
elab "prior_view" : tactic => do
  let env ← getEnv
  let name := `priorAlias.eq_1
  IO.println s!"PRIOR_CHECKED checked={env.constants.contains name} branch={env.containsOnBranch name} default={env.contains name}"
theorem sample (n : Nat) : n + 0 = n := by
  prior_view
  simp_engine_boundary_record "prior-checked" only [Nat.add_zero]
'''
output, nonce = compile_phase('prior-checked-recorded', text, module)
protocol.check_recording_abort_markers(output, expected_nonce=nonce, expected_module=module)
assert 'PRIOR_CHECKED checked=true branch=false default=false' in output
reports = protocol.parse_framed_json_lines(output, marker=source.ARTIFACT_MARKER, expected_nonce=nonce, label='boundary artifact')
assert len(reports) == 1
protocol.validate_report(reports[0], 'prior-checked', module)
assert reports[0]['environmentActions'] == []
replacement = source.preserve_original_call(source.format_report_variants(reports, '    '), 'simp only [Nat.add_zero]', '    ')
applied = text.replace('public meta import ExplicitLean.SimpEngine.Boundary\n', 'public meta import ExplicitLean.SimpEngine.Boundary.Tactic\n')
applied = applied.replace('simp_engine_boundary_record "prior-checked" only [Nat.add_zero]', replacement)
output, nonce = compile_phase('prior-checked-applied', applied, module, recording=False)
protocol.check_replay_abort_markers(output, expected_nonce=nonce, expected_module=module)
assert 'PRIOR_CHECKED checked=true branch=false default=false' in output
print('prior globally checked/off-branch declaration omitted from new delta: ok', flush=True)

module = 'Experiment.FreshEquation'
text = '''module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary
public section
@[expose] def freshAlias (n : Nat) : Nat := n
theorem freshEquation (n : Nat) : freshAlias n = n := by
  simp_engine_boundary_record "fresh-equation" only [freshAlias]
'''
output, nonce = compile_phase('equation-recorded', text, module)
protocol.check_recording_abort_markers(output, expected_nonce=nonce, expected_module=module)
reports = protocol.parse_framed_json_lines(output, marker=source.ARTIFACT_MARKER, expected_nonce=nonce, label='boundary artifact')
assert len(reports) == 1
protocol.validate_report(reports[0], 'fresh-equation', module)
assert [action['kind'] for action in reports[0]['environmentActions']] == ['declare_equation']
replacement = source.preserve_original_call(source.format_report_variants(reports, '    '), 'simp only [freshAlias]', '    ')
applied = text.replace('public meta import ExplicitLean.SimpEngine.Boundary\n', 'public meta import ExplicitLean.SimpEngine.Boundary.Tactic\n')
applied = applied.replace('simp_engine_boundary_record "fresh-equation" only [freshAlias]', replacement)
output, nonce = compile_phase('equation-applied', applied, module, recording=False)
protocol.check_replay_abort_markers(output, expected_nonce=nonce, expected_module=module)
print('fresh captured equation and separate-process replay: ok', flush=True)

module = private.MODULE
text = private.fixture(private=True)
text = text.replace('addDecl <| .thmDecl {\n    name, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }',
                    'addDecl <| .defnDecl {\n    name, levelParams := [], type := mkConst ``Nat, value := mkNatLit 7,\n    hints := .abbrev, safety := .safe, all := [name] }')
assert '.defnDecl' in text
output, nonce = compile_phase('fresh-private-computation', text, module)
reports = protocol.parse_framed_json_lines(output, marker=source.ARTIFACT_MARKER, expected_nonce=nonce, label='boundary artifact')
assert reports == []
try:
    protocol.check_recording_abort_markers(output, expected_nonce=nonce, expected_module=module, expected_occurrence='proof-declaration-test')
except RuntimeError as error:
    assert 'boundary_comparison_unsupported_environment_delta:_private.Experiment.SimpEnginePrivateDeclarations' in str(error), str(error)
else:
    raise AssertionError('fresh private computation silently omitted')
print('fresh private computation: caught compiler success, authenticated harness rejection: ok', flush=True)
(WORK / 'report.json').write_text(json.dumps(results, indent=2) + '\n')
print(WORK, flush=True)
