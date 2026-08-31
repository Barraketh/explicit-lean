#!/usr/bin/env python3
"""Fresh-process and cache-hit checks for captured public theorem effects."""
from pathlib import Path
import hashlib
import json
import subprocess
import tempfile

from process_runner import run_process

ROOT = Path(__file__).resolve().parents[1]
PRELUDE = '''module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary.PublicTheoremCodec
open Lean Meta Elab Command ExplicitLean.SimpEngine.Boundary
'''


def main() -> None:
    parent = ROOT / '.lake/public-theorem-codec'
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix='fixture-', dir=parent))
    payload = work / 'payload.json'
    prior_payload = work / 'prior-payload.json'
    tagged_payload = work / 'tagged-payload.json'
    rows = []

    def compile_case(label: str, body: str, expected: str | None = None) -> None:
        path = work / label / 'Experiment/PublicTheoremCodec.lean'
        path.parent.mkdir(parents=True)
        path.write_text(PRELUDE + body)
        result = run_process(['lake', 'env', 'lean', '-R', str(path.parent.parent), str(path)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
        log = path.with_suffix('.log'); log.write_text(result.stdout)
        if expected is None:
            if result.returncode or 'PUBLIC_THEOREM_CODEC_OK' not in result.stdout:
                raise RuntimeError(f'{label}: {result.stdout}')
        elif result.returncode == 0 or expected not in result.stdout:
            raise RuntimeError(f'{label}: expected {expected}: {result.stdout}')
        rows.append({'case': label, 'exitCode': result.returncode, 'expectedError': expected,
            'source': str(path), 'sourceSha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'log': str(log), 'logSha256': hashlib.sha256(log.read_bytes()).hexdigest()})

    compile_case('capture', f'''run_cmd liftTermElabM do
  let before ← getEnv
  let name ← withDeclNameForAuxNaming `publicCodecSample <| withExporting (isExporting := true) <|
    mkAuxLemma [] (mkConst ``True) (mkConst ``True.intro) (kind? := `_simp)
  unless name == `publicCodecSample._simp_1 && !isPrivateName name do
    throwError "unexpected public auxiliary name"
  let some (.thmInfo thm) := (← getEnv).find? name | throwError "missing captured theorem"
  let encoded ← encodeBoundaryPublicTheorem before thm
  IO.FS.writeFile {json.dumps(str(payload))} encoded
  IO.println "PUBLIC_THEOREM_CODEC_OK"
''')

    source = payload.read_text()
    replay = f'''run_cmd liftTermElabM do
  let before ← getEnv
  let source := {json.dumps(source)}
  unless !before.containsOnBranch `publicCodecSample._simp_1 do
    throwError "replay is not fresh"
  executeBoundaryPublicTheorem `publicCodecSample._simp_1 source
  let some (.thmInfo thm) := (← getEnv).find? `publicCodecSample._simp_1
    | throwError "replayed theorem missing"
  unless (← encodeBoundaryPublicTheorem before thm) == source do
    throwError "captured public theorem or metadata changed"
  executeBoundaryPublicTheorem `publicCodecSample._simp_1 source
  let existing ← withDeclNameForAuxNaming `publicCodecSample <| withExporting (isExporting := true) <|
    mkAuxLemma [] (mkConst ``True) (mkConst ``True.intro) (kind? := `_simp)
  unless existing == `publicCodecSample._simp_1 do
    throwError "auxiliary cache was not restored"
  IO.println "PUBLIC_THEOREM_CODEC_OK"
'''
    compile_case('fresh-and-cached', replay)

    def negative(label, mutate, expected, *, cached=False, setup_text=''):
        data = json.loads(source); mutate(data)
        setup = setup_text
        if cached:
            setup += f'  executeBoundaryPublicTheorem `publicCodecSample._simp_1 {json.dumps(source)}\n'
        body = 'run_cmd liftTermElabM do\n' + setup
        body += f'  executeBoundaryPublicTheorem `publicCodecSample._simp_1 {json.dumps(json.dumps(data, separators=(",", ":")))}\n'
        compile_case(label, body, expected)

    def mutate_group(p):
        thm = json.loads(p[1])
        thm[2] = [[['s', 'foreign']]]
        p[1] = json.dumps(thm, separators=(',', ':'))

    negative('all-group-conflict', mutate_group,
        'boundary_public_theorem_unsupported_group')

    existing_value_setup = '''  let oldName := `publicCodecAlternative
  let old : TheoremVal := {
    name := oldName
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro
    all := [oldName]
  }
  addDecl (.thmDecl old)
  let expected := `publicCodecSample._simp_1
  let existing : TheoremVal := {
    name := expected
    levelParams := []
    type := mkConst ``True
    value := mkConst oldName
    all := [expected]
  }
  addDecl (.thmDecl existing)
'''
    negative('existing-value-conflict', lambda _p: None,
        'boundary_public_theorem_existing_declaration_conflict',
        setup_text=existing_value_setup)

    negative('cached-tag', lambda p: p.__setitem__(2, not p[2]),
        'boundary_public_theorem_tag_conflict', cached=True)
    negative('cache-before-conflict', lambda p: p[4].__setitem__(3, [[["s", "foreign"]], []]),
        'boundary_public_theorem_cache_state_conflict')
    negative('cache-type-conflict', lambda p: p[4].__setitem__(0,
        '["expr_dag_v1",[["c",[["s","False"]],[]]],0]'),
        'boundary_public_theorem_cache_type_conflict')
    def bad_proof(p):
        thm = json.loads(p[1]); thm[5] = '["expr_dag_v1",[["c",[["s","Nat"],["s","zero"]],[]]],0]'
        p[1] = json.dumps(thm, separators=(',', ':'))
    negative('invalid-proof', bad_proof, 'boundary_theorem_value_type_mismatch')

    tagged_capture = '''run_cmd liftTermElabM do
  let before ← getEnv
  let nat := mkConst ``Nat
  let zero := mkConst ``Nat.zero
  let type := mkApp3 (mkConst ``Eq [.succ .zero]) nat zero zero
  let value := mkApp2 (mkConst ``Eq.refl [.succ .zero]) nat zero
  let name ← withDeclNameForAuxNaming `publicCodecTagged <| withExporting (isExporting := true) <|
    mkAuxLemma [] type value (kind? := `_simp) (inferRfl := true)
  unless name == `publicCodecTagged._simp_1 do
    throwError "unexpected tagged auxiliary name"
  let env ← getEnv
  unless defeqAttr.hasTag env name && backwardDefeqAttr.hasTag env name do
    throwError "inferRfl did not install both defeq tags"
  let some (.thmInfo thm) := env.find? name | throwError "missing tagged theorem"
  let encoded ← encodeBoundaryPublicTheorem before thm
  IO.FS.writeFile __TAGGED_PATH__ encoded
  IO.println "PUBLIC_THEOREM_CODEC_OK"
'''.replace('__TAGGED_PATH__', json.dumps(str(tagged_payload)))
    compile_case('tagged-capture', tagged_capture)
    tagged_source = tagged_payload.read_text()
    tagged_replay = f'''run_cmd liftTermElabM do
  let before ← getEnv
  let source := {json.dumps(tagged_source)}
  unless !before.containsOnBranch `publicCodecTagged._simp_1 do
    throwError "tagged replay is not fresh"
  executeBoundaryPublicTheorem `publicCodecTagged._simp_1 source
  let env ← getEnv
  unless defeqAttr.hasTag env `publicCodecTagged._simp_1 &&
      backwardDefeqAttr.hasTag env `publicCodecTagged._simp_1 do
    throwError "tagged replay lost defeq metadata"
  let some (.thmInfo thm) := env.find? `publicCodecTagged._simp_1
    | throwError "replayed tagged theorem missing"
  unless (← encodeBoundaryPublicTheorem before thm) == source do
    throwError "tagged theorem re-encoding changed"
  IO.println "PUBLIC_THEOREM_CODEC_OK"
'''
    compile_case('tagged-replay', tagged_replay)

    prior_capture = '''run_cmd liftTermElabM do
  let oldName := `publicCodecPriorOld
  let unrelatedName := `publicCodecPriorUnrelated
  let old : TheoremVal := {
    name := oldName
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro
    all := [oldName]
  }
  let unrelated : TheoremVal := {
    name := unrelatedName
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro
    all := [unrelatedName]
  }
  addDecl (.thmDecl old)
  addDecl (.thmDecl unrelated)
  let priorKey : AuxLemmaKey := { type := mkConst ``True, isPrivate := false, defeq := false }
  let unrelatedKey : AuxLemmaKey := { type := mkConst ``Nat, isPrivate := false, defeq := false }
  modifyEnv fun env => auxLemmasExt.modifyState env fun state =>
    { state with lemmas := (state.lemmas.insert priorKey (oldName, [])).insert unrelatedKey (unrelatedName, []) }
  let before ← getEnv
  let name ← withDeclNameForAuxNaming `publicCodecPrior <| withExporting (isExporting := true) <|
    mkAuxLemma [] (mkConst ``True) (mkConst ``True.intro) (kind? := `_simp) (cache := false)
  unless name == `publicCodecPrior._simp_1 do
    throwError "unexpected prior-cache auxiliary name"
  let some (.thmInfo thm) := (← getEnv).find? name | throwError "missing prior-cache theorem"
  let encoded ← encodeBoundaryPublicTheorem before thm
  IO.FS.writeFile __PRIOR_PATH__ encoded
  IO.println "PUBLIC_THEOREM_CODEC_OK"
'''.replace('__PRIOR_PATH__', json.dumps(str(prior_payload)))
    compile_case('prior-cache-capture', prior_capture)
    prior_source = prior_payload.read_text()
    prior_replay = f'''run_cmd liftTermElabM do
  let oldName := `publicCodecPriorOld
  let unrelatedName := `publicCodecPriorUnrelated
  let old : TheoremVal := {{
    name := oldName
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro
    all := [oldName]
  }}
  let unrelated : TheoremVal := {{
    name := unrelatedName
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro
    all := [unrelatedName]
  }}
  addDecl (.thmDecl old)
  addDecl (.thmDecl unrelated)
  let priorKey : AuxLemmaKey := {{ type := mkConst ``True, isPrivate := false, defeq := false }}
  let unrelatedKey : AuxLemmaKey := {{ type := mkConst ``Nat, isPrivate := false, defeq := false }}
  modifyEnv fun env => auxLemmasExt.modifyState env fun state =>
    {{ state with lemmas := (state.lemmas.insert priorKey (oldName, [])).insert unrelatedKey (unrelatedName, []) }}
  let before ← getEnv
  let source := {json.dumps(prior_source)}
  unless !before.containsOnBranch `publicCodecPrior._simp_1 do
    throwError "prior-cache replay is not fresh"
  executeBoundaryPublicTheorem `publicCodecPrior._simp_1 source
  let env ← getEnv
  unless env.find? `publicCodecPrior._simp_1 |>.isSome do
    throwError "prior-cache theorem missing"
  unless (auxLemmasExt.getState env).lemmas.find? priorKey ==
      some (`publicCodecPrior._simp_1, []) do
    throwError "prior cache was not replaced by replayed theorem"
  unless (auxLemmasExt.getState env).lemmas.find? unrelatedKey ==
      some (unrelatedName, []) do
    throwError "unrelated cache entry was not preserved"
  let some (.thmInfo thm) := env.find? `publicCodecPrior._simp_1
    | throwError "prior-cache theorem info missing"
  unless (← encodeBoundaryPublicTheorem before thm) == source do
    throwError "prior-cache replay changed theorem or prior state"
  IO.println "PUBLIC_THEOREM_CODEC_OK"
'''
    compile_case('prior-cache-replay', prior_replay)

    report = {'kind': 'public_theorem_codec_check', 'status': 'passed', 'cases': rows,
        'payload': str(payload), 'payloadSha256': hashlib.sha256(payload.read_bytes()).hexdigest(),
        'additionalPayloads': [
            {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            for path in [prior_payload, tagged_payload]],
        'productionIntegrated': False,
        'limitations': [
            'Fresh forged defeq tags are intentionally not treated as a codec '
            'failure: callers must authenticate capture and run the independent '
            'full Boundary comparison; this codec does not infer or validate tags.'
        ],
        'implementation': [{'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            for path in [ROOT / 'ExplicitLean/SimpEngine/Boundary/PublicTheoremCodec.lean',
                         ROOT / 'ExplicitLean/SimpEngine/Boundary/DeclarationCodec.lean',
                         ROOT / 'Experiment/check_simp_engine_public_theorem_codec.py']]}
    (work / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
