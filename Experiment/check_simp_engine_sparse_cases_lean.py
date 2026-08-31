from pathlib import Path
import shutil
import os, sys, json, hashlib, tempfile
DEFAULT_ROOT = Path(__file__).resolve().parents[1]
ROOT = Path(os.environ.get('EXPLICIT_LEAN_PROJECT_ROOT', str(DEFAULT_ROOT))).resolve()
sys.path.insert(0, str(ROOT / 'Experiment'))
from process_runner import run_process

EVIDENCE_DIR = ROOT / '.lake/sparse-probe'
EVIDENCE_DIR.mkdir(parents=True, exist_ok=True)
WORK = Path(tempfile.mkdtemp(prefix='sparse-cases-lean-', dir=EVIDENCE_DIR))
HEADER = '''module
import Mathlib.Init
import Batteries.Data.List.Basic
public meta import ExplicitLean.SimpEngine.Boundary.SparseCasesCodec
public meta import Lean.Meta.Match.MatchEqs
public meta import Lean.Meta.Constructions.SparseCasesOn
meta import all Lean.Meta.Constructions.SparseCasesOn
open Lean Meta Elab ExplicitLean.SimpEngine.Boundary
run_meta do
  __BODY__
'''
records = []
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def resolve_pinned_lean() -> Path:
    result = run_process(['lake', 'env', 'printenv', 'PATH'], cwd=ROOT,
                         text=True, capture_output=True, check=False, timeout=10)
    if result.returncode != 0:
        raise RuntimeError(f'could not resolve lake environment PATH: {result.stdout}{result.stderr}')
    for directory in result.stdout.strip().split(os.pathsep):
        candidate = Path(directory) / 'lean'
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate.resolve()
    raise RuntimeError('lake environment PATH has no executable lean')

LEAN = resolve_pinned_lean()

INPUTS = [
    ROOT / 'lean-toolchain',
    LEAN,
    ROOT / 'Experiment/boundary_expr_codec.py',
    ROOT / 'Experiment/process_runner.py',
    Path(__file__).resolve(),
    ROOT / 'ExplicitLean/SimpEngine/Boundary/ExprCodec.lean',
    ROOT / 'ExplicitLean/SimpEngine/Boundary/DeclarationCodec.lean',
    ROOT / 'ExplicitLean/SimpEngine/Boundary/SparseCasesCodec.lean',
]
for stem in ('ExprCodec', 'DeclarationCodec', 'SparseCasesCodec'):
    for suffix in ('.olean', '.olean.private', '.olean.server', '.ir'):
        INPUTS.append(ROOT / f'.lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/{stem}{suffix}')
missing = [str(p) for p in INPUTS if not p.is_file()]
if missing:
    raise RuntimeError(f'missing pinned Lean inputs: {missing}')
INPUTS_BEFORE = {str(p): sha(p) for p in INPUTS}
ARCHIVE = WORK / 'inputs'; ARCHIVE.mkdir()
ARCHIVED_INPUTS = []
for path in INPUTS:
    target = ARCHIVE / path.name
    if target.exists() and sha(target) != sha(path):
        target = ARCHIVE / (sha(path)[:12] + '-' + path.name)
    shutil.copy2(path, target)
    ARCHIVED_INPUTS.append(dict(path=str(path), sha256=sha(path), archivedPath=str(target)))

def run(case, body, expected=None):
    path = WORK / case / 'Experiment/SparseCodecFixture.lean'
    path.parent.mkdir(parents=True)
    path.write_text(HEADER.replace('__BODY__', body.replace('\n', '\n  ')))
    result = run_process(['lake', 'env', str(LEAN), '-R', str(path.parent.parent), str(path)],
                         cwd=ROOT, text=True, capture_output=True, timeout=90)
    log = path.with_suffix('.log')
    log.write_text(result.stdout + result.stderr)
    if expected:
        if result.returncode == 0 or expected not in log.read_text():
            raise RuntimeError(f'{case}: expected {expected!r}; see {log}\n{log.read_text()}')
    else:
        if result.returncode != 0 or 'SPARSE_CODEC_OK' not in result.stdout:
            raise RuntimeError(f'{case}: compiler/control failed; see {log}\n{log.read_text()}')
    records.append(dict(case=case, expected=expected, exitCode=result.returncode,
                        source=str(path), sourceSha256=sha(path), log=str(log), logSha256=sha(log)))
    print(case + ': passed', flush=True)
    return result.stdout

out = run('capture', '''let before ← getEnv
let eqns ← Match.getEquationsFor `List.modifyLast.go.match_1
let env ← getEnv
let candidates := env.constants.foldStage2 (s := #[]) fun names name _ =>
  if !before.containsOnBranch name && (getSparseCasesOnInfoCore env name).isSome then names.push name else names
unless candidates.size == 1 do throwError "fixture helper count"
let name := candidates[0]!
let payload ← encodeBoundarySparseCases before name eqns.splitterName
IO.println ("PAYLOAD " ++ payload)
IO.println ("CACHE " ++ (boundarySparseCacheJson env (some eqns.splitterName)).compress)
IO.println "SPARSE_CODEC_OK"''')
raw = next(line.removeprefix('PAYLOAD ') for line in out.splitlines() if line.startswith('PAYLOAD '))
cache = next(line.removeprefix('CACHE ') for line in out.splitlines() if line.startswith('CACHE '))
payload = json.loads(raw)
name_wire = json.dumps(payload[1], separators=(',', ':'))

def preamble(raw_payload=raw):
    return ('let name ← match decodeBoundaryName (← ofExcept <| Json.parse ' + json.dumps(name_wire) + ') with\n'
            '  | .ok name => pure name\n  | .error error => throwError error\n'
            'let payload := ' + json.dumps(raw_payload) + '\n')

body = preamble() + '''let before ← getEnv
executeBoundarySparseCases name payload
let env ← getEnv
unless (boundarySparseCacheJson env).compress == __CACHE__ do throwError "cache differs"
let .arr #[_, _, .str definition, _, _] ← ofExcept <| Json.parse payload
  | throwError "fixture payload"
let .arr #[_, _, _, _, _, _, .str typeSource, .str valueSource] ← ofExcept <| Json.parse definition
  | throwError "fixture definition"
let some (.defnInfo actual) := env.find? name (skipRealize := true)
  | throwError "fixture missing definition"
unless actual.type == (← decodeBoundaryExpr typeSource) &&
    actual.value == (← decodeBoundaryExpr valueSource) do
  throwError "raw expressions differ"
executeBoundarySparseCases name payload
IO.println "SPARSE_CODEC_OK"'''.replace('__CACHE__', json.dumps(cache))
run('fresh-and-cached-replay', body)
run('cache-conflict', preamble() + '''modifyEnv fun env => sparseCasesOnCacheExt.modifyState env fun state =>
  state.insert { indName := ``List, ctors := #[``List.nil], isPrivate := true } `unrelated
executeBoundarySparseCases name payload''', 'boundary_sparse_cache_conflict')
run('cached-metadata-conflict', preamble() + '''executeBoundarySparseCases name payload
modifyEnv fun env => sparseCasesOnInfoExt.insert env name {
  indName := ``List, majorPos := 99, arity := 5, insterestingCtors := #[``List.nil] }
executeBoundarySparseCases name payload''', 'boundary_sparse_existing_metadata_conflict')
run('cached-reducibility-conflict', preamble() + '''executeBoundarySparseCases name payload
setIrreducibleAttribute name
executeBoundarySparseCases name payload''', 'boundary_sparse_reducibility_conflict')
for case in ('metadata-arity', 'duplicate-constructor', 'public-cache-key', 'non-abbreviation'):
    data = json.loads(raw)
    if case == 'metadata-arity':
        data[4][2] += 1; expected = 'boundary_sparse_metadata_conflict'
    elif case == 'duplicate-constructor':
        data[3][1] *= 2; expected = 'duplicate sparse constructor'
    elif case == 'public-cache-key':
        data[3][2] = False; expected = 'boundary_sparse_expected_private_helper'
    else:
        definition = json.loads(data[2]); definition[4] = ['opaque']
        data[2] = json.dumps(definition, separators=(',', ':'))
        expected = 'boundary_sparse_expected_safe_abbreviation'
    run(case, preamble(json.dumps(data, separators=(',', ':'))) + 'executeBoundarySparseCases name payload', expected)

inputs_after = {str(p): sha(p) for p in INPUTS}
if INPUTS_BEFORE != inputs_after:
    raise RuntimeError('pinned Lean inputs changed during fresh controls')
report = dict(status='passed', acceptedCampaignCoverage=False, records=records,
              inputs=ARCHIVED_INPUTS,
              inputSha256Before=INPUTS_BEFORE, inputSha256After=inputs_after,
              archivedInputDirectory=str(ARCHIVE),
              leanBinary=str(INPUTS[1]))
(WORK/'report.json').write_text(json.dumps(report, indent=2)+'\n')
print('report=' + str(WORK/'report.json'), flush=True)
