from pathlib import Path
import shutil
import os,sys,json,hashlib,tempfile
DEFAULT_ROOT=Path(__file__).resolve().parents[1]
ROOT=Path(os.environ.get('EXPLICIT_LEAN_PROJECT_ROOT',str(DEFAULT_ROOT))).resolve()
sys.path.insert(0,str(ROOT/'Experiment'))
from process_runner import run_process
EVIDENCE_DIR=ROOT/'.lake/sparse-probe'
EVIDENCE_DIR.mkdir(parents=True,exist_ok=True)
WORK=Path(tempfile.mkdtemp(prefix='sparse-matcher-lean-',dir=EVIDENCE_DIR))
HEADER='''module
import Mathlib.Init
import Batteries.Data.List.Basic
public meta import ExplicitLean.SimpEngine.Boundary.MatcherCodec
public meta import Lean.Meta.Match.MatchEqs
public meta import Lean.Meta.Constructions.SparseCasesOn
meta import all Lean.Meta.Constructions.SparseCasesOn
open Lean Meta Elab ExplicitLean.SimpEngine.Boundary
run_meta do
  __BODY__
'''
records=[];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def resolve_pinned_lean():
 result=run_process(['lake','env','printenv','PATH'],cwd=ROOT,text=True,capture_output=True,check=False,timeout=10)
 if result.returncode != 0: raise RuntimeError(f'could not resolve lake environment PATH: {result.stdout}{result.stderr}')
 for directory in result.stdout.strip().split(os.pathsep):
  candidate=Path(directory)/'lean'
  if candidate.is_file() and os.access(candidate,os.X_OK): return candidate.resolve()
 raise RuntimeError('lake environment PATH has no executable lean')
LEAN=resolve_pinned_lean()
INPUTS=[ROOT/'lean-toolchain',LEAN,
        ROOT/'Experiment/boundary_expr_codec.py',ROOT/'Experiment/boundary_protocol.py',ROOT/'Experiment/process_runner.py',
        Path(__file__).resolve(),
        ROOT/'ExplicitLean/SimpEngine/Boundary/ExprCodec.lean',
        ROOT/'ExplicitLean/SimpEngine/Boundary/DeclarationCodec.lean',
        ROOT/'ExplicitLean/SimpEngine/Boundary/SparseCasesCodec.lean',
        ROOT/'ExplicitLean/SimpEngine/Boundary/MatcherCodec.lean']
for stem in ('ExprCodec','DeclarationCodec','SparseCasesCodec','MatcherCodec'):
 for suffix in ('.olean','.olean.private','.olean.server','.ir'):
  INPUTS.append(ROOT/f'.lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/{stem}{suffix}')
missing=[str(p) for p in INPUTS if not p.is_file()]
if missing: raise RuntimeError(f'missing pinned Lean inputs: {missing}')
INPUTS_BEFORE={str(p):sha(p) for p in INPUTS}
ARCHIVE=WORK/'inputs'; ARCHIVE.mkdir()
ARCHIVED_INPUTS=[]
for path in INPUTS:
 target=ARCHIVE/path.name
 if target.exists() and sha(target) != sha(path): target=ARCHIVE/(sha(path)[:12]+'-'+path.name)
 shutil.copy2(path,target)
 ARCHIVED_INPUTS.append(dict(path=str(path),sha256=sha(path),archivedPath=str(target)))
def run(case,body,expected=None):
 path=WORK/case/'Experiment/SparseMatcherFixture.lean';path.parent.mkdir(parents=True)
 path.write_text(HEADER.replace('__BODY__',body.replace('\n','\n  ')))
 result=run_process(['lake','env',str(LEAN),'-R',str(path.parent.parent),str(path)],cwd=ROOT,text=True,capture_output=True,timeout=90)
 log=path.with_suffix('.log');log.write_text(result.stdout+result.stderr)
 if expected:
  if result.returncode == 0 or expected not in log.read_text():
   raise RuntimeError(f'{case}: expected {expected!r}; see {log}\n{log.read_text()}')
 elif result.returncode!=0 or 'SPARSE_MATCHER_OK' not in result.stdout:
  raise RuntimeError(f'{case}: compiler/control failed; see {log}\n{log.read_text()}')
 records.append(dict(case=case,expected=expected,exitCode=result.returncode,source=str(path),sourceSha256=sha(path),log=str(log),logSha256=sha(log)))
 print(case+': passed',flush=True);return result.stdout
out=run('capture','''let before ← getEnv
let checked := before.constants.foldStage2 (fun s n _ => s.insert n) ({} : NameSet)
let anchor := `List.modifyLast.go.match_1
let eqns ← Match.getEquationsFor anchor
let env ← getEnv
let sparse := env.constants.foldStage2 (s := #[]) fun names name _ =>
  if !checked.contains name && (getSparseCasesOnInfoCore env name).isSome then names.push name else names
unless sparse.size == 1 do throwError "fixture helper count"
let payload ← encodeBoundaryMatcher before checked anchor eqns #[] #[] sparse
IO.println ("PAYLOAD " ++ payload)
IO.println "SPARSE_MATCHER_OK"''')
raw=next(x[8:] for x in out.splitlines() if x.startswith('PAYLOAD '))
def prefix(payload=raw):return 'let anchor := `List.modifyLast.go.match_1\nlet payload := '+json.dumps(payload)+'\n'
run('fresh-and-cached',prefix()+'''let before := boundarySparseCacheJson (← getEnv)
executeBoundaryMatcher anchor payload
unless boundarySparseCacheJson (← getEnv) == before do throwError "caller changed"
executeBoundaryMatcher anchor payload
unless boundarySparseCacheJson (← getEnv) == before do throwError "cached caller changed"
IO.println "SPARSE_MATCHER_OK"''')
for case in ('missing-helper','altered-helper-metadata','altered-async-cache','altered-before-cache','altered-local-cache'):
 data=json.loads(raw)
 if case=='missing-helper':data[15]=[];expected='boundary_matcher_sparse_cache_conflict'
 elif case=='altered-helper-metadata':
  h=json.loads(data[15][0][1]);h[4][2]+=1;data[15][0][1]=json.dumps(h,separators=(',',':'));expected='boundary_sparse_metadata_conflict'
 elif case=='altered-async-cache':data[17]=[];expected='boundary_matcher_sparse_cache_conflict'
 elif case=='altered-before-cache':data[16]=data[17];expected='boundary_matcher_sparse_cache_conflict'
 else:data[18]=data[17];expected='boundary_matcher_sparse_cache_conflict'
 run(case,prefix(json.dumps(data,separators=(',',':')))+'executeBoundaryMatcher anchor payload',expected)
inputs=[ROOT/'ExplicitLean/SimpEngine/Boundary'/name for name in ('MatcherCodec.lean','SparseCasesCodec.lean')]
inputs_after={str(p):sha(p) for p in INPUTS}
if INPUTS_BEFORE != inputs_after:
 raise RuntimeError('pinned Lean inputs changed during fresh controls')
(WORK/'report.json').write_text(json.dumps(dict(status='passed',acceptedCampaignCoverage=False,records=records,
 inputs=ARCHIVED_INPUTS,inputSha256Before=INPUTS_BEFORE,
 inputSha256After=inputs_after,archivedInputDirectory=str(ARCHIVE),leanBinary=str(INPUTS[1])),indent=2)+'\n')
print('report='+str(WORK/'report.json'),flush=True)
