#!/usr/bin/env python3
"""Fresh full-source and mutation controls for an ExistsUnique local sequence.

Pass the immutable JSON report produced by a successful full-module
boundary_materialize_shard._module_result run. This driver performs no builds
and writes only into a new private .lake control directory. Internally consistent
changed metadata must fail the separate source-pair declaration oracle when it
is not rejected by encoded replay itself. This is bounded source evidence, not
cold serialized-output or translated dependency-tree certification.
"""
from pathlib import Path
import copy, hashlib, json, sys, tempfile
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'Experiment'))
import boundary_materialize_shard as m
import boundary_protocol as protocol
import boundary_expr_codec as wire
import check_simp_engine_recursive_realizations as recursive
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
report_path=Path(sys.argv[1]); base_report=json.loads(report_path.read_text()); result=base_report['result'];assert base_report['status']=='completed'
reports=[json.loads(line) for line in Path(result['reportPath']).read_text().splitlines()]
report=next(r for r in reports if r['occurrence']=='8cce65a0fe3fc19d')
action=next(a for a in report['environmentActions'] if json.loads(a['declaration'])[0]=='boundary_local_cached_sequence_v1')
payload=json.loads(action['declaration']); assert len(payload[3])==2
base=Path(result['materializedPath']).read_text();old=json.dumps(action['declaration'],ensure_ascii=False);assert base.count(old)==1
work=Path(tempfile.mkdtemp(prefix='controls-',dir=ROOT/'.lake'));print(work,flush=True)
(work/'driver.py').write_bytes(Path(__file__).read_bytes());inputs=recursive.input_hashes();inputs[str(report_path)]=sha(report_path)
runs=[];wire_checks=[]
def run(label,value,expected=None):
    text=base.replace(old,json.dumps(json.dumps(value,separators=(',',':')),ensure_ascii=False))
    path=m._copy_at_module_root(work/label,result['module'],text.encode())
    env,nonce=protocol.replay_subprocess_environment();code,output,elapsed=m._compile_copy(path,str(ROOT/'.lake/build/lib/libexplicitLean_ExplicitLean.dylib'),240,env=env)
    log=work/(label+'.log');log.write_text(output);failure=None
    try:protocol.check_replay_abort_markers(output,expected_nonce=nonce)
    except RuntimeError as e:failure=str(e)
    assert code in (0,1),output[-2000:]
    if expected is None:assert code==0 and failure is None,output[-3000:]
    elif expected == '__oracle':
        if failure is None:
            assert code==0,output[-3000:]
            oracle_error=None
            try:m.run_declaration_oracle(result['module'],Path(result['originalPath']),path,work/label,str(ROOT/'.lake/build/lib/libexplicitLean_ExplicitLean.dylib'),240)
            except RuntimeError as e:oracle_error=str(e)
            assert oracle_error is not None,'changed metadata accepted by oracle'
            oracle=(work/label/'declaration-oracle.log').read_text()
            assert '"status":"failure"' in oracle or 'SIMP_ENGINE_BOUNDARY_REPLAY_ABORT ' in oracle,oracle[-3000:]
            failure=oracle_error
    else:assert failure is not None and expected in failure,(failure or output[-3000:])
    runs.append(dict(label=label,source=str(path),log=str(log),nonce=nonce,compilerExit=code,expectedAbort=expected,elapsedSeconds=elapsed,failure=failure));print(label+': passed',flush=True)
def mutate(label,change,expected,wire_reject=False):
    value=copy.deepcopy(payload);change(value)
    if wire_reject:
        try:wire.validate_realization_payload(json.dumps(value),action['nameParts'],label)
        except RuntimeError:wire_checks.append(label)
        else:raise AssertionError('wire accepted '+label)
    run(label,value,expected)
run('fresh-full-replay',payload)
wire.validate_realization_payload(action['declaration'],action['nameParts'],'positive');wire_checks.append('valid')
mutate('missing-step',lambda p:p[7].pop(),'boundary_local_sequence_order',True)
mutate('duplicate-root',lambda p:p[7].append(copy.deepcopy(next(s for s in p[7] if s[0]=='root'))),'boundary_local_sequence_duplicate_root',True)
mutate('swapped-steps',lambda p:p[7].reverse(),'boundary_local_sequence_order',True)
mutate('wrong-owner',lambda p:p[6].__setitem__(0,[['s','Foreign']]),'boundary_local_sequence_identity',True)
mutate('owner-safety',lambda p:p[6][2].__setitem__(6,'unsafe'),'boundary_local_sequence_original_authentication',True)
mutate('descriptor-node',lambda p:p[6][3][3][0].__setitem__(1,not p[6][3][3][0][1]),'boundary_local_sequence_original_authentication')
mutate('root-snapshot',lambda p:next(s for s in p[7] if s[0]=='root').__setitem__(1,[[],[],[]]),'boundary_local_sequence_transition',True)
mutate('final-state',lambda p:p.__setitem__(5,[[],[],[]]),'boundary_local_sequence_after',True)
helpers=[i for i,s in enumerate(payload[7]) if s[0]=='helper'];assert len(helpers)==2
for number,index in enumerate(helpers):
    mutate(f'helper{number}-snapshot',lambda p,i=index:p[7][i].__setitem__(4,[[],[],[]]),'boundary_local_sequence_helper_snapshot',True)
    mutate(f'helper{number}-public',lambda p,i=index:p[7][i].__setitem__(3,not p[7][i][3]),'boundary_local_sequence_order',True)
    def change_helper(p,field,value,i=index):
        bundle=json.loads(p[7][i][2]);helper=json.loads(bundle[2][0][1]);helper[field]=value(helper[field]);bundle[2][0][1]=json.dumps(helper,separators=(',',':'));p[7][i][2]=json.dumps(bundle,separators=(',',':'))
    mutate(f'helper{number}-tag',lambda p:change_helper(p,4,lambda old:not old),'__oracle')
    mutate(f'helper{number}-export',lambda p:change_helper(p,2,lambda old:'theorem' if old!='theorem' else 'axiom'),'__oracle')
    mutate(f'helper{number}-cache-privacy',lambda p:change_helper(p,6,lambda cache:[cache[0],False,*cache[2:]]),'boundary_local_theorem_public_cache_key_for_private_name',True)
    def bad_proof(old):
        theorem=json.loads(old);theorem[5]=json.dumps(['expr_dag_v1',[['c',[['s','True'],['s','intro']],[]]],0],separators=(',',':'));return json.dumps(theorem,separators=(',',':'))
    mutate(f'helper{number}-proof',lambda p:change_helper(p,3,bad_proof),'')
after=recursive.input_hashes();after[str(report_path)]=sha(report_path);assert inputs==after
out=dict(status='passed',baseReport=str(report_path),runs=runs,wireChecks=wire_checks,inputsBefore=inputs,inputsAfter=after,files={str(p):sha(p) for p in work.rglob('*') if p.is_file()},wholeMathlib=False)
(work/'report.json').write_text(json.dumps(out,indent=2)+'\n');print(work/'report.json')
