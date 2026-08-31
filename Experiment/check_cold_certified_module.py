#!/usr/bin/env python3
"""Focused cold certificate controls using immutable prebuilt native tools."""
from pathlib import Path
from dataclasses import replace
import argparse, copy, json, os, subprocess, tempfile
from unittest.mock import patch

import cold_certified_module as cold
import certified_module as base
import boundary_protocol as protocol
import check_simp_engine_command_audit as audit
from translated_imports import build_import_environment
from process_runner import run_process

ROOT=Path(__file__).resolve().parents[1]

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--oracle',type=Path,default=ROOT/'.lake/build/bin/simpEngineDeclarationOracle')
 parser.add_argument('--auditor',type=Path,default=ROOT/'.lake/build/bin/simpEngineCommandAudit')
 args=parser.parse_args()
 oracle=base._checked_file(base.InputFile(args.oracle.resolve(strict=True),base.sha256(args.oracle)))
 auditor=base._checked_file(base.InputFile(args.auditor.resolve(strict=True),base.sha256(args.auditor)))
 work=Path(tempfile.mkdtemp(prefix='cold-certificate-check-',dir=ROOT/'.lake'));print(work,flush=True)
 sources=work/'sources';translated=work/'translated';runs=work/'runs'
 for p in (sources,translated,runs):p.mkdir()
 imports=build_import_environment(sources,translated)
 extra_import=work/'extra-import';extra_import.mkdir();imports=replace(imports,search_path=(*imports.search_path,extra_import))
 dep=sources/'Mathlib/ColdDependency.lean';dep.parent.mkdir();dep.write_text('module\npublic import Std\npublic def coldDependency : Nat := 7\n')
 out=translated/'Mathlib/ColdDependency.olean';out.parent.mkdir()
 command=[str(imports.lean_binary),'-R',str(sources),'-o',str(out),str(dep)]
 proc=run_process(command,cwd=ROOT,env=imports.environment(),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120,check=False)
 (work/'dependency.log').write_text(proc.stdout);assert proc.returncode==0,proc.stdout
 dependencies={'Mathlib.ColdDependency':{str(out.with_suffix(s)):base.sha256(out.with_suffix(s)) for s in base.SUFFIXES}}
 identities={str(Path(__file__).resolve()):base.sha256(Path(__file__).resolve()),str(Path(cold.__file__)):base.sha256(Path(cold.__file__)),str(oracle.path):oracle.sha256,str(auditor.path):auditor.sha256,**dependencies['Mathlib.ColdDependency']}
 checks=[];successes=[];events=[]
 prefix='module\nimport Lean\nimport Mathlib.ColdDependency\npublic section\n'
 body='@[expose] def coldValue : Nat := 7\ntheorem coldTarget (n : Nat) : n + 0 = n := by exact Nat.add_zero n\n'
 simple=prefix+body

 def call(name,stock_text=simple,applied_text=simple,*,detail=None,mutate=None,override=None):
  module='ColdCertificate.'+name
  relative=base._module_path(module).with_suffix('.lean')
  stock=sources/name/'stock'/relative;applied=sources/name/'applied'/relative
  for path,content in ((stock,stock_text),(applied,applied_text)):path.parent.mkdir(parents=True);path.write_text(content)
  params=dict(module=module,stock=cold.InputFile(stock,base.sha256(stock)),applied=cold.InputFile(applied,base.sha256(applied)),is_module=stock_text.startswith('module\n'),oracle=oracle,auditor=auditor,imports=imports,dependencies=dependencies,work_parent=runs,timeout=120)
  params.update(override or {})
  def run(command,**kw):
   is_bridge='--bridge-oleans' in command
   if mutate=='timeout':raise subprocess.TimeoutExpired(command,.01,output=b'partial timeout\n')
   if is_bridge and mutate in ('missing-nonce','missing-audit'):
    kw['env']=dict(kw['env']);kw['env'].pop(protocol.RUN_NONCE_ENV if mutate=='missing-nonce' else audit.ENABLE_ENV)
   result=run_process(command,**kw)
   events.append({'case':name,'command':command,'exitCode':result.returncode,'nonce':kw['env'].get(protocol.RUN_NONCE_ENV)})
   if is_bridge and callable(mutate):mutate(params,command,result)
   return result
  try:
   with patch.object(cold.process_runner,'run_process',side_effect=run):cert=cold.certify_module(**params)
  except cold.CertificationError as error:
   if detail is None or detail not in str(error):raise RuntimeError(f'{name}: unexpected {error}') from error
   if error.work_directory:
    assert not (error.work_directory/'receipt.json').exists()
    failure=json.loads((error.work_directory/'failure.json').read_text());assert not failure['acceptedCampaignCoverage']
    if name=='Postponed':
     log=(error.work_directory/'bridge.log').read_text()
     assert 'failed to open file' in log and 'Postponed.ir' in log and 'No such file or directory' in log
   checks.append({'case':name,'status':'rejected','detail':str(error),'work':str(error.work_directory)})
   cert=None
  else:
   assert detail is None,(name,'unexpected acceptance')
   r=cold.verify_certification(cert)
   assert not r['acceptedCampaignCoverage'] and not r['promoted'] and not r['sourceCommentProvenanceAccepted']
   assert len(r['stages'])==5 and len(r['artifactFamilies'])==6 and r['outputArtifactFamily']==r['artifactFamilies']['ordinary-applied']
   assert not (translated/relative.with_suffix('.olean')).exists()
   successes.append(cert);checks.append({'case':name,'status':'certified_in_quarantine','receipt':str(cert.receipt_path),'sha256':cert.receipt_sha256})
  print(json.dumps(checks[-1]),flush=True)
  return cert

 call('Module')
 call('Legacy',simple.replace('module\n','').replace('public section\n',''),simple.replace('module\n','').replace('public section\n',''))
 call('Replacement',simple.replace('by exact Nat.add_zero n','by simp'),simple.replace('by exact Nat.add_zero n','by\n  -- simp\n  exact Nat.add_zero n'))
 call('Partial',prefix+'#eval IO.print "partial"\n'+body,prefix+'#eval IO.print "partial"\n'+body)
 call('Changed',simple,simple.replace(':= 7',':= 8'),detail='bridge exited with code')
 call('Remaining',simple.replace('by exact Nat.add_zero n','by simp'),simple.replace('by exact Nat.add_zero n','by simp'),detail='directExecutableCount')
 call('Reusable',prefix+'macro "cold_quoted" : tactic => `(tactic| simp)\n',prefix+'macro "cold_quoted" : tactic => `(tactic| simp)\n',detail='reusableExecutableCount')
 call('WrongHeader',detail='module mode mismatch',override={'is_module':False})
 call('Postponed',simple.replace('public section','set_option compiler.postponeCompile true\npublic section'),simple.replace('public section','set_option compiler.postponeCompile true\npublic section'),detail='bridge exited with code 1')
 call('MissingNonce',detail='bridge exited with code',mutate='missing-nonce')
 call('MissingAudit',detail='bridge exited with code',mutate='missing-audit')
 call('Timeout',detail='timed out',mutate='timeout')
 def corrupt(params,command,result):
  f=Path(command[-2]).with_suffix('.olean.private');f.write_bytes(f.read_bytes()+b'changed')
 call('ColdMismatch',detail='cold artifact mismatch: stock bridge',mutate=corrupt)
 def extra(params,command,result):(Path(command[-1]).parent/'extra').write_text('stale')
 call('ExtraFamily',detail='artifact family',mutate=extra)
 def missing(params,command,result):Path(command[-1]).with_suffix('.ir').unlink()
 call('MissingFamily',detail='artifact family',mutate=missing)
 def source_change(params,command,result):params['applied'].path.write_bytes(params['applied'].path.read_bytes()+b'\n-- changed\n')
 call('SourceMutation',detail='input hash mismatch',mutate=source_change)
 dep_ir=out.with_suffix('.ir');saved=dep_ir.read_bytes()
 try:call('DependencyMutation',detail='input hash mismatch',mutate=lambda *a:dep_ir.write_bytes(saved+b'changed'))
 finally:dep_ir.write_bytes(saved)
 call('InsideSearchPath',detail='inside an import search root',override={'work_parent':translated})
 call('IncompleteDependency',detail='incomplete dependency',override={'dependencies':{'Mathlib.ColdDependency':dict(list(dependencies['Mathlib.ColdDependency'].items())[:3])}})
 link=work/'linked';link.symlink_to(runs,target_is_directory=True)
 call('SymlinkWork',detail='symlink path',override={'work_parent':link})
 wrong=sources/'wrong.lean';wrong.write_text(simple)
 call('WrongSourcePath',detail='module-relative',override={'stock':cold.InputFile(wrong,base.sha256(wrong))})

 valid=successes[0].receipt;event=valid['stages'][-1];text=Path(event['log']['path']).read_text();nonce=event['nonce']
 ids={side:audit.ExpectedAudit(valid['module'],Path(valid[side]['path']),Path(valid[side]['path']).read_bytes(),side,True) for side in ('stock','applied')}
 line=next(l for l in text.splitlines() if l.startswith(cold.BRIDGE_MARKER))
 frames=[l for l in text.splitlines() if l.startswith(audit.MARKER)]
 mutations={'wrong-nonce':(text,'foreign',0),'missing-result':(text.replace(line,''),nonce,0),'duplicate-result':(text+'\n'+line+'\n',nonce,0),'legacy-result':(text.replace(line,materializer_marker(line)),nonce,0),'missing-audit':(text.replace(frames[0],''),nonce,0),'duplicate-audit':(text+'\n'+frames[0]+'\n',nonce,0),'wrong-order':(text.replace(frames[0],'AUDIT_TEMP').replace(frames[1],frames[0]).replace('AUDIT_TEMP',frames[1]),nonce,0),'nonzero':(text,nonce,1)}
 mutations['v1-result']=(text.replace(cold.BRIDGE_MARKER,'SIMP_ENGINE_COLD_BRIDGE_ORACLE '),nonce,0)
 mutations['mixed-v1-v2']=(text+'\n'+line.replace(cold.BRIDGE_MARKER,'SIMP_ENGINE_COLD_BRIDGE_ORACLE ')+'\n',nonce,0)
 for field,value in [('schema',True),('module','Wrong'),('checkedDeclarationCount',True)]:
  obj=protocol.parse_framed_json_lines(line,marker=cold.BRIDGE_MARKER,expected_nonce=nonce,label='fixture')[0];obj[field]=value
  mutations['payload-'+field]=(text.replace(line,protocol.marker_prefix(cold.BRIDGE_MARKER,nonce)+json.dumps(obj)),nonce,0)
 for name,(changed,token,code) in mutations.items():
  try:cold.validate_bridge(changed,exit_code=code,module=valid['module'],nonce=token,**ids)
  except RuntimeError:checks.append({'case':name,'status':'rejected-wire'})
  else:raise RuntimeError('accepted wire mutation '+name)
 # Rehashing jointly changed invocation/result fields must not turn them into
 # a valid command/environment identity. These are private disposable fixtures.
 cert=successes[0];folder=cert.receipt_path.parent
 for field,value in [('command',['wrong']),('module','Wrong'),('environment',{}),('auditEnableVariable',True),('exitCode',False)]:
  changed=copy.deepcopy(cert.receipt);e=changed['stages'][0];e[field]=value
  invocation=Path(e['invocation']['path']);result=folder/(e['stage']+'.result.json');saved={p:p.read_bytes() for p in (invocation,result)}
  try:
   invocation.write_text(json.dumps({k:e[k] for k in ('stage','command','nonce','module','environment','auditEnableVariable')}))
   e['invocation']['sha256']=base.sha256(invocation);result.write_text(json.dumps(e))
   try:cold._verify_record(changed,folder)
   except RuntimeError as error:checks.append({'case':'consistent-edit-'+field,'status':'rejected-receipt','detail':str(error)})
   else:raise RuntimeError('accepted consistent receipt edit '+field)
  finally:
   for p,data in saved.items():p.write_bytes(data)
  cold.verify_certification(cert)
 (extra_import/'Mathlib').mkdir()
 try:
  try:cold.verify_certification(cert)
  except RuntimeError as error:checks.append({'case':'new-shadow-mathlib','status':'rejected-receipt','detail':str(error)})
  else:raise RuntimeError('accepted new shadow root')
 finally:(extra_import/'Mathlib').rmdir()
 target=translated/base._module_path(cert.receipt['module']);target.parent.mkdir(exist_ok=True);target.write_bytes(b'old output')
 try:
  try:cold.verify_certification(cert)
  except RuntimeError as error:checks.append({'case':'existing-publication-target','status':'rejected-receipt','detail':str(error)})
  else:raise RuntimeError('accepted existing target')
  cold.verify_certification(cert,require_target_absent=False)
 finally:target.unlink()
 cold.verify_certification(cert)
 # Read only ordinary-applied output in fresh downstream processes.
 for cert in successes[:2]:
  r=cert.receipt;src=work/(r['module'].replace('.','-')+'-consumer.lean');src.write_text(f"import {r['module']}\n#eval coldValue + coldDependency\n")
  env=imports.environment();env['LEAN_PATH']=os.pathsep.join([r['quarantine'],*(str(p) for p in imports.search_path)])
  command=[str(imports.lean_binary),str(src)];proc=run_process(command,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120,check=False)
  log=src.with_suffix('.log');log.write_text(proc.stdout);assert proc.returncode==0 and proc.stdout.strip()=='14',proc.stdout
  checks.append({'case':'read-'+r['module'],'status':'computed_14','log':str(log)})
 assert identities=={p:base.sha256(Path(p)) for p in identities}
 archive=work/'inputs';archive.mkdir()
 for i,(p,h) in enumerate(identities.items()):
  target=archive/f'{i:03d}-{Path(p).name}';subprocess.run(['/bin/cp','-c',p,str(target)],check=True);assert base.sha256(target)==h
 report={'status':'passed','acceptedCampaignCoverage':False,'inputs':identities,'checks':checks,'nativeRuns':events,'files':{str(p):base.sha256(p) for p in work.rglob('*') if p.is_file() and not p.is_symlink()}}
 path=work/'report.json';path.write_text(json.dumps(report,indent=2)+'\n');print(path,flush=True)

def materializer_marker(line):
 return 'SIMP_ENGINE_DECLARATION_ORACLE '+line.split(' ',2)[2]

if __name__=='__main__':main()
