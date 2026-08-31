#!/usr/bin/env python3
"""Three bounded source witnesses for pre-boundary expression references.

Each replaces exactly one original occurrence, preserves source/comments, and
requires fresh recording, replay and full declaration-oracle success. This is
not full module or dependency-cone coverage.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, tempfile
import boundary_materialize_shard as m
import boundary_protocol as p
import check_simp_engine_recursive_realizations as runtime

ROOT = Path(__file__).resolve().parents[1]
CASES = {
    'centralizer': ('Mathlib/Algebra/Algebra/Subalgebra/Centralizer.lean', '9dfed3d35b21d42b'),
    'quasicompact': ('Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean', 'e44856b28b26d122'),
    'faces': ('Mathlib/AlgebraicTopology/DoldKan/Faces.lean', '04da152183a5023a'),
}

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--manifest',type=Path,required=True)
    parser.add_argument('--only',choices=CASES)
    args=parser.parse_args()
    parent=ROOT/'.lake/expression-reference';parent.mkdir(exist_ok=True)
    work=Path(tempfile.mkdtemp(prefix='source-',dir=parent));print(work,flush=True)
    corpus=json.loads(args.manifest.read_bytes())
    selected={args.only:CASES[args.only]} if args.only else CASES
    def inputs():
        hashes=runtime.input_hashes()
        for path in [args.manifest,ROOT/'.lake/build/bin/simpEngineDeclarationOracle'] + [ROOT/'.lake/packages/mathlib'/module for module,_ in selected.values()]:
            hashes[str(path.resolve())]=digest(path)
        return hashes
    before=inputs();runs=[];status='failed'
    dylib=ROOT/'.lake/build/lib/libexplicitLean_ExplicitLean.dylib'
    archive=work/'runtime.dylib';subprocess.run(['cp','-c',str(dylib),str(archive)],check=True)
    try:
        for case,(module,occ) in selected.items():
            folder=work/case;folder.mkdir()
            source=(ROOT/'.lake/packages/mathlib'/module).read_bytes()
            row=next(x for x in corpus['modules'] if x['module']==module)
            assert row['sourceHash']==hashlib.sha256(source).hexdigest()
            entry=next(x for x in row['occurrences'] if x['id']==occ)
            assert source[entry['startByte']:entry['endByte']].decode()==entry['source']
            original=m._copy_at_module_root(folder/'original',module,source)
            instrumented=m._copy_at_module_root(folder/'instrumented',module,m.instrumented_source(source,[entry]))
            run={'case':case,'module':module,'occurrence':occ,'original':str(original),'instrumented':str(instrumented),'stages':[]}
            runs.append(run)
            def compile_stage(label,path,recording):
                env,nonce=p.recording_subprocess_environment() if recording else p.replay_subprocess_environment()
                code,output,elapsed=m._compile_copy(path,str(archive),360,env=env)
                log=folder/(label+'.log');log.write_text(output)
                run['stages'].append({'label':label,'source':str(path),'log':str(log),'nonce':nonce,'recording':recording,'exit':code,'seconds':elapsed})
                scanner=p.check_recording_abort_markers if recording else p.check_replay_abort_markers
                scanner(output,expected_nonce=nonce,expected_module=m.corpus.compiled_module_name(module))
                assert code==0,(case,label,str(log),output[-2000:])
                return output,nonce
            output,nonce=compile_stage('recording',instrumented,True)
            records=p.parse_framed_json_lines(output,marker=m.ARTIFACT_MARKER,expected_nonce=nonce,label=case)
            assert records and all(r['schema']==p.ARTIFACT_SCHEMA for r in records)
            m._write_jsonl(folder/'artifacts.jsonl',records)
            variants=m.group_report_variants(records,[occ],expected_module=m.corpus.compiled_module_name(module),unobserved_ids=set())
            rewritten=m.replace_all_occurrences(source,[entry],variants)
            generated=m._inject_import(rewritten,'ExplicitLean.SimpEngine.Boundary.Tactic')
            applied=m._copy_at_module_root(folder/'applied',module,generated)
            m._assert_context_gaps(source,generated,[entry],imported='ExplicitLean.SimpEngine.Boundary.Tactic',label=case,expected_without_import=rewritten)
            compile_stage('applied',applied,False)
            run['oracle']=m.run_declaration_oracle(module,original,applied,folder,str(archive),600)
            run['variantCount']=len(variants[occ]);print(case+': passed',flush=True)
        status='passed'
    finally:
        after=inputs()
        report={'kind':'expression-reference-source-diagnostic','status':status,'artifactSchema':p.ARTIFACT_SCHEMA,'reportSchema':m.REPORT_SCHEMA,'acceptedCoverage':False,'runs':runs,'inputsBefore':before,'inputsAfter':after}
        (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        assert before==after,'inputs changed during source diagnostics'
    print(work/'report.json',flush=True)

if __name__=='__main__':main()
