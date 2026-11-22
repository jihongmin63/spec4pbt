#!/usr/bin/env python3
"""Generate and compile every Wasm-specific adapter using actual complete AL.
Pass a target-owned previously prepared/pinned frontend source build.
The test harness never modifies the supplied build.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,tempfile
ROOT=Path(__file__).resolve().parents[4]
TESTS=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser();p.add_argument('--frontend-build',required=True,type=Path);p.add_argument('--run-dir',type=Path);a=p.parse_args()
    state=ROOT/'_opam-testing-theorems';base=state/'checks';base.mkdir(parents=True,exist_ok=True)
    source=a.frontend_build.resolve()
    if not source.is_relative_to(state/'build') or not (source/'dune-project').is_file():raise ValueError('frontend must be prepared under target build directory')
    run=a.run_dir.resolve() if a.run_dir else Path(tempfile.mkdtemp(prefix='wasm-wrappers.',dir=base))
    if not run.is_relative_to(state):raise ValueError('run must be target-local ignored evidence')
    run.mkdir(parents=True,exist_ok=True);build=run/'frontend';shutil.copytree(source,build)
    backend=build/'p4spec/al_to_coq';backend.mkdir(parents=True,exist_ok=True)
    modules=['context','coq_ir','data','emit_data','casts','render','lower_expr','wasm_bindings']
    for name in modules:shutil.copy2(ROOT/'translator/src'/(name+'.ml'),backend/(name+'.ml'))
    shutil.copy2(TESTS/'wrapper_main.ml',backend/'main.ml')
    (backend/'dune').write_text('(executable (name main) (modules main '+' '.join(modules)+') (libraries pass lang domain util diagnostic yojson unix))\n')
    report={'suite':'builtin-wasm-wrappers','status':'failed','source_build':str(source),'run':str(run),'commands':[],'source_hashes':{}}
    print(f'Wasm adapter evidence: {run}',flush=True)
    def execute(cmd,log,env=None):
        r=subprocess.run(list(map(str,cmd)),cwd=run,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (run/log).write_text(r.stdout);report['commands'].append({'argv':list(map(str,cmd)),'returncode':r.returncode,'log':log})
        if r.returncode:raise RuntimeError(f'{log}: exit {r.returncode}\n{r.stdout[-3500:]}')
    try:
        envcmd=['bash',ROOT/'environment/env.sh','frontend']
        execute(envcmd+['dune','build','--root',build,'-j','2','p4spec/al_to_coq/main.exe'],'build.log')
        gen=run/'generated';gen.mkdir();env=os.environ.copy();env['WASM_WRAPPER_OUTPUT']=str(gen)
        inputs=sorted((ROOT/'specification/wasm/source/spec').glob('*.watsup'))
        execute(envcmd+[build/'_build/default/p4spec/al_to_coq/main.exe']+inputs,'generation.log',env)
        bindings=json.loads((gen/'bindings.json').read_text());assert len(bindings)==74
        report['adapter_count']=len(bindings);report['shared_set_adapter_count']=2
        support=run/'support';support.mkdir();paths=[]
        for name in ['Execution.v','Values.v','Builtins/WasmScalar.v','Builtins/WasmFloat.v','Builtins/WasmVector.v','Builtins/WasmExecution.v']:
            src=ROOT/'translator/coq'/name;target=support/name;target.parent.mkdir(exist_ok=True);shutil.copy2(src,target);paths.append(target)
            report['source_hashes'][name]=hashlib.sha256(src.read_bytes()).hexdigest()
        for name in modules:report['source_hashes'][name+'.ml']=hashlib.sha256((ROOT/'translator/src'/(name+'.ml')).read_bytes()).hexdigest()
        paths.extend([gen/'Types_0000.v',gen/'WasmWrappers.v'])
        for path in paths:
            print(f'Compiling {path.name}',flush=True)
            execute(['bash',ROOT/'environment/env.sh','coqc','-q','-Q',support,'ALCoq','-Q',gen,'WasmSpec.Generated',path],path.stem+'.log')
        report['status']='passed'
    finally:(run/'report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
