"""Collect external occurrences, then check the frozen trace with SpecTec AL."""
from dataclasses import dataclass,asdict
from pathlib import Path
import os
import tempfile
from pbt.property.clause import CertifiedProperty,load_bundle,strict_json,write_json
from pbt.property.protocol import execute,validate_response
from pbt.property.implementation import Implementation,load_implementation,validate_snapshot
from pbt.lean_tools import require_name,require_timeout,rebuild_modules,run_checked
from pbt.lean_tools import fingerprint_dependencies
from translator.toolchain import digest, SCRATCH_DIRECTORY


@dataclass(frozen=True)
class CaseResult:
    verdict: str
    case_dir: Path
    trace_path: Path
    error: str | None = None
    reason: str | None = None


@dataclass(frozen=True)
class RunSummary:
    status: str
    counts: dict
    requested: int
    completed: int
    output: Path


def bundle_value(bundle):
    return bundle if isinstance(bundle,CertifiedProperty) else load_bundle(bundle)


def fresh(files):
    for path,expected in files.items():
        if not Path(path).is_file() or digest(path)!=expected:
            raise ValueError('certified sampler is stale: '+path)


def implementation_value(implementation,bundle):
    selected=(implementation if isinstance(implementation,Implementation)
              else load_implementation(implementation,bundle))
    validate_snapshot(selected.snapshot,bundle)
    selected.assert_fresh()
    return selected


def collect_case(bundle,input_value,output,*,implementation,case_id='0',timeout_seconds=10):
    bundle=bundle_value(bundle);bundle.assert_fresh();require_timeout(timeout_seconds)
    implementation=implementation_value(implementation,bundle)
    output=Path(output).resolve()
    if os.path.lexists(output): raise FileExistsError('case output already exists: '+str(output))
    output.mkdir(parents=True)
    entries=[];errors=[]
    for i,call in enumerate(bundle.plan['calls']):
        bundle.assert_fresh()
        implementation.assert_fresh()
        binding=implementation.for_relation(call['relation'])
        projected=bundle.request(input_value,entries,i)
        entry={'occurrence_id':call['id'],'relation_id':call['relation'],'input':None,
               'binding_id':binding.binding_id,'status':'blocked','observation':{},'raw_response':None,'error':None}
        if projected['ready']:
            entry['input']=projected['input']
            request={'plan_id':bundle.plan['plan_id'],'case_id':str(case_id),'occurrence_id':call['id'],
                     'relation_id':call['relation'],'input':projected['input'],'observe':call['profile_selectors']}
            directory=output/f'call-{i:03d}';directory.mkdir()
            write_json(directory/'request.json',request)
            reply,process,error=execute(binding.adapter,request,cwd=implementation.cwd,timeout_seconds=timeout_seconds)
            implementation.assert_fresh()
            write_json(directory/'process.json',process)
            if error:
                entry['status']='execution_error';entry['error']=error;errors.append(error)
            else:
                write_json(directory/'response.json',reply)
                entry.update(status=reply['status'],observation=reply.get('observation',{}),raw_response=reply)
                try: bundle.validate(input_value,[*entries,entry])
                except ValueError as e:
                    entry.update(status='execution_error',observation={},error=str(e))
                    errors.append(str(e));write_json(directory/'decode-error.json',{'error':str(e)})
        entries.append(entry)
    # The checker is first called after every external occurrence has an entry.
    trace={'schema_version':3,'plan_id':bundle.plan['plan_id'],'certificate_sha256':digest(bundle.directory/'certificate.json'),
           'implementation':implementation.snapshot,
           'case_id':str(case_id),'input':input_value,'entries':entries}
    trace_path=output/'trace.json';write_json(trace_path,trace)
    try:
        checked=bundle.invoke('check',input_value,entries)
        verdict,reason=checked['verdict'],checked.get('reason')
    except (ValueError,TimeoutError) as failure:
        errors.append(str(failure))
        verdict,reason='error','al_execution_error'
    result=CaseResult(verdict,output,trace_path,'; '.join(errors) if errors else None,reason)
    write_json(output/'result.json',{**asdict(result),'case_dir':str(output),'trace_path':str(trace_path)})
    return result


def validate_saved_trace(bundle,record):
    if record.get('schema_version')!=3 or type(record.get('schema_version')) is not int:
        raise ValueError('property trace schema 3 required; rebuild and rerun old traces')
    snapshot=validate_snapshot(record.get('implementation'),bundle)
    if record.get('plan_id')!=bundle.plan['plan_id'] or record.get('certificate_sha256')!=digest(bundle.directory/'certificate.json'):
        raise ValueError('saved trace certificate or plan identity mismatch')
    if not isinstance(record.get('entries'),list) or len(record['entries'])!=len(bundle.plan['calls']):
        raise ValueError('saved trace occurrence list is incomplete')
    for call,entry in zip(bundle.plan['calls'],record['entries']):
        fields={'occurrence_id','relation_id','input','binding_id','status',
                'observation','raw_response','error'}
        if not isinstance(entry,dict) or set(entry)!=fields:
            raise ValueError('invalid saved trace entry fields')
        if entry['occurrence_id']!=call['id'] or entry['relation_id']!=call['relation']:
            raise ValueError('saved trace occurrence identity mismatch')
        if entry.get('binding_id')!=snapshot['bindings'][call['relation']]['binding_id']:
            raise ValueError('saved occurrence binding identity mismatch')
        response=entry.get('raw_response')
        if response is None:
            if entry.get('status')=='execution_error':
                if entry['input'] is None or entry['observation']!={} or not isinstance(entry.get('error'),str) or not entry['error']:
                    raise ValueError('execution error cause missing from trace')
            elif entry.get('status')!='blocked' or entry.get('error') is not None or entry['input'] is not None or entry['observation']!={}:
                raise ValueError('missing raw response for external occurrence')
            continue
        if entry.get('input') is None:
            raise ValueError('recorded external request missing')
        request={'plan_id':record['plan_id'],'case_id':record['case_id'],
                 'occurrence_id':call['id'],'relation_id':call['relation'],
                 'input':entry['input'],'observe':call['profile_selectors']}
        try:
            validate_response(response,request)
        except ValueError as error:
            raise ValueError('invalid raw response: '+str(error)) from error
        if entry['status']=='execution_error':
            if entry['observation']!={} or not isinstance(entry.get('error'),str) or not entry['error']:
                raise ValueError('decode error cause missing from trace')
        elif entry.get('error') is not None:
            raise ValueError('normal adapter response has unexpected trace error')
        elif entry.get('status')!=response['status'] or entry.get('observation')!=response.get('observation',{}):
            raise ValueError('raw response and trace observation mismatch')


def recheck_trace(bundle,trace):
    bundle=bundle_value(bundle)
    trace_path=Path(trace).resolve();record=strict_json(trace_path.read_text())
    validate_saved_trace(bundle,record)
    bundle.validate(record['input'],record['entries'])
    errors=[e['error'] for e in record['entries'] if e.get('error')]
    try:
        checked=bundle.invoke('check',record['input'],record['entries'])
        verdict,reason=checked['verdict'],checked.get('reason')
    except (ValueError,TimeoutError) as failure:
        errors.append(str(failure))
        verdict,reason='error','al_execution_error'
    return CaseResult(verdict,trace_path.parent,trace_path,'; '.join(errors) or None,reason)


def rerun_case(bundle,case,output,*,implementation,timeout_seconds=10):
    bundle=bundle_value(bundle)
    record=strict_json((Path(case)/'trace.json').read_text())
    validate_saved_trace(bundle,record)
    # Recompute later requests from newly observed outputs, never old requests.
    return collect_case(bundle,record['input'],output,implementation=implementation,timeout_seconds=timeout_seconds)


def sample_inputs(bundle,generator_module,generator,*,count,size,seed,timeout_seconds):
    require_name(generator_module);require_name(generator);require_timeout(timeout_seconds)
    for key,value,minimum in [('count',count,1),('size',size,0),('seed',seed,0)]:
        if type(value) is not int or value<minimum: raise ValueError(f'{key} must be an integer >= {minimum}')
    bundle.assert_fresh()
    ns=bundle.namespace
    rebuild_modules(bundle.project,['Spec4Pbt.Observable',generator_module,bundle.module],timeout_seconds)
    base=bundle.project/SCRATCH_DIRECTORY;base.mkdir(parents=True,exist_ok=True)
    directory=Path(tempfile.mkdtemp(prefix='sampler-',dir=base))
    audit=directory/'Audit.lean'
    audit.write_text(f'''import Spec4Pbt.Observable
import Spec4Pbt.CorrectGen
import {bundle.module}
import {generator_module}
#spec4pbt_verify {generator} in_module {generator_module} : (CorrectGen {ns}.Premise)
#spec4pbt_observable_executable {generator}
#spec4pbt_observable_transport {ns}.encodeInput
''')
    driver=directory/'Driver.lean'
    driver.write_text(f'''import {bundle.module}
import {generator_module}
open Lean

def main : IO Unit := do
  let config : SampleConfig := {{ sizeLimit := {size}, backtrackLimit := 100, sizeRetryLimit := 100 }}
  for index in [:{count}] do
    let value : {ns}.Input ← Plausible.runRandWith ({seed} + index) (SampleM.sampleRand config {generator}.val)
    (← IO.getStdout).putStrLn (Json.mkObj [("index",toJson index),("input",{ns}.encodeInput value)]).compress
''')
    fingerprints=fingerprint_dependencies(bundle.project,[audit,driver],timeout_seconds)
    run_checked(['lake','env','lean',str(audit)],bundle.project,timeout_seconds)
    text=run_checked(['lake','env','lean','--run',str(driver)],bundle.project,timeout_seconds)
    fresh(fingerprints)
    samples=[strict_json(line) for line in text.splitlines()]
    if len(samples)!=count:raise ValueError('sampler count mismatch')
    for i,s in enumerate(samples):
        if set(s)!={'index','input'} or type(s['index']) is not int or s['index']!=i:
            raise ValueError('sampler protocol mismatch')
    return samples,fingerprints


def run_property(bundle,*,implementation,generator_module,generator,output,count=100,size=10,seed=0,
                 timeout_seconds=120,adapter_timeout_seconds=10):
    bundle=bundle_value(bundle);require_timeout(adapter_timeout_seconds)
    implementation=implementation_value(implementation,bundle)
    output=Path(output).resolve()
    if os.path.lexists(output):raise FileExistsError('run output already exists: '+str(output))
    samples,fingerprints=sample_inputs(bundle,generator_module,generator,count=count,size=size,seed=seed,timeout_seconds=timeout_seconds)
    output.mkdir(parents=True)
    write_json(output/'samples.json',samples)
    write_json(output/'run.json',{'plan_id':bundle.plan['plan_id'],'generator_module':generator_module,
                                'generator':generator,'count':count,'size':size,'seed':seed,
                                'adapter_timeout_seconds':adapter_timeout_seconds,'sampler_dependencies':fingerprints,
                                'implementation':implementation.snapshot})
    counts={k:0 for k in ['pass','fail','error']}
    for sample in samples:
        fresh(fingerprints)
        implementation.assert_fresh()
        result=collect_case(bundle,sample['input'],output/f'case-{sample["index"]:06d}',
                            implementation=implementation,case_id=str(sample['index']),timeout_seconds=adapter_timeout_seconds)
        counts[result.verdict]+=1
        if result.verdict=='error':break
    status='error' if counts['error'] else 'failed' if counts['fail'] else 'passed' if counts['pass'] else 'error'
    summary=RunSummary(status,counts,count,sum(counts.values()),output)
    write_json(output/'result.json',{**asdict(summary),'output':str(output)})
    return summary
