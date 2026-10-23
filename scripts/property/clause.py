"""Native SpecTec property clauses: certify, collect, and execute frozen AL."""
from dataclasses import dataclass
import json
import os
from pathlib import Path
import shutil
import subprocess
import tomllib

from scripts.toolchain import (
    PROJECT, BRIDGE_DIRECTORY, TRANSLATOR_DIRECTORY, TOOLCHAIN_SOURCE, PROPERTY_EXECUTABLE,
    PROPERTY_RUN_EXECUTABLE, resolve_toolchain, digest, source_identity,
)
from scripts.lean_tools import require_name, require_timeout, run_checked, rebuild_modules
from scripts.property.plan import compile_clause, identity, select_external
from scripts.property import emit as property_emit
from scripts.observations import validate_observation
from scripts.lean_tools import fingerprint_dependencies



def write_json(path, value):
    Path(path).write_text(json.dumps(value,indent=2,ensure_ascii=False,allow_nan=False)+'\n')


def strict_json(text):
    def pairs(items):
        result={}
        for k,v in items:
            if k in result: raise ValueError('duplicate JSON field '+k)
            result[k]=v
        return result
    def constant(x): raise ValueError('invalid JSON constant '+x)
    return json.loads(text,object_pairs_hook=pairs,parse_constant=constant)


def load_clause(spec_paths, property_path, name, *, project=PROJECT, timeout_seconds=60):
    tool=resolve_toolchain(project)
    exe=tool.root / PROPERTY_EXECUTABLE
    command=[str(exe)]
    for path in spec_paths: command += ['--spec',str(Path(path).resolve())]
    command += ['--property',str(Path(property_path).resolve())]
    payload=strict_json(run_checked(command,project,timeout_seconds))
    matches=[c for c in payload['properties'] if c['name']==name]
    if len(matches)!=1: raise ValueError(f'property {name!r} not found')
    return matches[0]


def contract_audit_source(contract_module, proof_module, property_proof):
    ns=contract_module
    return f'''import Spec4Pbt.GoalTools
import {proof_module}
#spec4pbt_verify {property_proof} in_module {proof_module} : {ns}.property
'''


def audit_native_plan(executable, spec_paths, property_path, name, plan_path, plan_id, project, timeout):
    command=[str(executable)]
    for path in spec_paths:command+=['--spec',str(path)]
    command+=['--property',str(property_path),'--name',name,'--plan',str(plan_path)]
    try:
        result=subprocess.run(command,cwd=project,text=True,capture_output=True,
                              input=json.dumps({'plan_id':plan_id,'mode':'audit','input':None,'trace':[]}),
                              timeout=timeout)
    except subprocess.TimeoutExpired as error:
        raise TimeoutError('native AL effect audit timed out') from error
    if result.returncode:
        raise ValueError('native AL effect audit rejected property: '+result.stderr+result.stdout)
    if strict_json(result.stdout)!={'valid':True}:
        raise ValueError('native AL effect audit returned invalid response')


@dataclass(frozen=True)
class CertifiedProperty:
    project: Path
    directory: Path
    plan: dict
    namespace: str
    module: str
    executable: Path
    spec_paths: tuple[Path, ...]
    property_path: Path
    property_name: str
    toolchain: dict
    fingerprints: dict
    generator_module: str | None = None
    generator: str | None = None

    def assert_fresh(self):
        for file,expected in self.fingerprints.items():
            if not Path(file).is_file() or digest(file)!=expected:
                raise ValueError('certified property is stale: '+file)
        if resolve_toolchain(self.project).identity()!=self.toolchain:
            raise ValueError('certified native toolchain is stale')

    def invoke(self, mode, input_value, trace, index=None, timeout_seconds=60):
        self.assert_fresh()
        request={'plan_id':self.plan['plan_id'],'mode':mode,'input':input_value,'trace':trace}
        if index is not None: request['index']=index
        command=[str(self.executable)]
        for path in self.spec_paths: command+=['--spec',str(path)]
        command+=['--property',str(self.property_path),'--name',self.property_name,
                  '--plan',str(self.directory/'plan.json')]
        try:
            result=subprocess.run(command,cwd=self.project,
                                  text=True,capture_output=True,input=json.dumps(request,allow_nan=False),
                                  timeout=require_timeout(timeout_seconds))
        except subprocess.TimeoutExpired as error:
            raise TimeoutError('property executor timed out') from error
        if result.returncode: raise ValueError('property executor rejected request: '+result.stderr+result.stdout)
        self.assert_fresh()
        return strict_json(result.stdout)

    def evaluate(self,input_value,trace): return self.invoke('check',input_value,trace)['verdict']
    def request(self,input_value,trace,index): return self.invoke('request',input_value,trace,index)
    def validate(self,input_value,trace): return self.invoke('validate',input_value,trace)


def generate_property_files(*, spec_paths, property_path, config_path, external_path,
                            name, output, project=PROJECT, timeout_seconds=120,
                            transport_model=None, namespace=None, audit_plan=True):
    """Generate and audit source artifacts without compiling authored declarations."""
    project=Path(project).resolve();timeout=require_timeout(timeout_seconds)
    spec_paths=[Path(p).absolute() for p in spec_paths]
    property_path=Path(property_path).absolute();config_path=Path(config_path).absolute()
    external_path=Path(external_path).absolute()
    with config_path.open('rb') as f: catalog=tomllib.load(f)
    with external_path.open('rb') as f: selection=tomllib.load(f)
    config=select_external(catalog,selection)
    initial_toolchain=resolve_toolchain(project).identity()
    clause=load_clause(spec_paths,property_path,name,project=project,timeout_seconds=timeout)
    plan=compile_clause(clause,config)
    if plan['unsupported']:
        details=', '.join(f"{entry['relation']}: {entry['reason']}" for entry in plan['unsupported'])
        raise ValueError('property execution plan has unsupported structures: '+details)
    tool=resolve_toolchain(project)
    origins={**source_identity(spec_paths),str(property_path):digest(property_path),
             str(config_path):digest(config_path),str(external_path):digest(external_path)}
    if transport_model is not None:
        transport_model=Path(transport_model).resolve();origins[str(transport_model)]=digest(transport_model)
    output=Path(output)
    if not output.is_absolute(): output=project/output
    output=output.resolve()
    if not output.is_relative_to(project) or output==project: raise ValueError('bundle must be inside the Lean project')
    base=(namespace.rsplit('.',1)[0] if namespace else '.'.join(output.relative_to(project).parts))
    require_name(base)
    namespace=base+'.Contract'
    module=namespace
    output.mkdir(parents=True,exist_ok=True)
    spec=run_checked([str(tool.executable),'--relation-semantics','ordered',
                      *[str(p) for p in spec_paths],str(property_path)],project,timeout)
    (output/'Spec.lean').write_text(spec)
    settings=output/'metadata-config.json'
    write_json(settings,{'schema_version':1,'observations':config.get('observations',[])})
    catalog_settings=output/'catalog-config.json'
    write_json(catalog_settings,catalog)
    model_args=['--transport-model',str(transport_model)] if transport_model else []
    catalog_payload=strict_json(run_checked([str(tool.helper),'--spec-module',base+'.Spec',
        '--namespace',namespace+'CatalogTransport','--config',str(catalog_settings),
        *model_args,*[str(p) for p in spec_paths]],project,timeout))
    write_json(output/'catalog-manifest.json',catalog_payload['manifest'])
    payload=strict_json(run_checked([str(tool.helper),'--spec-module',base+'.Spec','--namespace',namespace+'Transport',
                                    '--config',str(settings),'--property',str(property_path),'--property-name',name,*model_args,*[str(p) for p in spec_paths]],project,timeout))
    # Validate every selected field's type, even if this clause hides the
    # enclosing output as an existential witness.
    observation_config={'schema_version':1,'observations':config.get('observations',[])}
    profiles={p['relation']:p for p in observation_config['observations']}
    for call in plan['calls']:
        selected=validate_observation(observation_config,profiles[call['relation']]['id'],payload['manifest'])
        present={o['selector'] for o in call['observations']}
        for selector,view in zip(profiles[call['relation']]['observe'],selected.selectors):
            if selector not in present:
                call['observations'].append({'selector':selector,'type':{'lean':payload['manifest']['types'][view.type_key]['lean']}})
    # Transport aliases capture the chosen concrete external-type model.
    # Freeze both relation and value types before leaving that namespace.
    def bind_transport(value):
        if isinstance(value,dict):
            if 'key' in value and 'lean' in value:
                entry=payload['manifest']['types'].get(value['key'])
                if entry is not None: value['lean']=entry['lean']
                elif 'SpecTec.' in value['lean']:
                    raise ValueError('missing transport type alias: '+value['key'])
            if value.get('kind')=='relation':
                relation=payload['manifest']['relations'].get(value['relation'])
                if relation is not None:
                    value['lean_relation']=relation['lean']
            for item in value.values(): bind_transport(item)
        elif isinstance(value,list):
            for item in value: bind_transport(item)
    bind_transport(plan)
    plan['plan_id']=identity({k:v for k,v in plan.items() if k!='plan_id'})
    (output/'Transport.lean').write_text(payload['transport'])
    write_json(output/'manifest.json',payload['manifest'])
    write_json(output/'plan.json',plan)
    executable=tool.root / PROPERTY_RUN_EXECUTABLE
    if audit_plan:
        audit_native_plan(executable,spec_paths,property_path,name,output/'plan.json',
                          plan['plan_id'],project,timeout)
    (output/'Contract.lean').write_text(property_emit.render_contract(plan,module,base+'.Transport'))
    if tool.identity()!=initial_toolchain:
        raise ValueError('translator changed during property emission')
    return plan, origins, tool


def build_property(*, spec_paths, property_path, config_path, external_path, name, output,
                   project=PROJECT, timeout_seconds=120, transport_model=None,
                   proof_module=None, property_proof=None):
    for label, value in [('proof_module', proof_module), ('property_proof', property_proof)]:
        if not value:
            raise ValueError(f'{label} is required for property certification')
        require_name(value)
    project=Path(project).resolve();timeout=require_timeout(timeout_seconds)
    spec_paths=[Path(p).absolute() for p in spec_paths]
    property_path=Path(property_path).absolute()
    output=Path(output)
    if not output.is_absolute(): output=project/output
    if os.path.lexists(output): raise FileExistsError('output already exists: '+str(output))
    output=output.resolve()
    if not output.is_relative_to(project) or output==project:
        raise ValueError('bundle must be inside the Lean project')
    base='.'.join(output.relative_to(project).parts)
    require_name(base)
    namespace=module=base+'.Contract'
    try:
        plan, origins, tool=generate_property_files(spec_paths=spec_paths,
            property_path=property_path,config_path=config_path,external_path=external_path,
            name=name,output=output,project=project,timeout_seconds=timeout,
            transport_model=transport_model)
        initial_toolchain=tool.identity()
        executable=tool.root / PROPERTY_RUN_EXECUTABLE
        (output/'ContractAudit.lean').write_text(contract_audit_source(
            module,proof_module,property_proof))
        rebuild_modules(project,[module,proof_module],timeout)
        run_checked(['lake','env','lean',str(output/'ContractAudit.lean')],project,timeout)
        files=fingerprint_dependencies(project,[output/'ContractAudit.lean'],timeout)
        files.update(origins)
        for p in [output/'manifest.json',output/'metadata-config.json',
                  output/'catalog-config.json',output/'catalog-manifest.json']:
            files[str(p)]=digest(p)
        property_directory = Path(__file__).resolve().parent
        tool_sources = [property_directory / name for name in
                        ['plan.py', 'emit.py', 'clause.py', 'runner.py', 'protocol.py']]
        tool_sources += [property_directory.parent / name for name in
                         ['lean_tools.py', '_lean_dependencies.py', 'observations.py']]
        tool_sources += [project / TOOLCHAIN_SOURCE,
                         project / BRIDGE_DIRECTORY / 'property_document.ml',
                         project / BRIDGE_DIRECTORY / 'property_cli.ml',
                         project / BRIDGE_DIRECTORY / 'property_exec.ml']
        files.update({str(path): digest(path) for path in tool_sources})
        files[str(output/'plan.json')]=digest(output/'plan.json')
        files[str(executable)]=digest(executable)
        if tool.identity()!=initial_toolchain:
            raise ValueError('translator changed during property certification')
        certificate={'schema_version':3,'project':str(project),'namespace':namespace,'module':module,
                     'fingerprints':files,'plan_id':plan['plan_id'],'toolchain':tool.identity(),
                     'proof_module':proof_module,'property_proof':property_proof,
                     'spec_paths':[str(p) for p in spec_paths],
                     'property_path':str(property_path),'property_name':name}
        write_json(output/'certificate.json',certificate)
        bundle=CertifiedProperty(project,output,plan,namespace,module,executable,
                                 tuple(spec_paths),property_path,name,tool.identity(),files)
        bundle.assert_fresh()
        return bundle
    except BaseException:
        if output.exists():
            shutil.rmtree(output)
        raise


def load_bundle(directory, *, timeout_seconds=120):
    directory=Path(directory).resolve()
    if not (directory/'certificate.json').is_file():
        raise ValueError('bundle has no certificate; complete the files and run check first')
    cert=strict_json((directory/'certificate.json').read_text())
    if cert.get('schema_version') == 4:
        from scripts.property.workflow import load_checked_bundle
        return load_checked_bundle(directory, cert, timeout_seconds=timeout_seconds)
    plan=strict_json((directory/'plan.json').read_text())
    if cert.get('schema_version')!=3 or type(cert.get('schema_version')) is not int:
        raise ValueError('property certificate schema 3 required; rebuild the bundle with separate implementation metadata')
    if any('adapter' in call for call in plan.get('calls', [])):
        raise ValueError('combined-config plan is obsolete; rebuild the bundle with separate implementation metadata')
    require_name(cert['module']);require_name(cert['namespace'])
    project=Path(cert['project']).resolve()
    if not directory.is_relative_to(project) or cert['module']!='.'.join(directory.relative_to(project).parts)+'.Contract':
        raise ValueError('bundle location does not match its certified module')
    if plan.get('plan_id')!=cert['plan_id'] or cert['plan_id']!=identity({k:v for k,v in plan.items() if k!='plan_id'}): raise ValueError('plan identity mismatch')
    executable=resolve_toolchain(project).root / PROPERTY_RUN_EXECUTABLE
    bundle=CertifiedProperty(project,directory,plan,cert['namespace'],cert['module'],executable,
                             tuple(Path(p) for p in cert['spec_paths']),Path(cert['property_path']),
                             cert['property_name'],cert['toolchain'],cert['fingerprints'])
    bundle.assert_fresh()
    if (directory/'Contract.lean').read_text()!=property_emit.render_contract(plan,bundle.namespace,bundle.module.rsplit('.',1)[0]+'.Transport'):
        raise ValueError('generated contract source mismatch')
    expected_audit=contract_audit_source(bundle.module,cert['proof_module'],
        cert['property_proof'])
    if (directory/'ContractAudit.lean').read_text()!=expected_audit: raise ValueError('audit source mismatch')
    rebuild_modules(bundle.project,[bundle.module,cert['proof_module']],timeout_seconds)
    run_checked(['lake','env','lean',str(directory/'ContractAudit.lean')],bundle.project,timeout_seconds)
    bundle.assert_fresh()
    return bundle


if __name__ == "__main__":
    from scripts.property.cli import main
    raise SystemExit(main())
