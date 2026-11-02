"""Validate per-implementation adapters and freeze their execution provenance.

The snapshot records which files were selected; it does not attest that a
target's response is truthful. Runtime freshness and offline validation are
separate so recheck needs no implementation files.
"""
from dataclasses import dataclass
import json
import os
from pathlib import Path
import shutil
import tomllib

from scripts.toolchain import digest
from scripts.property.plan import identity


SCRIPT_SUFFIXES={'.py','.sh','.rb','.pl'}
OUTCOME_NAMES={'match','unmatch','abort'}


@dataclass(frozen=True)
class RelationBinding:
    relation: str
    command: tuple[str, ...]
    binding_id: str

    @property
    def adapter(self):
        return list(self.command)


@dataclass(frozen=True)
class Implementation:
    _snapshot_json: str
    _bindings: tuple[RelationBinding, ...]

    @property
    def snapshot(self):
        return json.loads(self._snapshot_json)

    @property
    def identity(self):
        return self.snapshot['identity']

    @property
    def cwd(self):
        return Path(self.snapshot['cwd'])

    def for_relation(self, relation):
        for binding in self._bindings:
            if binding.relation==relation:
                return binding
        raise ValueError('missing implementation binding for '+relation)

    def assert_fresh(self):
        snapshot=self.snapshot
        paths={snapshot['manifest']['path']:snapshot['manifest']['sha256']}
        for item in snapshot['bindings'].values():
            paths.update(item['dependencies'])
        for file,expected in paths.items():
            if not Path(file).is_file() or digest(file)!=expected:
                raise ValueError('implementation is stale: '+file)


def _bundle_relations(bundle):
    metadata=json.loads((bundle.directory/'metadata-config.json').read_text())
    catalog=json.loads((bundle.directory/'catalog-config.json').read_text())
    manifest=json.loads((bundle.directory/'manifest.json').read_text())
    catalog_manifest=json.loads((bundle.directory/'catalog-manifest.json').read_text())
    selected={profile['relation'] for profile in metadata['observations']}
    allowed={profile['relation'] for profile in catalog['observations']}
    if not selected <= allowed:
        raise ValueError('selected observation metadata exceeds the specification catalog')
    if allowed != set(catalog_manifest['relations']):
        raise ValueError('catalog observation metadata differs from the specification manifest')
    if not selected <= set(manifest['relations']):
        raise ValueError('observation metadata names a relation absent from the relation manifest')
    return allowed


def _nonempty(value,label):
    if not isinstance(value,str) or not value or '\x00' in value:
        raise ValueError(label+' must be a nonempty string without NUL')
    return value


def _outcomes(value,label):
    if not isinstance(value,dict) or set(value)!=OUTCOME_NAMES:
        raise ValueError(label+' must define match, unmatch, and abort')
    for name,criterion in value.items():
        _nonempty(criterion,label+' '+name)
        if not criterion.strip():
            raise ValueError(label+' '+name+' must describe a nonempty criterion')
    return value


def _file(path,label):
    if not path.is_file():
        raise ValueError(label+' is missing: '+str(path))
    # Follow the invocation path again during freshness checks so retargeted
    # symlinks are detected instead of checking only their former targets.
    return path.absolute()


def _command_dependencies(command,cwd,artifacts):
    executable=Path(command[0])
    if executable.is_absolute() or '/' in command[0]:
        launcher=_file(executable if executable.is_absolute() else cwd/executable,'adapter launcher')
    else:
        search_path=os.pathsep.join(
            str(Path(part) if Path(part).is_absolute() else cwd/part)
            for part in os.get_exec_path())
        resolved=shutil.which(command[0],path=search_path)
        if resolved is None:
            raise ValueError('adapter launcher is missing: '+command[0])
        launcher=_file(Path(resolved),'adapter launcher')
    files=[launcher]
    launcher_name=Path(command[0]).name
    if launcher_name.startswith('python') or launcher_name in {'sh','bash','ruby','perl'}:
        for arg in command[1:]:
            if arg in {'-c','-m','-e'}:
                break
            if not arg.startswith('-'):
                files.append(_file(Path(arg) if Path(arg).is_absolute() else cwd/arg,'adapter script'))
                break
    for arg in command[1:]:
        if Path(arg).suffix in SCRIPT_SUFFIXES:
            files.append(_file(Path(arg) if Path(arg).is_absolute() else cwd/arg,'adapter script'))
    for artifact in artifacts:
        files.append(_file(Path(artifact) if Path(artifact).is_absolute() else cwd/artifact,'artifact'))
    return [str(launcher),*command[1:]], {str(path):digest(path) for path in files}


def load_implementation(path,bundle):
    """Preflight a manifest against certified metadata and used AL calls."""
    path=_file(Path(path).absolute(),'implementation manifest')
    with path.open('rb') as source:
        document=tomllib.load(source)
    if set(document)-{'schema_version','id','cwd','executions'}:
        raise ValueError('invalid implementation manifest field')
    version=document.get('schema_version')
    if type(version) is not int or version not in (1,2):
        raise ValueError('implementation schema_version 1 or 2 required')
    name=_nonempty(document.get('id'),'implementation id')
    cwd_value=_nonempty(document.get('cwd','.'),'implementation cwd')
    cwd=(path.parent/cwd_value).resolve()
    if not cwd.is_dir():
        raise ValueError('implementation cwd is missing: '+str(cwd))
    entries=document.get('executions')
    if not isinstance(entries,list):
        raise ValueError('implementation executions must be an array')
    external=_bundle_relations(bundle)
    bindings={}
    for entry in entries:
        if not isinstance(entry,dict) or set(entry)-{'relation','adapter','artifacts','outcomes'} or not {'relation','adapter'}<=set(entry):
            raise ValueError('invalid implementation execution field')
        if version==2 and 'outcomes' not in entry:
            raise ValueError('implementation outcomes are required by schema_version 2')
        relation=_nonempty(entry['relation'],'execution relation')
        if relation in bindings:
            raise ValueError('duplicate implementation binding for '+relation)
        if relation not in external:
            raise ValueError('implementation relation is unknown or internal: '+relation)
        command=entry['adapter']
        if not isinstance(command,list) or not command or any(not isinstance(arg,str) or not arg or '\x00' in arg for arg in command):
            raise ValueError('adapter must be a nonempty argv array without NUL')
        artifacts=entry.get('artifacts',[])
        if not isinstance(artifacts,list) or any(not isinstance(arg,str) or not arg or '\x00' in arg for arg in artifacts):
            raise ValueError('artifacts must be nonempty file paths without NUL')
        command,dependencies=_command_dependencies(command,cwd,artifacts)
        record={'adapter':command,'dependencies':dependencies}
        if 'outcomes' in entry:
            record['outcomes']=_outcomes(entry['outcomes'],'implementation outcomes')
        record['binding_id']=identity({'relation':relation,**record})
        bindings[relation]=record
    used={call['relation'] for call in bundle.plan['calls']}
    if missing:=used-set(bindings):
        raise ValueError('missing implementation binding for '+', '.join(sorted(missing)))
    snapshot={'schema_version':1,'id':name,'cwd':str(cwd),
              'manifest':{'path':str(path),'sha256':digest(path)},'bindings':bindings}
    snapshot['identity']=identity(snapshot)
    frozen=json.dumps(snapshot,sort_keys=True,ensure_ascii=False,separators=(',',':'))
    result=Implementation(frozen,tuple(RelationBinding(r,tuple(b['adapter']),b['binding_id']) for r,b in bindings.items()))
    result.assert_fresh()
    return result


def validate_snapshot(snapshot,bundle):
    """Validate saved provenance without reading its manifest or dependency files."""
    if not isinstance(snapshot,dict) or set(snapshot)!={'schema_version','id','cwd','manifest','bindings','identity'}:
        raise ValueError('invalid saved implementation snapshot')
    if type(snapshot['schema_version']) is not int or snapshot['schema_version']!=1:
        raise ValueError('invalid saved implementation snapshot schema')
    _nonempty(snapshot['id'],'saved implementation id')
    _nonempty(snapshot['cwd'],'saved implementation cwd')
    manifest=snapshot['manifest']
    if not isinstance(manifest,dict) or set(manifest)!={'path','sha256'}:
        raise ValueError('invalid saved implementation manifest identity')
    _nonempty(manifest['path'],'saved implementation manifest path')
    _nonempty(manifest['sha256'],'saved implementation manifest digest')
    bindings=snapshot['bindings']
    if not isinstance(bindings,dict):
        raise ValueError('invalid saved implementation bindings')
    external=_bundle_relations(bundle)
    if not set(bindings)<=external or not {c['relation'] for c in bundle.plan['calls']}<=set(bindings):
        raise ValueError('saved implementation binding coverage mismatch')
    for relation,record in bindings.items():
        if not isinstance(record,dict) or set(record) not in (
            {'adapter','dependencies','binding_id'},
            {'adapter','dependencies','outcomes','binding_id'}):
            raise ValueError('invalid saved implementation binding')
        command=record['adapter']
        if not isinstance(command,list) or not command or any(not isinstance(x,str) or not x for x in command):
            raise ValueError('invalid saved implementation adapter')
        deps=record['dependencies']
        if not isinstance(deps,dict) or not deps or any(not isinstance(k,str) or not isinstance(v,str) or not k or not v for k,v in deps.items()):
            raise ValueError('invalid saved implementation dependencies')
        payload={'relation':relation,'adapter':command,'dependencies':deps}
        if 'outcomes' in record:
            payload['outcomes']=_outcomes(record['outcomes'],'saved implementation outcomes')
        if record['binding_id']!=identity(payload):
            raise ValueError('saved implementation binding identity mismatch')
    if snapshot['identity']!=identity({k:v for k,v in snapshot.items() if k!='identity'}):
        raise ValueError('saved implementation identity mismatch')
    return snapshot
