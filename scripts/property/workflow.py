"""Emit visible obligations, certify completed declarations, and load checked bundles."""
from pathlib import Path
import os
import tempfile

from scripts.toolchain import (
    PROJECT, SCRATCH_DIRECTORY, BRIDGE_DIRECTORY, TRANSLATOR_DIRECTORY, TOOLCHAIN_SOURCE,
    PROPERTY_RUN_EXECUTABLE, digest, resolve_toolchain,
)
from scripts.lean_tools import (
    require_name, require_timeout, rebuild_modules, run_checked, fingerprint_dependencies,
)
from scripts.property.clause import (
    CertifiedProperty, generate_property_files, contract_audit_source, strict_json, write_json,
)
from scripts.property.emit import render_contract
from scripts.property.plan import identity


GENERATED_FILES = (
    'Helpers.lean', 'Transport.lean', 'Contract.lean', 'plan.json', 'manifest.json',
    'metadata-config.json', 'catalog-config.json', 'catalog-manifest.json',
    'ContractAudit.lean', 'GeneratorAudit.lean',
)


def generator_audit_source(contract_module, generator_module, generator):
    return f'''import Spec4Pbt.Observable
import {contract_module}
import {generator_module}
#spec4pbt_verify {generator} in_module {generator_module} : {contract_module}.generator
#spec4pbt_observable_executable {generator}
#spec4pbt_observable_transport {contract_module}.encodeInput
'''


def _bundle_path(path, project):
    path = Path(path)
    if not path.is_absolute():
        path = project / path
    if any(parent.is_symlink() for parent in [path, *path.parents] if parent != project):
        raise ValueError('generated bundle directory must not be a symlink')
    path = path.resolve()
    if not path.is_relative_to(project):
        raise ValueError('generated bundle must be inside the project')
    relative = path.relative_to(project)
    property_bundle = len(relative.parts) == 3 and relative.parts[0] == 'properties' and relative.parts[2] == 'bundle'
    scratch = project / SCRATCH_DIRECTORY
    if not property_bundle and not (path.is_relative_to(scratch) and path != scratch):
        raise ValueError('generated bundle must be properties/<name>/bundle or below build/scratch')
    require_name('.'.join(relative.parts))
    return path


def _module_path(module, project):
    require_name(module)
    path = project.joinpath(*module.split('.')).with_suffix('.lean')
    if path.is_symlink() or not path.resolve().is_relative_to(project):
        raise ValueError('authored module must be inside the project without a symlink')
    if path.exists() and not path.is_file():
        raise ValueError('authored module path must be a regular file: '+str(path))
    return path


def _declarations(project, property_path, proof_module, property_proof, generator_module, generator):
    parent = property_path.parent
    if not parent.is_relative_to(project):
        if proof_module is None or generator_module is None:
            raise ValueError('external property source requires explicit authored module names')
    else:
        prefix = '.'.join(parent.relative_to(project).parts)
        proof_module = proof_module or (prefix + '.Proof' if prefix else 'Proof')
        generator_module = generator_module or (prefix + '.Generator' if prefix else 'Generator')
    values = dict(proof_module=proof_module, property_proof=property_proof or proof_module+'.property_correct',
                  generator_module=generator_module, generator=generator or generator_module+'.generator')
    for value in values.values():
        require_name(value)
    if proof_module == generator_module:
        raise ValueError('proof and generator must use separate authored modules')
    return values


def _template(contract, declaration, kind):
    namespace, _, name = declaration.rpartition('.')
    target = 'property' if kind == 'theorem' else 'generator'
    lines = [f'import {contract}', '', '-- Generated unfinished obligation: complete this declaration.']
    if namespace:
        lines += [f'namespace {namespace}', '']
    lines += [f'{kind} {name} : {contract}.{target} := by',
              f'  fail "Fill in the {target} obligation before running check"', '']
    if namespace:
        lines += [f'end {namespace}', '']
    return '\n'.join(lines)


def _audit_files(directory, module, declarations):
    (directory/'ContractAudit.lean').write_text(contract_audit_source(
        module, declarations['proof_module'], declarations['property_proof']))
    (directory/'GeneratorAudit.lean').write_text(generator_audit_source(
        module, declarations['generator_module'], declarations['generator']))


def _fresh(fingerprints, description):
    for name, expected in fingerprints.items():
        path = Path(name)
        if not path.is_file() or digest(path) != expected:
            raise ValueError(f'{description} is stale: {path}')


def _tool_fingerprints(project):
    directory = Path(__file__).resolve().parent
    paths = [directory/name for name in
             ['workflow.py', 'clause.py', 'cli.py', 'emit.py', 'plan.py', 'runner.py', 'protocol.py', 'implementation.py']]
    paths += [directory.parent/'lean_tools.py', directory.parent/'_lean_dependencies.py', directory.parent/'observations.py', directory.parent/'specification.py',
              project/TOOLCHAIN_SOURCE]
    paths += [project/BRIDGE_DIRECTORY/name for name in
              ['property_document.ml', 'property_cli.ml', 'property_exec.ml']]
    return {str(path): digest(path) for path in paths}


def emit_property(*, spec_paths, property_path, config_path, external_path, name, output=None,
                  project=PROJECT, timeout_seconds=120, transport_model=None,
                  proof_module=None, property_proof=None, generator_module=None, generator=None):
    """Generate obligations without certifying or overwriting authored declarations."""
    project = Path(project).resolve()
    timeout = require_timeout(timeout_seconds)
    property_path = Path(property_path).resolve()
    output = _bundle_path(output if output is not None else property_path.parent/'bundle', project)
    declarations = _declarations(project, property_path, proof_module, property_proof, generator_module, generator)
    module = '.'.join(output.relative_to(project).parts) + '.Contract'
    authored = [_module_path(declarations[key], project) for key in ['proof_module', 'generator_module']]
    generated_paths = {output/name for name in (*GENERATED_FILES, 'emission.json', 'certificate.json')}
    if any(path.resolve() in generated_paths or path.resolve() == property_path for path in authored):
        raise ValueError('authored module collides with a generated file or property source')
    if output.exists() and not (output/'emission.json').is_file():
        raise FileExistsError('output already exists without emission metadata: '+str(output))
    for path in generated_paths:
        if path.is_symlink() or (path.exists() and not path.is_file()):
            raise ValueError('generated file path is not a regular file: '+str(path))
    request = dict(spec_paths=[str(Path(path).resolve()) for path in spec_paths],
                   property_path=str(property_path), config_path=str(Path(config_path).resolve()),
                   external_path=str(Path(external_path).resolve()), name=name,
                   transport_model=str(Path(transport_model).resolve()) if transport_model else None)
    scratch = project/SCRATCH_DIRECTORY
    scratch.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='emit-', dir=scratch) as tmp:
        stage = Path(tmp)
        _, origins, tool = generate_property_files(**request, output=stage, project=project,
            timeout_seconds=timeout, namespace=module, audit_plan=False)
        _audit_files(stage, module, declarations)
        record = dict(schema_version=1, project=str(project), module=module,
                      request=request, declarations=declarations, sources=origins,
                      toolchain=tool.identity(),
                      generated={name: digest(stage/name) for name in GENERATED_FILES})
        write_json(stage/'emission.json', record)
        output.mkdir(parents=True, exist_ok=True)
        (output/'certificate.json').unlink(missing_ok=True)
        for name in (*GENERATED_FILES, 'emission.json'):
            # Replacing the directory entry also preserves any authored file
            # accidentally hardlinked to the previous generated artifact.
            os.replace(stage/name, output/name)
    for path, kind, key in zip(authored, ['theorem', 'def'], ['property_proof', 'generator']):
        path.parent.mkdir(parents=True, exist_ok=True)
        try:
            with path.open('x') as file:
                file.write(_template(module, declarations[key], kind))
        except FileExistsError:
            pass
    return output


def _read_emission(directory):
    record = strict_json((directory/'emission.json').read_text())
    if type(record.get('schema_version')) is not int or record['schema_version'] != 1:
        raise ValueError('emission schema 1 required; run emit again')
    project = Path(record['project']).resolve()
    if _bundle_path(directory, project) != directory:
        raise ValueError('emission location mismatch')
    module = '.'.join(directory.relative_to(project).parts)+'.Contract'
    if record['module'] != module:
        raise ValueError('emission module location mismatch')
    for value in record['declarations'].values():
        require_name(value)
    for key in ['proof_module', 'generator_module']:
        _module_path(record['declarations'][key], project)
    if record['declarations']['proof_module'] == record['declarations']['generator_module']:
        raise ValueError('proof and generator must use separate authored modules')
    return record, project


def _assert_proof_independent(project, declarations, graph):
    proof = str(_module_path(declarations['proof_module'], project).resolve())
    generator = str(_module_path(declarations['generator_module'], project).resolve())
    pending = [proof]
    seen = set()
    while pending:
        source = pending.pop()
        if source == generator:
            raise ValueError('proof must not depend on the generator module, directly or transitively')
        if source not in seen:
            seen.add(source)
            pending.extend(graph.get(source, []))


def _validate_generated(directory, record, project, timeout):
    """Bind metadata to the actual selected source, not to editable hash claims."""
    _fresh(record['sources'], 'emitted source; run emit again')
    if resolve_toolchain(project).identity() != record['toolchain']:
        raise ValueError('emitted toolchain is stale; run emit again')
    module = record['module']
    declarations = record['declarations']
    scratch = project/SCRATCH_DIRECTORY
    with tempfile.TemporaryDirectory(prefix='check-', dir=scratch) as tmp:
        stage = Path(tmp)
        plan, origins, tool = generate_property_files(**record['request'], output=stage,
            project=project, timeout_seconds=timeout, namespace=module, verify_shared=True)
        _audit_files(stage, module, declarations)
        for name in GENERATED_FILES:
            if (directory/name).read_bytes() != (stage/name).read_bytes():
                raise ValueError('generated source mismatch: '+name+'; run emit again')
    return plan, origins, tool


def check_property(directory, *, timeout_seconds=120):
    """Reconstruct generated source and certify both completed declarations."""
    directory = Path(directory).resolve()
    record, project = _read_emission(directory)
    (directory/'certificate.json').unlink(missing_ok=True)
    timeout = require_timeout(timeout_seconds)
    plan, origins, tool = _validate_generated(directory, record, project, timeout)
    module = record['module']
    declarations = record['declarations']
    rebuild_modules(project, ['Spec4Pbt.Observable', module, declarations['proof_module'],
                              declarations['generator_module']], timeout)
    roots = [directory/'ContractAudit.lean', directory/'GeneratorAudit.lean']
    graph = {}
    files = fingerprint_dependencies(project, roots, timeout, dependency_graph=graph)
    _assert_proof_independent(project, declarations, graph)
    files.update(origins)
    files.update(_tool_fingerprints(project))
    files.update({str(directory/name): digest(directory/name) for name in (*GENERATED_FILES, 'emission.json')})
    executable = tool.root/PROPERTY_RUN_EXECUTABLE
    files[str(executable)] = digest(executable)
    for audit in roots:
        run_checked(['lake', 'env', 'lean', str(audit)], project, timeout)
    _fresh(files, 'checked dependency')
    if tool.identity() != record['toolchain']:
        raise ValueError('translator changed during certification')
    request = record['request']
    certificate = dict(schema_version=4, project=str(project), namespace=module, module=module,
        fingerprints=files, plan_id=plan['plan_id'], toolchain=tool.identity(), **declarations,
        spec_paths=request['spec_paths'], property_path=request['property_path'], property_name=request['name'])
    write_json(directory/'certificate.json', certificate)
    return load_checked_bundle(directory, certificate, timeout_seconds=timeout, _just_checked=True)


def load_checked_bundle(directory, certificate, *, timeout_seconds=120, _just_checked=False):
    """Load the already checked pair; file freshness binds source and executable artifacts."""
    require_timeout(timeout_seconds)
    record, project = _read_emission(directory)
    if type(certificate.get('schema_version')) is not int or certificate['schema_version'] != 4:
        raise ValueError('joint certificate schema 4 required; run check')
    module = record['module']
    if certificate['module'] != module or certificate['namespace'] != module or certificate['project'] != str(project):
        raise ValueError('certificate module location mismatch')
    for key, value in record['declarations'].items():
        if certificate.get(key) != value:
            raise ValueError('certificate declaration mismatch: '+key)
    request = record['request']
    if (certificate['spec_paths'] != request['spec_paths']
            or certificate['property_path'] != request['property_path']
            or certificate['property_name'] != request['name']
            or certificate['toolchain'] != record['toolchain']):
        raise ValueError('certificate source selection mismatch')
    plan = strict_json((directory/'plan.json').read_text())
    if plan.get('plan_id') != certificate['plan_id'] or plan['plan_id'] != identity({k:v for k,v in plan.items() if k!='plan_id'}):
        raise ValueError('plan identity mismatch')
    bundle = CertifiedProperty(project, directory, plan, module, module,
        resolve_toolchain(project).root/PROPERTY_RUN_EXECUTABLE,
        tuple(Path(path) for path in certificate['spec_paths']), Path(certificate['property_path']),
        certificate['property_name'], certificate['toolchain'], certificate['fingerprints'],
        certificate['generator_module'], certificate['generator'])
    bundle.assert_fresh()
    if (directory/'Contract.lean').read_text() != render_contract(plan, module, module.rsplit('.',1)[0]+'.Transport'):
        raise ValueError('generated contract source mismatch')
    declarations = record['declarations']
    if (directory/'ContractAudit.lean').read_text() != contract_audit_source(
            module, declarations['proof_module'], declarations['property_proof']):
        raise ValueError('property audit source mismatch')
    if (directory/'GeneratorAudit.lean').read_text() != generator_audit_source(
            module, declarations['generator_module'], declarations['generator']):
        raise ValueError('generator audit source mismatch')
    if not _just_checked:
        # Certificates are editable local data. Repeat the Lean audits when
        # loading, so repaired/omitted hashes cannot attest a different proof.
        _validate_generated(directory, record, project, timeout_seconds)
        rebuild_modules(project, ['Spec4Pbt.Observable', module, declarations['proof_module'],
                                  declarations['generator_module']], timeout_seconds)
        roots = [directory/'ContractAudit.lean', directory/'GeneratorAudit.lean']
        graph = {}
        current = fingerprint_dependencies(project, roots, timeout_seconds, dependency_graph=graph)
        _assert_proof_independent(project, declarations, graph)
        for audit in roots:
            run_checked(['lake', 'env', 'lean', str(audit)], project, timeout_seconds)
        _fresh(current, 'audited dependency')
        bundle.assert_fresh()
        # Require the recorded closure to cover every dependency just audited.
        if any(certificate['fingerprints'].get(path) != value for path, value in current.items()):
            raise ValueError('certificate dependency closure mismatch; run check again')
    return bundle
