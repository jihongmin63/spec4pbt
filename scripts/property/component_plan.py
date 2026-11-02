"""Check conditional generator component contracts against a typed property premise.

This module deliberately does not certify that a generator implements a component.
It checks the structure of a plan and elaborates its connection and final-goal
implications in Lean using the existing proof audit.
"""
from __future__ import annotations

import hashlib
from pathlib import Path
import re
import tomllib

from scripts.toolchain import PROJECT, SCRATCH_DIRECTORY, digest, source_identity
from scripts.lean_tools import elaborate, rebuild_modules, require_name, require_timeout
from scripts.property.clause import strict_json, load_clause
from scripts.property.plan import compile_clause, select_external
from scripts.property.emit import render_contract


ID = re.compile(r"[A-Za-z][A-Za-z0-9_]*\Z")
SHA = re.compile(r"[0-9a-f]{64}\Z")


def _id(value, label):
    if not isinstance(value, str) or not ID.fullmatch(value):
        raise ValueError(f"invalid {label}: {value!r}")
    return value


def _list(value, label):
    if not isinstance(value, list) or any(not isinstance(item, str) for item in value) or len(value) != len(set(value)):
        raise ValueError(f"{label} must be a duplicate-free list")
    return value


def _records(value, label):
    if not isinstance(value, list) or any(not isinstance(item, dict) for item in value):
        raise ValueError(f'{label} must be a list of objects')
    return value


def _term(value, label):
    if not isinstance(value, str) or not value.strip() or '\n' in value or '\r' in value:
        raise ValueError(f"{label} must be a nonempty single-line Lean term")
    return value


def _source(project, item):
    if not isinstance(item, dict) or set(item) != {'path', 'sha256', 'symbol'}:
        raise ValueError('implementation reference needs path, sha256, symbol')
    if not isinstance(item['path'], str) or not isinstance(item['sha256'], str):
        raise ValueError('invalid implementation reference path or hash')
    path = project / item['path']
    if path.is_symlink() or not path.resolve().is_relative_to(project):
        raise ValueError('implementation reference must be a regular project file')
    if not path.is_file() or not SHA.fullmatch(item['sha256']) or digest(path) != item['sha256']:
        raise ValueError(f"implementation reference is missing or stale: {path}")
    symbol = _id(item['symbol'], 'implementation symbol')
    if not re.search(r'(?m)^\s*(?:def|abbrev|theorem|structure)\s+' + re.escape(symbol) + r'\b', path.read_text()):
        raise ValueError(f"implementation symbol {symbol} not found in {path}")


def _validate(plan, project):
    if not isinstance(plan, dict) or set(plan) != {'schema_version', 'target', 'contract_module', 'imports', 'implementation_refs', 'values', 'components', 'connections', 'final'} or plan['schema_version'] != 1:
        raise ValueError('unsupported component plan schema')
    contract = require_name(plan['contract_module'])
    contract_path = project.joinpath(*contract.split('.')).with_suffix('.lean')
    if contract_path.is_symlink() or not contract_path.is_file():
        raise ValueError(f'missing typed property contract: {contract_path}')
    target = plan['target']
    if not isinstance(target, dict) or set(target) != {'spec', 'property', 'name', 'config', 'external', 'type_aliases', 'source_sha256', 'lean_sha256'}:
        raise ValueError('target needs original property selection and source fingerprint')
    if not isinstance(target['lean_sha256'], dict) or not target['lean_sha256']:
        raise ValueError('target lean_sha256 is required')
    if str(contract_path.relative_to(project)) not in target['lean_sha256']:
        raise ValueError('target must fingerprint its typed Contract')
    for name, expected in target['lean_sha256'].items():
        if not isinstance(name, str) or not isinstance(expected, str) or Path(name).is_absolute() or not SHA.fullmatch(expected):
            raise ValueError('invalid Lean reference fingerprint')
        file = project / name
        if file.is_symlink() or not file.resolve().is_relative_to(project) or not file.is_file() or digest(file) != expected:
            raise ValueError(f'stale Lean semantic declaration: {name}')
    paths = {}
    for key in ('spec', 'property', 'config', 'external'):
        item = target[key]
        if not isinstance(item, str) or Path(item).is_absolute():
            raise ValueError(f'target {key} must be a project-relative path')
        candidate = project / item
        if candidate.is_symlink() or not candidate.resolve().is_relative_to(project) or not candidate.exists():
            raise ValueError(f'missing target {key}: {item}')
        paths[key] = candidate
    if not isinstance(target['source_sha256'], dict) or not target['source_sha256']:
        raise ValueError('target source_sha256 is required')
    current = {str(Path(k).relative_to(project)): v for k, v in source_identity([paths['spec']]).items()}
    if current != target['source_sha256']:
        raise ValueError('specification source is stale')
    with paths['config'].open('rb') as file:
        catalog = tomllib.load(file)
    with paths['external'].open('rb') as file:
        external = tomllib.load(file)
    native = load_clause([paths['spec']], paths['property'], target['name'], project=project)
    compiled = compile_clause(native, select_external(catalog, external))
    aliases = target['type_aliases']
    if not isinstance(aliases, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in aliases.items()):
        raise ValueError('target type_aliases must map type keys to Lean types')
    def bind_aliases(value):
        if isinstance(value, dict):
            if 'key' in value and 'lean' in value and value['key'] in aliases:
                value['lean'] = aliases[value['key']]
            for child in value.values():
                bind_aliases(child)
        elif isinstance(value, list):
            for child in value:
                bind_aliases(child)
    bind_aliases(compiled)
    base = contract.rpartition('.')[0]
    reconstructed = render_contract(compiled, contract, base + '.Transport')
    if contract_path.read_text() != reconstructed:
        raise ValueError('typed property contract does not match original property')
    imports = _list(plan['imports'], 'imports')
    for module in imports:
        require_name(module)
        module_path = project.joinpath(*module.split('.')).with_suffix('.lean')
        if module_path.is_symlink() or not module_path.is_file():
            raise ValueError(f'missing Lean import: {module}')
        if str(module_path.relative_to(project)) not in target['lean_sha256']:
            raise ValueError(f'target must fingerprint Lean import: {module}')
    for reference in _records(plan['implementation_refs'], 'implementation_refs'):
        _source(project, reference)
    values = {}
    for item in _records(plan['values'], 'values'):
        if set(item) != {'id', 'type'}:
            raise ValueError('value needs id and type')
        name = _id(item['id'], 'value id')
        if name in values:
            raise ValueError(f'duplicate value {name}')
        values[name] = _term(item['type'], f'type of {name}')
    components = {}
    producer = {}
    for item in _records(plan['components'], 'components'):
        if set(item) != {'id', 'input', 'output', 'require', 'ensure', 'implementation'}:
            raise ValueError('component needs id, input, output, require, ensure, implementation')
        name = _id(item['id'], 'component id')
        if name in components:
            raise ValueError(f'duplicate component {name}')
        inputs = _list(item['input'], f'{name}.input')
        outputs = _list(item['output'], f'{name}.output')
        if set(inputs) & set(outputs):
            raise ValueError(f'{name} cannot consume and produce one value')
        for value in inputs + outputs:
            if value not in values:
                raise ValueError(f'{name} uses unknown value {value}')
        if not outputs:
            raise ValueError(f'{name} must produce a value')
        for value in outputs:
            if value in producer:
                raise ValueError(f'{value} is sampled or computed twice')
            producer[value] = name
        _term(item['require'], f'{name}.require')
        _term(item['ensure'], f'{name}.ensure')
        if item['implementation'] is not None:
            _source(project, item['implementation'])
        components[name] = item
    if set(producer) != set(values):
        raise ValueError(f'unproduced values: {sorted(set(values)-set(producer))}')
    links = {}
    edges = {name: set() for name in components}
    for item in _records(plan['connections'], 'connections'):
        if set(item) != {'target', 'sources', 'proof'}:
            raise ValueError('connection needs target, sources, proof')
        target = _id(item['target'], 'connection target')
        if target not in components or target in links:
            raise ValueError(f'unknown or duplicate connection target {target}')
        sources = _list(item['sources'], f'{target}.sources')
        for source in sources:
            if source not in components or source == target:
                raise ValueError(f'invalid source {source} for {target}')
            edges[source].add(target)
        _term(item['proof'], f'{target}.proof')
        links[target] = item
    if set(links) != set(components):
        raise ValueError(f'missing requirement discharge for {sorted(set(components)-set(links))}')
    for name, item in components.items():
        for value in item['input']:
            edges[producer[value]].add(name)
    pending = {k: set(v) for k, v in edges.items()}
    ready = sorted(k for k in pending if not any(k in deps for deps in pending.values()))
    order = []
    while ready:
        node = ready.pop(0)
        order.append(node)
        for target in sorted(pending.pop(node)):
            if not any(target in deps for deps in pending.values()) and target not in ready:
                ready.append(target)
        ready.sort()
    if pending:
        raise ValueError(f'ungrounded component cycle: {sorted(pending)}')
    final = plan['final']
    if not isinstance(final, dict) or set(final) != {'output', 'proof'} or final['output'] not in values:
        raise ValueError('final needs a known output and proof')
    _term(final['proof'], 'final.proof')
    if values[final['output']] != contract + '.Input':
        raise ValueError('final output must have the exact Contract.Input type')
    return contract, imports, values, components, links, order


def _forall(values, body):
    binders = ' '.join(f'(v_{name} : {ty})' for name, ty in values.items())
    return f'∀ {binders}, {body}'


def _and(parts):
    return ' ∧ '.join(f'({part})' for part in parts) if parts else 'True'


def render(plan, validated, module):
    contract, imports, values, components, links, order = validated
    lines = ['import Spec4Pbt.GoalTools', f'import {contract}', *(f'import {x}' for x in imports),
             'set_option autoImplicit false', f'namespace {module}', '']
    for name in order:
        item = components[name]
        ins = ' '.join(f'(v_{v} : {values[v]})' for v in item['input'])
        allvars = ' '.join(f'(v_{v} : {values[v]})' for v in item['input'] + item['output'])
        lines += [f'def require_{name} {ins} : Prop := {item["require"]}',
                  f'def ensure_{name} {allvars} : Prop := {item["ensure"]}', '']
    def call(prefix, name):
        item = components[name]
        args = item['input'] if prefix == 'require' else item['input'] + item['output']
        return f'({prefix}_{name} ' + ' '.join(f'v_{v}' for v in args) + ')'
    expected = {}
    for name in order:
        item = links[name]
        typ = _forall(values, f'{_and([call("ensure", s) for s in item["sources"]])} → {call("require", name)}')
        lines += [f'theorem discharge_{name} : {typ} := {item["proof"]}', '']
        expected[f'discharge_{name}'] = typ
    goal = f'{contract}.Premise v_{plan["final"]["output"]}'
    typ = _forall(values, f'{_and([call("ensure", name) for name in order])} → {goal}')
    lines += [f'theorem premise : {typ} := {plan["final"]["proof"]}', '', f'end {module}', '']
    expected['premise'] = typ
    return '\n'.join(lines), expected


def check(path, *, project=PROJECT, timeout_seconds=120):
    project = Path(project).resolve()
    path = Path(path).resolve()
    if not path.is_file() or not path.is_relative_to(project):
        raise ValueError('plan must be a project file')
    plan = strict_json(path.read_text())
    validated = _validate(plan, project)
    timeout = require_timeout(timeout_seconds)
    fingerprint = hashlib.sha256(path.read_bytes()).hexdigest()[:16]
    module = f'build.scratch.plan_{fingerprint}.PlanContract'
    destination = project / SCRATCH_DIRECTORY / f'plan_{fingerprint}'
    destination.mkdir(parents=True, exist_ok=True)
    source, expected = render(plan, validated, module)
    (destination / 'PlanContract.lean').write_text(source)
    contract, imports, _, _, _, order = validated
    rebuild_modules(project, [contract, *imports, module], timeout)
    audit = [f'import {module}', f'open {module}']
    for name, typ in expected.items():
        audit.append(f'#spec4pbt_verify {module}.{name} in_module {module} : {typ}')
    elaborate(project, '\n'.join(audit) + '\n', timeout)
    return {'status': 'checked', 'plan': str(path), 'components': order,
            'remaining_require': [], 'premise': f'{contract}.Premise',
            'scope': 'conditional contracts; generator implementations not certified'}
