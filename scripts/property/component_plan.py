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
from scripts.property.source_graph import check_site
from scripts.property.execution_graph import validate as validate_execution
from scripts.property.recursive_template import validate as validate_templates, render as render_templates


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


def _source(project, item, inputs=None, outputs=None):
    if not isinstance(item, dict) or set(item) not in ({'path', 'sha256', 'symbol'}, {'path', 'sha256', 'symbol', 'site'}):
        raise ValueError('implementation reference needs path, sha256, symbol, optionally site')
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
    if 'site' in item:
        if inputs is None or outputs is None or not isinstance(item['site'], dict) or item['site'].get('owner') != symbol:
            raise ValueError(f'{path.name}:{symbol} has an unbound source site')
        return check_site(path, item['site'], inputs, outputs, project)


def _validate(plan, project):
    old_keys = {'schema_version', 'target', 'contract_module', 'imports', 'implementation_refs', 'values', 'components', 'connections', 'final'}
    if not isinstance(plan, dict) or plan.get('schema_version') not in (1, 2) or set(plan) != (old_keys if plan['schema_version'] == 1 else old_keys | {'execution', 'templates'}):
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
    source_sites = set()
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
            if plan['schema_version'] == 1:
                raise ValueError(f'{name}: schema 1 cannot claim implementation correspondence; use source-site schema 2')
            site = _source(project, item['implementation'], inputs, outputs)
            if plan['schema_version'] == 2:
                if site is None:
                    raise ValueError(f'{name} is missing a source call/definition mapping')
                key = (item['implementation']['path'], site['owner'], site['fragment'])
                if key in source_sites:
                    raise ValueError(f'{name} duplicates a source sampler or computation: {key}')
                source_sites.add(key)
        elif plan['schema_version'] == 2:
            raise ValueError(f'{name} is missing a source mapping')
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
        if plan['schema_version'] == 2:
            missing = {producer[value] for value in components[target]['input']} - set(sources)
            if missing:
                raise ValueError(f'{target} missing value-dependency edges from {sorted(missing)}')
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
    execution = validate_execution(plan['execution'], components, project) if plan['schema_version'] == 2 else None
    templates = validate_templates(plan['templates'], project, components, execution) if plan['schema_version'] == 2 else None
    if plan['schema_version'] == 2:
        for loop in plan['execution']['loops']:
            callee = Path(loop['entry']['path']).stem + '.' + loop['entry']['owner']
            call_fragments = [components[loop['component']]['implementation']['site']['fragment']]
            call_fragments.extend(c['source']['fragment'] for template in plan['templates']
                                  if template['applies_to'] == loop['component'] for c in template['components'])
            if loop['via'] is not None:
                via = loop['via']
                if callee not in via['fragment'] or not any(re.search(r'\b' + re.escape(via['owner']) + r'\b', fragment) for fragment in call_fragments):
                    raise ValueError(f'{loop["id"]} recursive entry is not called through its source wrapper')
            elif not any(callee in fragment for fragment in call_fragments):
                raise ValueError(f'{loop["id"]} recursive entry is not called by its component/template')
    return contract, imports, values, components, links, order, execution, templates


def _forall(values, body):
    binders = ' '.join(f'(v_{name} : {ty})' for name, ty in values.items())
    return f'∀ {binders}, {body}'


def _and(parts):
    return ' ∧ '.join(f'({part})' for part in parts) if parts else 'True'


def render(plan, validated, module):
    contract, imports, values, components, links, order, _, _ = validated
    lines = ['import Spec4Pbt.GoalTools', f'import {contract}', *(f'import {x}' for x in imports),
             'set_option autoImplicit false', f'namespace {module}', '']
    template_expected = {}
    if plan['schema_version'] == 2:
        template_lines, template_expected = render_templates(plan['templates'])
        lines.extend(template_lines)
    for name in order:
        item = components[name]
        ins = ' '.join(f'(v_{v} : {values[v]})' for v in item['input'])
        allvars = ' '.join(f'(v_{v} : {values[v]})' for v in item['input'] + item['output'])
        lines += [f'-- component {name}', f'def require_{name} {ins} : Prop := {item["require"]}',
                  f'def ensure_{name} {allvars} : Prop := {item["ensure"]}', '']
    def call(prefix, name):
        item = components[name]
        args = item['input'] if prefix == 'require' else item['input'] + item['output']
        return f'({prefix}_{name} ' + ' '.join(f'v_{v}' for v in args) + ')'
    expected = dict(template_expected)
    for name in order:
        item = links[name]
        typ = _forall(values, f'{_and([call("ensure", s) for s in item["sources"]])} → {call("require", name)}')
        lines += [f'-- connection {name}', f'theorem discharge_{name} : {typ} := {item["proof"]}', '']
        expected[f'discharge_{name}'] = typ
    goal = f'{contract}.Premise v_{plan["final"]["output"]}'
    typ = _forall(values, f'{_and([call("ensure", name) for name in order])} → {goal}')
    lines += ['-- final premise', f'theorem premise : {typ} := {plan["final"]["proof"]}', '', f'end {module}', '']
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
    contract, imports, _, components, _, order, execution, templates = validated
    try:
        rebuild_modules(project, [contract, *imports, module], timeout)
    except ChildProcessError as exc:
        if plan['schema_version'] != 2:
            raise
        match = re.search(r'(?m)^error: .*PlanContract\.lean:(\d+):\d+', str(exc))
        location = 'generated plan module'
        if match:
            lineno = int(match.group(1))
            for line in reversed(source.splitlines()[:lineno]):
                if line.startswith('-- component ') or line.startswith('-- connection ') or line.startswith('-- template ') or line == '-- final premise':
                    location = line.removeprefix('-- ')
                    break
        errors = re.findall(r'(?m)^error:.*$', str(exc))
        raise ValueError(f'plan semantic failure at {location}: ' + '\n'.join(errors[:3])) from exc
    audit = [f'import {module}', f'open {module}']
    for name, typ in expected.items():
        audit.append(f'#spec4pbt_verify {module}.{name} in_module {module} : {typ}')
    elaborate(project, '\n'.join(audit) + '\n', timeout)
    edges = [{'source': source, 'target': item['target']} for item in plan['connections'] for source in item['sources']]
    nodes = [{'id': name, 'input': components[name]['input'], 'output': components[name]['output'],
              'require': components[name]['require'], 'ensure': components[name]['ensure'],
              'source': {'path': components[name]['implementation']['path'],
                         'owner': components[name]['implementation']['site']['owner'],
                         'fragment': components[name]['implementation']['site']['fragment'],
                         'uses': components[name]['implementation']['site']['uses'],
                         'conditions': components[name]['implementation']['site']['conditions'],
                         'projections': components[name]['implementation']['site']['projections']}
              if plan['schema_version'] == 2 else None}
             for name in order]
    return {'status': 'checked', 'plan': str(path), 'components': order,
            'nodes': nodes, 'edges': edges,
            'execution': execution,
            'templates': templates,
            'remaining_require': [], 'premise': f'{contract}.Premise',
            'scope': 'conditional contracts; generator implementations not certified'}


def format_text(result):
    lines = [f"{result['status']}: {len(result['nodes'])} nodes, {len(result['edges'])} edges; "
             f"premise {result['premise']}; remaining require {len(result['remaining_require'])}"]
    if result['execution']:
        lines.append('execution frames:')
        for frame in result['execution']['frames']:
            lines.append(f"  {frame['id']}: {', '.join(frame['members'])}")
    lines.append('nodes:')
    for node in result['nodes']:
        source = node['source'] or {}
        lines.append(f"  {node['id']}: ({', '.join(node['input'])}) -> ({', '.join(node['output'])}) "
                     f"at {source.get('path', '?')}:{source.get('owner', '?')}")
        if source.get('conditions'):
            lines.append(f"    semantic conditions: {', '.join(source['conditions'])}")
        lines.append(f"    require: {node['require']}")
        lines.append(f"    ensure: {node['ensure']}")
    lines.append('edges:')
    for edge in result['edges']:
        lines.append(f"  {edge['source']} -> {edge['target']}")
    if result['execution']:
        lines.append('recursive source shapes:')
        for loop in result['execution']['loops']:
            lines.append(f"  {loop['id']} ({loop['measure']}): {loop['component']} / {loop['smaller']}")
        lines.append('source result bindings:')
        for binding in result['execution']['bindings']:
            lines.append(f"  {binding['path']}:{binding['owner']} / {binding['fragment']}")
    if result['templates']:
        lines.append('typed recursive templates:')
        for template in result['templates']:
            lines.append(f"  {template['id']} -> {template['applies_to']}: "
                         f"{', '.join(template['components'])}; base and step checked")
    lines.append(result['scope'])
    return '\n'.join(lines)
