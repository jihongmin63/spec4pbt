"""Typed one-step composition checks for a finite recursive plan template."""
from __future__ import annotations

import re

from scripts.property.execution_graph import _source


IDENT = re.compile(r'[A-Za-z][A-Za-z0-9_]*\Z')


def _name(value, label):
    if not isinstance(value, str) or not IDENT.fullmatch(value):
        raise ValueError(f'invalid {label}: {value!r}')
    return value


def _term(value, label):
    if not isinstance(value, str) or not value.strip() or '\n' in value or '\r' in value:
        raise ValueError(f'{label} must be a single-line Lean term')
    return value


def _and(parts):
    return ' ∧ '.join(f'({x})' for x in parts) if parts else 'True'


def validate(templates, project, main_components, execution):
    if not isinstance(templates, list) or not templates:
        raise ValueError('schema 2 needs nonempty recursive templates')
    seen = set()
    reports = []
    for template in templates:
        if not isinstance(template, dict) or set(template) != {'id', 'parameters', 'values', 'components', 'connections', 'recursive', 'base', 'summary', 'applies_to', 'loop'}:
            raise ValueError('recursive template has invalid fields')
        if any(not isinstance(template[key], list) for key in ('parameters', 'values', 'components', 'connections')):
            raise ValueError('recursive template parameters, values, components, connections must be lists')
        ident = _name(template['id'], 'template id')
        if ident in seen:
            raise ValueError(f'duplicate recursive template {ident}')
        seen.add(ident)
        values = {}
        for kind in ('parameters', 'values'):
            for item in template[kind]:
                if not isinstance(item, dict) or set(item) != {'id', 'type'}:
                    raise ValueError(f'{ident}.{kind} needs id and type')
                name = _name(item['id'], f'{ident} value')
                if name in values:
                    raise ValueError(f'{ident} duplicate value {name}')
                values[name] = _term(item['type'], f'{ident}.{name} type')
        params = {x['id'] for x in template['parameters']}
        components = {}
        producers = {}
        for item in template['components']:
            if not isinstance(item, dict) or set(item) != {'id', 'input', 'output', 'require', 'ensure', 'source'}:
                raise ValueError(f'{ident} component has invalid fields')
            name = _name(item['id'], f'{ident} component')
            if name in components:
                raise ValueError(f'{ident} duplicate component {name}')
            for key in ('input', 'output'):
                if not isinstance(item[key], list) or len(item[key]) != len(set(item[key])) or any(v not in values for v in item[key]):
                    raise ValueError(f'{ident}.{name} has invalid {key}')
            if not item['output'] or set(item['output']) & set(item['input']):
                raise ValueError(f'{ident}.{name} has invalid output')
            for value in item['output']:
                if value in params or value in producers:
                    raise ValueError(f'{ident}.{value} is produced twice')
                producers[value] = name
            _term(item['require'], f'{ident}.{name}.require')
            _term(item['ensure'], f'{ident}.{name}.ensure')
            _source(project, item['source'])
            components[name] = item
        if set(producers) != set(values) - params:
            raise ValueError(f'{ident} has unproduced values')
        if template['recursive'] not in components:
            raise ValueError(f'{ident} recursive call component is missing')
        if template['applies_to'] not in main_components:
            raise ValueError(f'{ident} has an unknown enclosing component')
        matching = [loop for loop in execution['loops'] if loop['id'] == template['loop']]
        if len(matching) != 1 or matching[0]['component'] != template['applies_to']:
            raise ValueError(f'{ident} is not attached to its recursive source loop')
        source = components[template['recursive']]['source']
        if (source['path'], source['owner'], source['fragment']) != (
                matching[0]['source_path'], matching[0]['source_owner'], matching[0]['smaller']):
            raise ValueError(f'{ident} recursive source does not match the attached loop')
        links = {}
        edges = {name: set() for name in components}
        for item in template['connections']:
            if not isinstance(item, dict) or set(item) != {'target', 'sources', 'proof'}:
                raise ValueError(f'{ident} connection has invalid fields')
            target = item['target']
            if target not in components or target in links:
                raise ValueError(f'{ident} has duplicate or unknown connection target {target}')
            sources = item['sources']
            if not isinstance(sources, list) or len(sources) != len(set(sources)) or any(s not in components or s == target for s in sources):
                raise ValueError(f'{ident}.{target} has invalid sources')
            required = {producers[v] for v in components[target]['input'] if v not in params}
            if not required <= set(sources):
                raise ValueError(f'{ident}.{target} is missing producer edges: {sorted(required-set(sources))}')
            _term(item['proof'], f'{ident}.{target} proof')
            for source in sources:
                edges[source].add(target)
            links[target] = item
        if set(links) != set(components):
            raise ValueError(f'{ident} is missing requirement discharge')
        pending = {k: set(v) for k, v in edges.items()}
        order = []
        while pending:
            ready = sorted(k for k in pending if not any(k in v for v in pending.values()))
            if not ready:
                raise ValueError(f'{ident} has an ungrounded cycle')
            name = ready[0]
            order.append(name)
            pending.pop(name)
        for key in ('base', 'summary'):
            item = template[key]
            if not isinstance(item, dict) or set(item) != {'claim', 'proof'}:
                raise ValueError(f'{ident}.{key} needs claim and proof')
            _term(item['claim'], f'{ident}.{key} claim')
            _term(item['proof'], f'{ident}.{key} proof')
        reports.append({'id': ident, 'applies_to': template['applies_to'], 'loop': template['loop'],
                        'components': order, 'parameters': sorted(params),
                        'recursive': template['recursive'], 'remaining_require': [],
                        'edges': [{'source': s, 'target': c['target']} for c in template['connections'] for s in c['sources']]})
    return reports


def render(templates):
    lines, expected = [], {}
    for template in templates:
        ident = template['id']
        values = {v['id']: v['type'] for v in template['parameters'] + template['values']}
        binders = ' '.join(f'(v_{v} : {t})' for v, t in values.items())
        components = {c['id']: c for c in template['components']}
        def call(kind, name):
            c = components[name]
            args = c['input'] if kind == 'require' else c['input'] + c['output']
            return f'({kind}_{ident}_{name} ' + ' '.join('v_' + x for x in args) + ')'
        for c in template['components']:
            name = c['id']
            ins = ' '.join(f'(v_{v} : {values[v]})' for v in c['input'])
            allvars = ' '.join(f'(v_{v} : {values[v]})' for v in c['input'] + c['output'])
            lines += [f'-- template {ident} component {name}', f'def require_{ident}_{name} {ins} : Prop := {c["require"]}',
                      f'def ensure_{ident}_{name} {allvars} : Prop := {c["ensure"]}', '']
        for link in template['connections']:
            name = link['target']
            typ = f'∀ {binders}, {_and([call("ensure", s) for s in link["sources"]])} → {call("require", name)}'
            theorem = f'template_{ident}_discharge_{name}'
            lines += [f'-- template {ident} connection {name}', f'theorem {theorem} : {typ} := {link["proof"]}', '']
            expected[theorem] = typ
        base = template['base']
        theorem = f'template_{ident}_base'
        lines += [f'-- template {ident} base', f'theorem {theorem} : {base["claim"]} := {base["proof"]}', '']
        expected[theorem] = base['claim']
        summary = template['summary']
        typ = f'∀ {binders}, {_and([call("ensure", c["id"]) for c in template["components"]])} → {summary["claim"]}'
        theorem = f'template_{ident}_step'
        lines += [f'-- template {ident} step', f'theorem {theorem} : {typ} := {summary["proof"]}', '']
        expected[theorem] = typ
    return lines, expected
