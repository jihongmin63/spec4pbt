"""Classify normalized SpecTec AL without interpreting source expressions.

The native frontend supplies typed nodes, bindings, origin, and order. This
module only follows data provenance and plans external observations.
"""
import copy
import hashlib
import json
from dataclasses import dataclass

from pbt.observations import SELECTOR


def identity(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
                                    separators=(',', ':'), allow_nan=False).encode()).hexdigest()


def variables(expression):
    if expression['kind'] == 'variable':
        return {expression['name']}
    found = set()
    for key, value in expression.items():
        if key in ('type', 'location'):
            continue
        if isinstance(value, dict):
            if 'kind' in value:
                found |= variables(value)
            else:
                for field in value.values():
                    if isinstance(field, dict) and 'kind' in field:
                        found |= variables(field)
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, dict) and 'kind' in item:
                    found |= variables(item)
    return found


def pattern_leaves(expression, selector):
    if expression['kind'] == 'record':
        for field, value in expression['fields'].items():
            yield from pattern_leaves(value, selector + '.' + field)
    else:
        yield selector, expression


def selected_expression(pattern, selector):
    fields = selector.split('.')[1:]
    for field in fields:
        if pattern['kind'] != 'record' or field not in pattern['fields']:
            return None
        pattern = pattern['fields'][field]
    return pattern


@dataclass(frozen=True)
class Flow:
    sources: frozenset = frozenset()
    producers: frozenset = frozenset()
    observed: frozenset = frozenset()
    fields: dict | None = None


def join(*flows):
    if len(flows) == 1:
        return flows[0]
    return Flow(frozenset().union(*(f.sources for f in flows)),
                frozenset().union(*(f.producers for f in flows)),
                frozenset().union(*(f.observed for f in flows)))


def _profiles(config):
    if set(config) - {'schema_version', 'observations'}:
        if 'executions' in config:
            raise ValueError('move executions into a separate implementation manifest and rebuild the bundle')
        raise ValueError('invalid observation metadata fields')
    if type(config.get('schema_version')) is not int or config['schema_version'] != 1:
        raise ValueError('expected observation schema_version 1')
    if not isinstance(config.get('observations', []), list):
        raise ValueError('observations must be an array')
    profiles, ids = {}, set()
    for profile in config.get('observations', []):
        if set(profile) != {'id', 'relation', 'observe'}:
            raise ValueError('invalid observation profile fields')
        rid, oid, selectors = profile['relation'], profile['id'], profile['observe']
        if not isinstance(rid, str) or not isinstance(oid, str) or not oid:
            raise ValueError('profile needs relation and nonempty id')
        if rid in profiles or oid in ids:
            raise ValueError('duplicate relation observation profile or id')
        if not isinstance(selectors, list) or any(not isinstance(x, str) or SELECTOR.fullmatch(x) is None for x in selectors):
            raise ValueError('invalid observation selector')
        for i, a in enumerate(selectors):
            if any(a == b or a.startswith(b+'.') or b.startswith(a+'.') for b in selectors[:i]):
                raise ValueError('duplicate or overlapping observation selectors')
        profiles[rid] = profile
        ids.add(oid)
    return profiles


def compile_clause(clause, config):
    """Compile the native AL IR into a proof and runtime collection plan."""
    clause = copy.deepcopy(clause)
    if 'condition_blocks' not in clause or 'goal_block' not in clause:
        raise ValueError('property AL schema 2 required; rebuild the native toolchain')
    if len(clause['condition_blocks']) != len(clause['conditions']):
        raise ValueError('AL condition blocks do not cover every source condition')
    for index, block in enumerate(clause['condition_blocks']):
        origin = f'condition.{index}'
        if block['origin'] != origin or not block['nodes'] or any(
                node['origin'] != origin or node['scope'] != block['scope']
                for node in block['nodes']):
            raise ValueError(f'AL condition block {origin} has invalid origin, scope, or nodes')
    if clause['goal_block']['origin'] != 'goal' or not clause['goal_block']['nodes'] or any(
            node['origin'] != 'goal' or node['scope'] != clause['goal_block']['scope']
            for node in clause['goal_block']['nodes']):
        raise ValueError('AL goal block has invalid origin, scope, or nodes')
    profiles = _profiles(config)
    known = {x['name']: {**x, 'producer': None, 'selector': None,
                         'projection': [], 'sources': ['input'], 'dependencies': []}
             for x in clause['inputs']}
    flows = {name: Flow(frozenset({'I'})) for name in known}
    input_names = set(known)
    calls, checks, proof, origins = [], [], [], {}

    def diagnostic(node, message):
        loc = node.get('location', {})
        where = f"{loc.get('file', '<property>')}:{loc.get('line', 0)}:{loc.get('column', 0)}"
        return ValueError(f"{where} [{node.get('id', node.get('origin', 'property'))}] {message}")

    def details_from_names(names):
        order = sorted(names, key=lambda n: (0 if 'L' in flows.get(n, Flow()).sources else 1, n))
        return ', '.join(f"{name}({','.join(sorted(flows[name].sources))}@{known[name]['producer']})"
                         for name in order if name in known)

    def children(expr):
        for key, value in expr.items():
            if key in ('id', 'kind', 'type', 'location'):
                continue
            if isinstance(value, dict):
                if 'kind' in value:
                    yield value
                else:
                    for item in value.values():
                        if isinstance(item, dict) and 'kind' in item:
                            yield item
            elif isinstance(value, list):
                for item in value:
                    if isinstance(item, dict) and 'kind' in item:
                        yield item

    def expression_flow(expr, node):
        kind = expr['kind']
        if kind == 'variable':
            name = expr['name']
            if name not in flows:
                raise diagnostic(node, f'{name} has no AL producer')
            return flows[name]
        if kind == 'record':
            fields = {name: expression_flow(value, node) for name, value in expr['fields'].items()}
            merged = join(*fields.values())
            return Flow(merged.sources, merged.producers, merged.observed, fields)
        if kind == 'field':
            base = expression_flow(expr['base'], node)
            return base.fields.get(expr['field'], base) if base.fields else base
        return join(*(expression_flow(x, node) for x in children(expr)))

    def classify(value_flow, node, expr):
        names = details_from_names(variables(expr))
        if 'H' in value_flow.sources:
            raise diagnostic(node, f'{names}: hidden output is not observable in a runtime expression')
        if 'E' in value_flow.sources and 'L' in value_flow.sources:
            raise diagnostic(node, f'mixed private and observable values: {names}')
        if 'L' in value_flow.sources and value_flow.observed:
            raise diagnostic(node, f'observation-dependent private value: {names}; external sources {sorted(value_flow.observed)}')
        return 'check' if 'E' in value_flow.sources else 'proof'

    def add_binding(name, definition, origin, selector, projection, value_flow):
        if name in known:
            raise ValueError(f'{origin}: AL binding {name} is repeated')
        info = {**definition, 'producer': origin, 'selector': selector,
                'projection': projection, 'sources': sorted(value_flow.sources),
                'dependencies': sorted(value_flow.producers),
                'observed_dependencies': sorted(value_flow.observed)}
        known[name] = info
        flows[name] = value_flow

    def bind_pattern(target, value_flow, block_bindings, origin):
        if target['kind'] == 'variable':
            name = target['name']
            if name in block_bindings:
                add_binding(name, block_bindings[name], origin, None, [], value_flow)
        elif target['kind'] == 'record':
            for field, child in target['fields'].items():
                flow = value_flow.fields.get(field, value_flow) if value_flow.fields else value_flow
                bind_pattern(child, flow, block_bindings, origin)
        else:
            for child in children(target):
                bind_pattern(child, value_flow, block_bindings, origin)

    def process_relation(node, origin, block_bindings):
        rid = node['relation']
        external = rid in profiles
        args, in_slots = node['arguments'], node['inputs']
        if any(i >= len(args) for i in in_slots):
            raise diagnostic(node, 'relation input slot out of range')
        input_flow = join(*(expression_flow(args[i], node) for i in in_slots))
        needed = set().union(*(variables(args[i]) for i in in_slots)) if in_slots else set()
        if 'H' in input_flow.sources or 'L' in input_flow.sources:
            if external:
                raise diagnostic(node, f'external request input requires observable values: {details_from_names(needed)}')
            if 'E' in input_flow.sources or input_flow.observed:
                raise diagnostic(node, f'internal request combines private and observable values: {details_from_names(needed)}')
        if external:
            selectors = profiles[rid]['observe']
            observations = []
            for selector in selectors:
                slot = int(selector.split('.')[0][1:])
                if slot in in_slots or slot >= len(args):
                    raise diagnostic(node, f'{rid}: invalid output selector {selector}')
                selected = selected_expression(args[slot], selector)
                if selected is not None:
                    observations.append({'selector': selector, 'type': selected['type']})
        else:
            selectors, observations = [], []
        matches, bindings = [], []
        for slot, arg in enumerate(args):
            if slot in in_slots:
                continue
            for path, leaf in pattern_leaves(arg, f'%{slot}'):
                covering = next((s for s in selectors if path == s or path.startswith(s+'.')), None)
                projection = path[len(covering)+1:].split('.') if covering and path != covering else []
                if leaf['kind'] == 'variable' and leaf['name'] in block_bindings:
                    name = leaf['name']
                    source = 'E' if covering else 'H' if external else 'L'
                    observed = input_flow.observed | (frozenset({origin}) if external else frozenset())
                    value_flow = Flow(frozenset({source}), frozenset({origin}), observed)
                    add_binding(name, block_bindings[name], origin, covering, projection, value_flow)
                    bindings.append(known[name])
                else:
                    if external and covering is None:
                        raise diagnostic(node, f'output constraint {path} must be observed')
                    used = variables(leaf)
                    for name in used:
                        if name not in known or 'H' in flows[name].sources:
                            raise diagnostic(node, f'output match reads hidden or unavailable {name}')
                    if external:
                        matches.append({'selector': covering, 'projection': projection, 'expression': leaf})
        if external:
            occurrence = origin if not node['auxiliary'] else node['id']
            call = {**node, 'node_id': node['id'], 'id': occurrence,
                    'dependencies': sorted(input_flow.producers & frozenset(c['id'] for c in calls)),
                    'profile_selectors': list(selectors),
                    'observations': observations, 'bindings': bindings,
                    'matches': matches, 'input_only': needed <= input_names}
            calls.append(call)
            return 'call'
        return 'check' if 'E' in input_flow.sources else 'proof'

    def process_block(block, is_goal=False):
        origin = block['origin']
        block_bindings = {b['name']: b for b in block['bindings']}
        runtime = []
        for node in block['nodes']:
            origins[node['id']] = {'origin': origin, 'scope': node['scope'],
                                   'location': node['location'], 'auxiliary': node['auxiliary']}
            kind = node['kind']
            if kind == 'relation':
                category = process_relation(node, origin, block_bindings)
            elif kind == 'let':
                value_flow = expression_flow(node['value'], node)
                category = classify(value_flow, node, node['value']) if not is_goal else 'goal'
                bind_pattern(node['target'], value_flow, block_bindings, origin)
            elif kind == 'guard':
                value_flow = expression_flow(node['expression'], node)
                if is_goal:
                    if 'H' in value_flow.sources:
                        raise diagnostic(node, f'{details_from_names(variables(node["expression"]))}: hidden goal value is not observable')
                    category = 'goal'
                else:
                    category = classify(value_flow, node, node['expression'])
            else:
                raise diagnostic(node, f'unsupported AL premise kind {kind}')
            if not is_goal:
                if category == 'proof':
                    proof.append(node)
                elif category == 'check':
                    runtime.append(node)
        if runtime:
            checks.append({**block, 'nodes': runtime})

    for block in clause['condition_blocks']:
        process_block(block)
    source_goal = clause['goal']
    goal_names = (variables(source_goal['expression']) if source_goal['kind'] == 'guard'
                  else set().union(*(variables(arg) for arg in source_goal['arguments'])))
    for name in sorted(goal_names):
        if name in known and ('L' in flows[name].sources or 'H' in flows[name].sources):
            raise diagnostic({**source_goal, 'id': 'goal'},
                             f'goal reads {name} private/internal value; only input or observable values are allowed')
    process_block(clause['goal_block'], True)

    all_conditions = []
    for index, source in enumerate(clause['conditions']):
        item = {**source, 'id': f'condition.{index}', 'origin': f'condition.{index}'}
        if item['kind'] == 'guard':
            item['input_only'] = variables(item['expression']) <= input_names
        else:
            item['input_only'] = set().union(*(variables(item['arguments'][i]) for i in item['inputs'])) <= input_names
        all_conditions.append(item)
    result = {'schema_version': 2, 'engine': 'spectec-al', 'relation_semantics': 'ordered',
              'name': clause['name'], 'inputs': clause['inputs'],
              'all_conditions': all_conditions, 'proof_conditions': proof,
              'conditions': all_conditions, 'checks': checks, 'goal_block': clause['goal_block'],
              'goal': clause['goal'], 'condition_blocks': clause['condition_blocks'],
              'calls': calls, 'variables': known,
              'bindings': [known[n] for n in known if n not in input_names],
              'origins': origins}
    result['plan_id'] = identity(result)
    return result
