"""Classify normalized SpecTec AL without interpreting source expressions.

The native frontend supplies typed nodes, bindings, origin, and order. This
module only follows data provenance and plans external observations.
"""
import copy
import hashlib
import json
from dataclasses import dataclass

from pbt.observations import SELECTOR


def classify_relations(helpers, primitive_external, *, observations=None):
    """Compute the greatest external helper set from relation dependencies.

    Output selectors deliberately play no part in this calculation. Cycles
    remain in the set only when every dependency leaving the cycle does.
    """
    del observations
    primitive_external = set(primitive_external)
    dependencies = {}
    for helper in helpers:
        name = helper['name']
        if name in dependencies or name in primitive_external:
            raise ValueError(f'duplicate or primitive helper relation {name}')
        dependencies[name] = set().union(
            *(set(rule['dependencies']) for rule in helper['rules']))
    possible = set(dependencies)
    while True:
        remaining = {name for name in possible
                     if dependencies[name] <= (possible | primitive_external)}
        if remaining == possible:
            break
        possible = remaining
    return {
        'external': sorted(possible | primitive_external),
        'reasons': {name: sorted(dependencies[name]) for name in sorted(possible)},
        'internal': {name: sorted(dependencies[name] - (possible | primitive_external))
                     for name in sorted(set(dependencies) - possible)},
    }


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


def select_external(catalog, selection):
    """Restrict a specification's external catalog for one property."""
    if not isinstance(catalog, dict) or set(catalog) != {'schema_version', 'observations'}:
        raise ValueError('catalog requires schema_version and observations only')
    if not isinstance(catalog['observations'], list) or any(
            not isinstance(entry, dict) for entry in catalog['observations']):
        raise ValueError('catalog observations must be an array of tables')
    _profiles(catalog)
    by_id = {entry['id']: entry for entry in catalog['observations']}
    if not isinstance(selection, dict) or set(selection) != {'schema_version', 'external'}:
        raise ValueError('selection requires schema_version and external only')
    if type(selection['schema_version']) is not int or selection['schema_version'] != 1:
        raise ValueError('expected external selection schema_version 1')
    if not isinstance(selection['external'], list):
        raise ValueError('external selection must be an array')
    seen = set()
    selected = []
    for index, entry in enumerate(selection['external']):
        where = f'external[{index}]'
        if not isinstance(entry, dict) or set(entry) != {'id', 'observe'}:
            raise ValueError(f'{where}: expected id and observe only')
        oid, selectors = entry['id'], entry['observe']
        if not isinstance(oid, str) or not oid:
            raise ValueError(f'{where}: id must be a nonempty string')
        if oid in seen:
            raise ValueError(f'{where}: duplicate external id {oid}')
        seen.add(oid)
        if oid not in by_id:
            raise ValueError(f'{where}: unknown catalog id {oid}')
        if not isinstance(selectors, list):
            raise ValueError(f'{where}: observe must be an array')
        allowed = by_id[oid]['observe']
        for i, selector in enumerate(selectors):
            if not isinstance(selector, str) or SELECTOR.fullmatch(selector) is None:
                raise ValueError(f'{where}: invalid observation selector {selector!r}')
            if any(selector == previous or selector.startswith(previous + '.') or
                   previous.startswith(selector + '.') for previous in selectors[:i]):
                raise ValueError(f'{where}: overlapping observation selectors')
            if not any(selector == grant or selector.startswith(grant + '.') for grant in allowed):
                raise ValueError(f'{where}: observation selector {selector} is outside catalog grant')
        selected.append({'id': oid, 'relation': by_id[oid]['relation'],
                         'observe': list(selectors)})
    return {'schema_version': 1, 'observations': selected}


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
    helper_names = {helper['name'] for helper in clause.get('helpers', [])}
    helpers = {helper['name']: helper for helper in clause.get('helpers', [])}
    overlap = helper_names & set(profiles)
    if overlap:
        raise ValueError('helper external classification is automatic; remove observation profiles for '
                         + ', '.join(sorted(overlap)))
    roles = classify_relations(clause.get('helpers', []), profiles)
    external_relations = set(roles['external'])

    def delegate_primitive(name):
        seen = set()
        inverted = False
        while name in helpers and name not in seen:
            seen.add(name)
            inverted ^= helpers[name].get('negative', False)
            name = helpers[name].get('delegate')
            if name is None:
                return None
        if name in seen:
            return None
        profile = profiles.get(name)
        return (name, inverted) if profile is not None and not profile['observe'] else None
    known = {x['name']: {**x, 'producer': None, 'selector': None,
                         'projection': [], 'sources': ['input'], 'dependencies': []}
             for x in clause['inputs']}
    flows = {name: Flow(frozenset({'I'})) for name in known}
    input_names = set(known)
    calls, checks, proof, origins, unsupported = [], [], [], {}, []

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
        negative = node['kind'] == 'not_relation'
        external = rid in external_relations
        primitive = rid in profiles
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
            selectors = profiles[rid]['observe'] if primitive else []
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
        if external and not primitive:
            delegated = delegate_primitive(rid)
            if delegated is not None:
                target, inverted = delegated
                occurrence = origin if not node['auxiliary'] else node['id']
                calls.append({**node, 'node_id': node['id'], 'id': occurrence,
                              'relation': target, 'source_relation': rid, 'invert': inverted ^ negative,
                              'dependencies': sorted(input_flow.producers & frozenset(c['id'] for c in calls)),
                              'profile_selectors': [], 'observations': [],
                              'bindings': [], 'matches': [], 'input_only': needed <= input_names})
            else:
                unsupported.append({'relation': rid, 'location': node.get('location'),
                                    'reason': 'composed external helper execution is not supported'})
            return 'call'
        if external:
            occurrence = origin if not node['auxiliary'] else node['id']
            call = {**node, 'node_id': node['id'], 'id': occurrence,
                    'invert': negative,
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
            if kind in ('relation', 'not_relation'):
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
              'external_relations': roles['external'], 'helper_reasons': roles['reasons'],
              'internal_helpers': roles['internal'], 'unsupported': unsupported,
              'all_conditions': all_conditions, 'proof_conditions': proof,
              'conditions': all_conditions, 'checks': checks, 'goal_block': clause['goal_block'],
              'goal': clause['goal'], 'condition_blocks': clause['condition_blocks'],
              'calls': calls, 'variables': known,
              'bindings': [known[n] for n in known if n not in input_names],
              'origins': origins}
    result['plan_id'] = identity(result)
    return result
