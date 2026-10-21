"""Emit Lean from typed property IR; this compiler never runs an implementation."""
import json
from pbt.property_plan import variables


def string(value):
    return json.dumps(value, ensure_ascii=False)


def quote(value):
    if '«' in value or '»' in value or '\n' in value:
        raise ValueError('unrepresentable Lean identifier')
    return '«' + value + '»'


def expression(e, names):
    k=e['kind']; ty=e['type']['lean']
    if k=='variable': return names[e['name']]
    if k=='number': return f'({e["value"]} : {ty})'
    if k=='bool': return 'true' if e['value'] else 'false'
    if k=='text': return string(e['value'])
    if k=='cast': return f'({expression(e["value"],names)} : {ty})' if e['value']['type']['lean']==ty else f'(Int.ofNat {expression(e["value"],names)})'
    if k=='field': return f'({expression(e["base"],names)}).{quote(e["field"])}'
    if k=='index': return f'({expression(e["base"],names)})[{expression(e["index"],names)}]!'
    if k=='length': return f'({expression(e["value"],names)}).length'
    if k=='record': return '({ '+', '.join(quote(f)+' := '+expression(v,names) for f,v in e['fields'].items())+f' }} : {ty})'
    if k=='tuple': return '('+', '.join(expression(x,names) for x in e['items'])+')'
    if k=='list': return '(['+', '.join(expression(x,names) for x in e['items'])+f'] : {ty})'
    if k=='option': return '(none : '+ty+')' if not e['items'] else '(some '+expression(e['items'][0],names)+')'
    if k=='unary':
        v=expression(e['value'],names); op=e['operator']
        return f'(!{v})' if op=='~' else f'(-{v})' if op=='-' else v
    if k in ('binary','compare'):
        a,b=expression(e['left'],names),expression(e['right'],names);op=e['operator']
        if k=='compare':
            op={'=/=':'≠','<=':'≤','>=':'≥'}.get(op,op)
            return f'(decide ({a} {op} {b}))'
        if op in ('/','\\'):
            raise ValueError('partial SpecTec division/modulo is unsupported in property expressions')
        if op in ('+','-','*','^'): return f'({a} {op} {b})'
        if op=='/\\': return f'({a} && {b})'
        if op=='\\/': return f'({a} || {b})'
        if op=='=>': return f'(!{a} || {b})'
        if op=='<=>': return f'({a} == {b})'
        raise ValueError(f'unsupported property operator {op}')
    raise ValueError(f'unsupported executable property expression {k}')


def render_contract(plan, namespace, spec_module):
    """Render the whole source contract, including observed conditions.

    The AL proof subset only controls runtime omission. It never determines
    generator support or the property theorem's premise.
    """
    source_names = set().union(*(variables(x['expression']) if x['kind'] == 'guard'
                                 else set().union(*(variables(a) for a in x['arguments']))
                                 for x in plan['all_conditions']))
    goal_node = plan['goal']
    goal_names = (variables(goal_node['expression']) if goal_node['kind'] == 'guard'
                  else set().union(*(variables(a) for a in goal_node['arguments'])))
    outputs = [v for v in plan['variables'].values() if v['producer'] is not None]
    cvars = [v for v in outputs if v['producer'] != 'goal' and v['name'] in source_names]
    gvars = [v for v in outputs if v['producer'] == 'goal' and v['name'] in goal_names]
    rvars = [v for v in outputs if v['producer'] != 'goal']
    goal_al_vars = [v for v in outputs if v['producer'] == 'goal']
    names = {x['name']: 'input.' + quote(x['name']) for x in plan['inputs']}
    for value in outputs:
        names[value['name']] = quote(value['name'])

    def binders(values):
        return ' '.join('(' + names[v['name']] + ' : ' + v['type']['lean'] + ')' for v in values)

    def args(values):
        return ' '.join(names[v['name']] for v in values)

    def exists(values, body):
        return '∃ ' + binders(values) + ', ' + body if values else body

    def forall(values, body):
        return '∀ ' + binders(values) + ', ' + body if values else body

    def atom(node):
        if node['kind'] == 'guard':
            return expression(node['expression'], names) + ' = true'
        if node['kind'] == 'relation':
            relation = node.get('lean_relation', 'SpecTec.' + quote(node['relation']))
            return '(' + relation + ' ' + ' '.join(expression(e, names) for e in node['arguments']) + ')'
        if node['kind'] == 'let':
            return '(' + expression(node['target'], names) + ' = ' + expression(node['value'], names) + ')'
        raise ValueError('unsupported logical AL condition ' + node['kind'])

    def conj(items):
        return ' ∧ '.join('(' + x + ')' for x in items) if items else 'True'

    conditions = plan['all_conditions']
    body = conj([atom(node) for node in conditions])
    condition_nodes = [node for block in plan['condition_blocks'] for node in block['nodes']]
    call_facts = conj([atom(node) for node in condition_nodes if node['kind'] in ('relation', 'let')])
    observed_nodes = [node for block in plan['checks'] for node in block['nodes']]
    observed = conj([atom(node) for node in observed_nodes if node['kind'] == 'guard'])
    goal_al_nodes = plan['goal_block']['nodes']
    goal_facts = conj([atom(node) for node in goal_al_nodes if node['kind'] in ('relation', 'let')])
    goal_checks = conj([atom(node) for node in goal_al_nodes if node['kind'] == 'guard'])
    progress = []
    prior_nodes = []
    prior_vars = []
    for block in [*plan['condition_blocks'], plan['goal_block']]:
        block_vars = [v for v in outputs if v['producer'] == block['origin']]
        for node in block['nodes']:
            if node['kind'] == 'relation':
                prefix = conj([atom(p) for p in prior_nodes])
                progress.append(forall(prior_vars,
                    prefix + ' → ' + exists(block_vars, atom(node))))
            if node['kind'] in ('relation', 'let'):
                prior_nodes.append(node)
        prior_vars += block_vars
    goal = atom(goal_node)
    cargs = args(cvars)
    rargs = args(rvars)
    al_goal_args = args(rvars + goal_al_vars)
    goal_reference = forall(goal_al_vars,
        'GoalALFacts input ' + al_goal_args + ' → GoalALChecks input ' + al_goal_args)
    reference_body = ('CallFacts input ' + rargs + ' → ObservedChecks input ' + rargs +
        ' ∧ ' + exists(gvars, 'Goal input ' + args(cvars + gvars)) + ' ∧ (' + goal_reference + ')')
    return '\n'.join([
        'import Lean',
        'import ' + spec_module,
        '',
        'set_option autoImplicit false',
        'set_option linter.unusedVariables false',
        'namespace ' + namespace,
        '',
        'structure Input where',
        *['  ' + quote(x['name']) + ' : ' + x['type']['lean'] for x in plan['inputs']],
        '  deriving Lean.FromJson, Lean.ToJson',
        'def encodeInput (input : Input) : Lean.Json := Lean.toJson input',
        '',
        'def Conditions (input : Input) ' + binders(cvars) + ' : Prop := ' + body,
        'def Goal (input : Input) ' + binders(cvars + gvars) + ' : Prop := ' + goal,
        'def Premise (input : Input) : Prop := ' + exists(cvars, 'Conditions input ' + cargs),
        'def SpecProperty : Prop := ∀ (input : Input), ' +
            forall(cvars, 'Conditions input ' + cargs + ' → ' + exists(gvars, 'Goal input ' + args(cvars + gvars))),
        'def CallFacts (input : Input) ' + binders(rvars) + ' : Prop := ' + call_facts,
        'def ObservedChecks (input : Input) ' + binders(rvars) + ' : Prop := ' + observed,
        'def GoalALFacts (input : Input) ' + binders(rvars + goal_al_vars) + ' : Prop := ' + goal_facts,
        'def GoalALChecks (input : Input) ' + binders(rvars + goal_al_vars) + ' : Prop := ' + goal_checks,
        'def CallProgress (input : Input) : Prop := ' + conj(progress),
        'def ReferenceRun (input : Input) : Prop := CallProgress input ∧ (' +
            forall(rvars, reference_body) + ')',
        '',
        'end ' + namespace,
        '',
    ])
