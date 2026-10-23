"""Emit Lean from typed property IR; this compiler never runs an implementation."""
import json
from scripts.property.plan import variables


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
    observed_cvars = [v for v in cvars if 'E' in v['sources']]
    private_cvars = [v for v in cvars if 'E' not in v['sources']]
    names = {x['name']: 'input.' + quote(x['name']) for x in plan['inputs']}
    for value in outputs:
        names[value['name']] = quote(value['name'])

    def binder(value):
        return '(' + names[value['name']] + ' : ' + value['type']['lean'] + ')'

    def exists(values, body, indent):
        if not values:
            return body
        return (
            '∃ ' + binder(values[0]) + ',\n' + ' ' * (indent + 2)
            + exists(values[1:], body, indent + 2)
        )

    def forall(values, body, indent):
        if not values:
            return body
        return (
            '∀ ' + binder(values[0]) + ',\n' + ' ' * (indent + 2)
            + forall(values[1:], body, indent + 2)
        )

    def definition(name, values, body):
        arguments = ['(input : Input)'] + [binder(value) for value in values]
        return '\n'.join([
            'def ' + name,
            *['    ' + argument for argument in arguments[:-1]],
            '    ' + arguments[-1] + ' : Prop :=',
            '  ' + body,
        ])

    def atom(node):
        if node['kind'] == 'guard':
            return expression(node['expression'], names) + ' = true'
        if node['kind'] in ('relation', 'not_relation'):
            relation = node.get('lean_relation', 'SpecTec.' + quote(node['relation']))
            atom = '(' + relation + ' ' + ' '.join(expression(e, names) for e in node['arguments']) + ')'
            return '(¬ ' + atom + ')' if node['kind'] == 'not_relation' else atom
        if node['kind'] == 'let':
            return '(' + expression(node['target'], names) + ' = ' + expression(node['value'], names) + ')'
        raise ValueError('unsupported logical AL condition ' + node['kind'])

    def conj(items, continuation_indent):
        if not items:
            return 'True'
        if len(items) == 1:
            return items[0]
        separator = ' ∧\n' + ' ' * continuation_indent
        return separator.join('(' + x + ')' for x in items)

    conditions = plan['all_conditions']
    condition_atoms = [atom(node) for node in conditions]
    premise_body = conj(condition_atoms, 4 + 2 * len(cvars))
    goal_atom = atom(goal_node)
    # Existentially bind only outputs appearing in the goal atom. If it reads
    # an observed premise output, use the conditions for a pointwise obligation.
    if any(value['name'] in goal_names for value in observed_cvars):
        condition_indent = 2 + 2 * len(observed_cvars)
        condition_body = exists(
            private_cvars,
            conj(condition_atoms, condition_indent + 1 + 2 * len(private_cvars)),
            condition_indent + 1,
        )
        goal_body = forall(
            observed_cvars,
            '(' + condition_body + ') →\n'
            + ' ' * (condition_indent + 2)
            + exists(gvars, goal_atom, condition_indent + 2),
            2,
        )
    else:
        goal_body = exists(gvars, goal_atom, 2)
    return '\n'.join([
        'import Lean',
        'import Spec4Pbt.CorrectGen',
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
        definition('Goal', [], goal_body),
        '',
        definition('Premise', [], exists(cvars, premise_body, 2)),
        '',
        'abbrev generator := CorrectGen Premise',
        '',
        'def property : Prop :=\n'
        '  ∀ (input : Input),\n'
        '    Premise input →\n'
        '      Goal input',
        '',
        'end ' + namespace,
        '',
    ])
