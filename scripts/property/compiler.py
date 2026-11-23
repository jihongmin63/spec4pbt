"""Compile a typed property model and explicit observation contract."""
from pathlib import Path
import hashlib
import json
import subprocess
import tomllib

from .bridge import ROOT, build_bridge
from .model import CompileError, DebugProgram, ReplayProgram, SpecProperty


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def frontend_check(source):
    executable = build_bridge()
    command = ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
               str(executable), 'check', str(source)]
    result = subprocess.run(command, capture_output=True, text=True, timeout=120)
    if result.returncode:
        raise CompileError(result.stderr or result.stdout)
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise CompileError(f'invalid frontend response: {error}') from error


def compile_spec(source, config):
    source, config = Path(source).resolve(), Path(config).resolve()
    report = frontend_check(source)
    settings = tomllib.loads(config.read_text())
    definitions = report['definitions']
    by_name = {}
    for definition in definitions:
        by_name.setdefault(definition['name'], []).append(definition)
    def get_unique(name):
        matches = by_name.get(name, ())
        if len(matches) != 1:
            raise CompileError(f'ambiguous or missing relation ID: {name}')
        return matches[0]

    pre_name, goal_name = settings['precondition'], settings['goal']
    pre, goal = get_unique(pre_name), get_unique(goal_name)
    if not pre['defined'] or pre['rule_count'] != 1:
        raise CompileError(f'{pre_name}: Pre must have exactly one defined rule')
    if not goal['defined']:
        raise CompileError(f'{goal_name}: Goal must have a definition')
    names = pre['rule_inputs']
    if len(names) != len(pre['input_types']) or None in names or len(set(names)) != len(names):
        raise CompileError(f'{pre_name}: inputs must be distinct rule variables')
    goal_abi = pre['input_types'] + pre['output_types']
    if goal['input_types'] != goal_abi:
        raise CompileError(f'{goal_name}: Goal input types do not match Pre inputs and outputs')

    external = []
    seen = set()
    for item in settings.get('external', []):
        relation = item['relation']
        if relation in seen:
            raise CompileError(f'duplicate external relation: {relation}')
        seen.add(relation)
        definition = get_unique(relation)
        if 'observed_outputs' not in item:
            raise CompileError(f'{relation}: observed_outputs is required')
        positions = item['observed_outputs']
        if (not isinstance(positions, list) or
                any(type(p) is not int or p < 0 or p >= len(definition['output_types'])
                    for p in positions) or len(set(positions)) != len(positions)):
            raise CompileError(f'{relation}: invalid observed_outputs')
        if not item.get('adapter') or item.get('conversion') != 'json-v1':
            raise CompileError(f'{relation}: adapter and json-v1 conversion required')
        external.append({**item, 'observed_outputs': sorted(positions)})

    inputs = tuple({'name': name, 'type': typ} for name, typ
                   in zip(names, pre['input_types']))
    return SpecProperty(
        source=str(source), source_sha256=digest(source),
        config=str(config), config_sha256=digest(config),
        precondition=pre_name, goal=goal_name, inputs=inputs,
        pre_outputs=tuple(pre['output_types']),
        goal_inputs=tuple(goal['input_types']), external=tuple(external),
        definitions=tuple(definitions))


def analyze_replay(model):
    executable = build_bridge()
    command = ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
               str(executable), 'analyze', model.source]
    request = {'pre': model.precondition, 'goal': model.goal,
               'external': list(model.external)}
    result = subprocess.run(command, input=json.dumps(request) + '\n',
                            capture_output=True, text=True, timeout=120)
    if result.returncode:
        raise CompileError(result.stderr or result.stdout)
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise CompileError(f'invalid observability result: {error}') from error


def compile_replay(model):
    analysis = analyze_replay(model)
    return ReplayProgram(model=model, projection=analysis['projection'],
                         analysis=analysis)


def compile_debug(model):
    executable = build_bridge()
    command = ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
               str(executable), 'debug-check', model.source]
    request = {'pre': model.precondition, 'goal': model.goal}
    result = subprocess.run(command, input=json.dumps(request) + '\n',
                            capture_output=True, text=True, timeout=120)
    if result.returncode:
        raise CompileError(result.stderr or result.stdout)
    response = json.loads(result.stdout)
    return DebugProgram(model, response['available'], tuple(response['missing']),
                        response['al_md5'])
