"""Compare native Rust with compiled Aeneas Lean and check the real Module_ok.

Run from the repository root after building native `wasm` and translating the core.
The generated Lean source is left unchanged; inputs and evidence are saved under build/wasm.
"""
from __future__ import annotations

from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from typing import Callable, cast

from scripts.tests.rust_wasm_cases import Config, replay_arguments, replay_cases

from .translate import executable_source
from experiments.wasm.check import check_modules
from scripts.toolchain import PROJECT


BUILD: Path = PROJECT / 'build/generator-rust'
EVIDENCE: Path = PROJECT / 'build/wasm/completeness-rust'
NATIVE: Path = BUILD / 'native-target/release/wasm'
CASES: tuple[tuple[int, int, int], ...] = tuple(
    (4, size, seed)
    for size in (1, 2, 3, 4, 5, 8, 16)
    for seed in (17, 2026, (1 << 64) - 4)
)
MODULE_FIELDS: frozenset[str] = frozenset({
    'TYPES', 'GLOBALS', 'TABLES', 'MEMS', 'TAGS', 'FUNCS', 'START',
    'ELEMS', 'DATAS', 'IMPORTS', 'EXPORTS',
})


def parse_modules(lines: list[str], source: str) -> list[dict[str, object]]:
    modules: list[dict[str, object]] = []
    for index, line in enumerate(lines):
        value: object = json.loads(line)
        if not isinstance(value, dict) or set(value) != MODULE_FIELDS:
            raise ValueError(f'{source} module {index} is not a complete canonical module object')
        modules.append(cast(dict[str, object], value))
    return modules


def native_result(arguments: list[str], environment: dict[str, str]) -> subprocess.CompletedProcess[str]:
    command: list[str] = [str(NATIVE), *arguments]
    return subprocess.run(
        command, cwd=PROJECT, env=environment, capture_output=True,
        text=True, check=False, timeout=30,
    )


def native(arguments: list[str], environment: dict[str, str]) -> list[dict[str, object]]:
    result: subprocess.CompletedProcess[str] = native_result(arguments, environment)
    if result.returncode != 0:
        raise ChildProcessError(
            f'{result.args!r} exited {result.returncode}; stdout={result.stdout[-1000:]!r}; stderr={result.stderr[-2000:]!r}'
        )
    return parse_objects(result.stdout.removesuffix('\n').split('\n'), str(result.args))


def native_sample(arguments: list[str], environment: dict[str, str]) -> tuple[list[dict[str, object]], str | None]:
    """Preserve every seed and any emitted prefix when reference production fails."""
    result: subprocess.CompletedProcess[str] = native_result(arguments, environment)
    error: str | None = None
    if result.returncode != 0:
        matched: re.Match[str] | None = re.fullmatch(
            r'Error: "(NoReferenceProducer: no initialized local or declared function produces non-null type [0-9]+)"\n?',
            result.stderr,
        )
        if result.returncode != 1 or matched is None:
            raise ChildProcessError(
                f'{result.args!r} exited {result.returncode}; stdout={result.stdout!r}; stderr={result.stderr!r}'
            )
        error = matched.group(1)
    lines: list[str] = result.stdout.removesuffix('\n').split('\n') if result.stdout else []
    return parse_objects(lines, str(result.args)), error


def native_report(arguments: list[str], environment: dict[str, str]) -> dict[str, object]:
    values = native(arguments, environment)
    if len(values) != 1:
        raise AssertionError(f'Expected one report for {arguments!r}; got {len(values)}')
    report_module(values[0])
    return values[0]


def parse_objects(lines: list[str], source: str) -> list[dict[str, object]]:
    values: list[dict[str, object]] = []
    for line in lines:
        value: object = json.loads(line)
        if not isinstance(value, dict):
            raise ValueError(f'{source}: expected JSON object, received {value!r}')
        values.append(cast(dict[str, object], value))
    return values


def execution_source(arguments: list[list[str]]) -> str:
    """Expose every CLI output and error for comparison, without changing generation."""
    calls: list[str] = ['#eval wasmOutcomeCase ' + json.dumps(args) for args in arguments]
    return '''import WasmMain

def wasmOutcomeCase (args : List String) : IO Unit := do
  try
    main args
  catch error =>
    (← IO.getStdout).putStrLn (Lean.Json.mkObj [("error", .str (toString error))]).compress

''' + '\n'.join(calls) + '\n'


def translated(arguments: list[list[str]], errors: list[tuple[list[str], str]], environment: dict[str, str]) -> list[dict[str, object]]:
    ready_value: object = json.loads((BUILD / 'bootstrap.json').read_text())
    if not isinstance(ready_value, dict) or not isinstance(ready_value.get('lean_bin'), str):
        raise ValueError('bootstrap.json must contain lean_bin')
    lean_bin: Path = Path(ready_value['lean_bin'])
    paths_value: object = json.loads((BUILD / 'lean-environment.json').read_text())
    names: tuple[str, ...] = ('LEAN_PATH', 'LEAN_SRC_PATH', 'LD_LIBRARY_PATH', 'LEAN_SYSROOT')
    if not isinstance(paths_value, dict) or any(not isinstance(paths_value.get(name), str) for name in names):
        raise ValueError('lean-environment.json must contain Lake compiler paths')
    paths: dict[str, str] = cast(dict[str, str], paths_value)
    compiler_environment: dict[str, str] = environment | {name: paths[name] for name in names}
    runner: Path = BUILD / 'lean/RunWasmCases.lean'
    runner.write_text(execution_source(arguments + [args for args, _ in errors]))
    result: subprocess.CompletedProcess[str] = subprocess.run(
        [str(lean_bin / 'lean'), '-j', '1', '-M', '3100', runner.name],
        cwd=BUILD / 'lean', env=compiler_environment, capture_output=True,
        text=True, check=False, timeout=600,
    )
    (EVIDENCE / 'lean-execution.log').write_text(result.stdout + result.stderr)
    if result.returncode != 0:
        raise ChildProcessError(
            f'Lean batch exited {result.returncode}; log={EVIDENCE / "lean-execution.log"}; '
            f'stderr={result.stderr[-2000:]!r}'
        )
    return parse_objects(result.stdout.removesuffix('\n').split('\n'), 'Lean batch')


def replace_first(value: object, tag: str, replacement: Callable[[object], object]) -> tuple[object, bool]:
    if isinstance(value, dict):
        if tag in value:
            return value | {tag: replacement(value[tag])}, True
        for key, child in value.items():
            changed, found = replace_first(child, tag, replacement)
            if found:
                return value | {key: changed}, True
    if isinstance(value, list):
        for index, child in enumerate(value):
            changed, found = replace_first(child, tag, replacement)
            if found:
                return value[:index] + [changed] + value[index + 1:], True
    return value, False


def empty_yes_branch(value: object) -> object:
    if not isinstance(value, list) or len(value) != 3:
        raise ValueError(f'Expected three conditional fields, received {value!r}')
    return [value[0], [], value[2]]


def mutations(conditional: dict[str, object], call: dict[str, object], wide: dict[str, object]) -> list[dict[str, object]]:
    altered: list[dict[str, object]] = []
    for tag, replacement in (
        ('BODY', lambda _: []), ('FTYPE', lambda _: 999),
        ('BODY', lambda _: [{'LOCAL.GET': 999}]), ('FuncExport', lambda _: 999),
    ):
        changed, found = replace_first(conditional, tag, replacement)
        if not found:
            raise AssertionError(f'No {tag} to mutate')
        altered.append(cast(dict[str, object], changed))
    duplicate_export = deepcopy(conditional)
    exports: object = duplicate_export['EXPORTS']
    if not isinstance(exports, list) or len(exports) != 2:
        raise ValueError('Conditional fixture needs exactly two exports')
    exports[1]['NAME'] = exports[0]['NAME']
    altered.append(duplicate_export)
    for module, tag, replacement in (
        (call, 'CALL', lambda _: 999),
        (conditional, 'IF % % ELSE %', empty_yes_branch),
        (wide, 'CONST', lambda _: {'I32': 0}),
    ):
        changed, found = replace_first(module, tag, replacement)
        if not found:
            raise AssertionError(f'No {tag} to mutate')
        altered.append(cast(dict[str, object], changed))
    altered.append(conditional | {'START': {'SFUNC': 0}})
    altered.append(wide | {'START': {'SFUNC': 999}})
    for body in (
        ['UNREACHABLE', {'CONST': {'I64': 7}}, {'BINOP': {'I32': 'IAdd'}}],
        ['UNREACHABLE', {'BLOCK': [{'ValBlockType': {'NumT': 'I32T'}}, []]}],
    ):
        changed, found = replace_first(conditional, 'BODY', lambda _: body)
        if not found:
            raise AssertionError('No function body for polymorphic-stack negative case')
        altered.append(cast(dict[str, object], changed))
    return altered


def report_module(report: dict[str, object]) -> dict[str, object]:
    if set(report) != {'module', 'choices', 'state', 'remaining'}:
        raise ValueError(f'Invalid execution report fields: {list(report)}')
    choices: object = report['choices']
    if not isinstance(choices, list) or any(type(value) is not int or not 0 <= value < 1 << 64 for value in choices):
        raise ValueError('Report choices must be u64 cells')
    if type(report['remaining']) is not int or (report['state'] is not None and type(report['state']) is not int):
        raise ValueError('Report remaining/state must be integers or null state')
    return parse_modules([json.dumps(report['module'])], 'report')[0]


def assert_targeted(modules: dict[str, dict[str, object]]) -> None:
    """Check observable shapes independently of instruction-selection implementation."""
    expected_memories: dict[str, list[tuple[str, int, int | None]]] = {
        'memory_only': [('I32AT', 0, None)],
        'memory32_limit': [('I32AT', 65536, 65536)],
        'memory64_limit': [('I64AT', 281474976710656, 281474976710656)],
        'memory64_unbounded_max': [('I64AT', 281474976710656, None)],
        'mixed_memories': [('I32AT', 1, 10), ('I64AT', 42, None), ('I32AT', 0, 65536)],
        'memory_stop_empty': [],
        'memory_early_stop': [('I32AT', 2, None)],
        'imports_memories_datas': [('I32AT', 0, None)],
    }
    for name, memories in expected_memories.items():
        expected: list[dict[str, object]] = [
            {'MTYPE': {'MemoryT': [address, {'MIN': minimum, 'MAX': maximum}]}}
            for address, minimum, maximum in memories
        ]
        if modules[name]['MEMS'] != expected:
            raise AssertionError(f'Memory address width, order, or inclusive page limits changed: {name}')
    for name, payloads in (
        ('passive_empty_string', ['']),
        ('passive_unicode', ['A\0🦀']),
        ('passive_unicode_line_separators', ['\u0085\u2028\u2029']),
        ('passive_two_segments', ['', 'a']),
        ('passive_stop_empty', []),
        ('imports_memories_datas', ['Hi']),
    ):
        if modules[name]['DATAS'] != [{'DINIT': payload, 'DMODE': 'Passive'} for payload in payloads]:
            raise AssertionError(f'Passive data payload or ordering changed: {name}')
    for name, module_name, item_name, address, minimum, maximum in (
        ('memory_import_only', [], [], 'I32AT', 0, None),
        ('memory_import_unbounded_names', [0, 1 << 80, 55296], [1114112, 1 << 64], 'I32AT', 65536, 65536),
        ('imports_memories_datas', [], [], 'I64AT', 281474976710656, None),
    ):
        imported: list[dict[str, object]] = [{
            'MODULENAME': module_name, 'ITEMNAME': item_name,
            'IDESC': {'MemImport': {'MemoryT': [address, {'MIN': minimum, 'MAX': maximum}]}},
        }]
        if modules[name]['IMPORTS'] != imported:
            raise AssertionError(f'Memory import names or descriptors changed: {name}')
    i64 = modules['natural_i64_2pow80_plus5']
    if i64['FUNCS'] != [{'FTYPE': 0, 'LOCALS': [], 'BODY': [{'CONST': {'I64': (1 << 80) + 5}}]}]:
        raise AssertionError('Unbounded i64 payload or exact instruction body changed')
    empty = modules['empty']
    if empty['FUNCS'] != [] or empty['TYPES'] != [] or empty['START'] is not None:
        raise AssertionError('Empty-module witness changed')
    types = modules['type_only']
    if len(types['TYPES']) != 2 or types['FUNCS'] != []:
        raise AssertionError('Type-only witness changed')
    wide = modules['six_functions_wide_signatures_locals_aliases']
    if len(wide['FUNCS']) != 6 or len(wide['TYPES']) != 1 or len(wide['EXPORTS']) != 12:
        raise AssertionError('Independent function/type/export counts not exercised')
    signature = wide['TYPES'][0]['RecT'][0]['SubT'][2]['DefFuncT']['FuncT']
    if len(signature[0]) != 4 or len(signature[1]) != 2 or len(wide['FUNCS'][0]['LOCALS']) != 3:
        raise AssertionError('Wide signatures, results, or locals not exercised')
    if wide['FUNCS'][0]['BODY'] != [{'CONST': {'I64': (1 << 64) - 1}}, {'CONST': {'I32': (1 << 32) - 1}}]:
        raise AssertionError('Full-width integer constants changed')
    if wide['EXPORTS'][-1]['NAME'] != list(b'e11'):
        raise AssertionError('Multi-digit export name was truncated')
    long = modules['long_sequence_start']
    if long['FUNCS'][0]['BODY'] != ['NOP'] * 64 or long['START'] != {'SFUNC': 0}:
        raise AssertionError('Fuel beyond five or empty-signature start not exercised')
    if modules['self_call']['FUNCS'][0]['BODY'] != [{'CALL': 0}]:
        raise AssertionError('Self-recursive Wasm call not exercised')
    nested: list[object] = [{'CONST': {'I32': 7}}]
    for _ in range(8):
        nested = [{'BLOCK': [{'ValBlockType': {'NumT': 'I32T'}}, nested]}]
    if modules['nested_blocks_depth_eight']['FUNCS'][0]['BODY'] != nested:
        raise AssertionError('Structured nesting beyond depth five not exercised')
    i32_block: dict[str, object] = {'ValBlockType': {'NumT': 'I32T'}}
    control_bodies: dict[str, list[object]] = {
        'unreachable_add': ['UNREACHABLE', {'BINOP': {'I32': 'IAdd'}}],
        'unreachable_one_concrete_operand': [
            'UNREACHABLE', {'CONST': {'I32': 7}}, {'BINOP': {'I32': 'IAdd'}}],
        'unreachable_nonempty_predecessor': [{'CONST': {'I64': 7}}, 'UNREACHABLE'],
        'loop_parameter_label': [{'LOOP': [i32_block, [{'BR': 0}]]}],
        'outer_block_label': [{'BLOCK': [i32_block, [
            {'BLOCK': [i32_block, [{'CONST': {'I32': 7}}, {'BR': 1}]]}]]}],
        'br_if_retains_argument': [{'CONST': {'I32': 7}}, {'CONST': {'I32': 0}}, {'BR_IF': 0}],
    }
    for name, body in control_bodies.items():
        if modules[name]['FUNCS'][0]['BODY'] != body:
            raise AssertionError(f'Exact polymorphic stack or label witness changed: {name}')
    mutual = modules['mutual_void_calls']['FUNCS']
    if mutual[0]['BODY'] != [{'CALL': 1}] or mutual[1]['BODY'] != [{'CALL': 0}]:
        raise AssertionError('Mutual void calls not exercised')
    forward = modules['forward_wide_call']['FUNCS'][0]['BODY']
    if len(forward) != 5 or forward[-1] != {'CALL': 1}:
        raise AssertionError('Forward call with four arguments not exercised')
    indexed = modules['indexed_block_parameters_multivalue']['FUNCS'][0]['BODY']
    expected: list[object] = [{'LOCAL.GET': 0}, {'LOCAL.GET': 1}, {'LOCAL.GET': 2}, {'LOCAL.GET': 3},
        {'BLOCK': [{'VarBlockType': 0}, ['DROP'] * 4 + [{'LOCAL.GET': 1}, {'LOCAL.GET': 0}]]}]
    if indexed != expected:
        raise AssertionError(f'Parameterized multi-result block changed: {indexed!r}')


def main() -> None:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    generated: Path = BUILD / 'lean/GeneratorRust.lean'
    generated_bytes: bytes = executable_source(generated)
    generated_hash: str = hashlib.sha256(generated_bytes).hexdigest()
    environment: dict[str, str] = dict(os.environ) | {'LEAN_NUM_THREADS': '1'}
    commands: list[list[str]] = [[str(count), str(size), str(seed)] for count, size, seed in CASES]
    commands.extend([['1', '0', '0'], ['1', '0', str((1 << 64) - 1)]])
    native_values: list[dict[str, object]] = []
    modules: list[dict[str, object]] = []
    sampling_errors: int = 0
    for arguments in commands:
        values, error = native_sample(arguments, environment)
        count: int = int(arguments[0])
        if (error is None and len(values) != count) or (error is not None and len(values) >= count):
            raise AssertionError(f'Wrong module count for {arguments}')
        native_values.extend(values)
        modules.extend(parse_modules([json.dumps(value) for value in values], 'legacy'))
        if error is not None:
            native_values.append({'error': error})
            sampling_errors += 1
    legacy_count: int = len(modules)
    profiles: tuple[Config, ...] = (
        Config(6, 8, 5, 3, 5, 10, 12, 0, 0, 0, 100000),
        Config(1, 3, 0, 0, 4, 4, 16, 0, 0, 0, 10000),
        Config(3, 5, 8, 4, 8, 3, 32, 0, 0, 0, 100000),
    )
    replay_pairs: int = 0
    for config in profiles:
        for seed in (0, 17, 2026, (1 << 64) - 1):
            args: list[str] = ['sample', *(str(value) for value in config), str(seed)]
            values, error = native_sample(args, environment)
            commands.append(args)
            if error is not None:
                if values:
                    raise AssertionError(f'Failed single sample emitted a report for {args!r}: {values!r}')
                native_values.append({'error': error})
                sampling_errors += 1
                continue
            if len(values) != 1:
                raise AssertionError(f'Expected one sample report for {args!r}; got {len(values)}')
            report: dict[str, object] = values[0]
            module = report_module(report)
            native_values.append(report)
            modules.append(module)
            tape = cast(list[int], report['choices'])
            args = ['replay', *(str(value) for value in config), ','.join(str(value) for value in tape)]
            replayed = native_report(args, environment)
            if replayed != report | {'state': None}:
                raise AssertionError('Recorded seed choices did not replay exactly')
            commands.append(args)
            native_values.append(replayed)
            modules.append(report_module(replayed))
            replay_pairs += 1
    targeted: dict[str, dict[str, object]] = {}
    for case in replay_cases():
        args = replay_arguments(case)
        report = native_report(args, environment)
        module = report_module(report)
        targeted[case.name] = module
        commands.append(args)
        native_values.append(report)
        modules.append(module)
    assert_targeted(targeted)
    zero: list[str] = ['0'] * 10 + ['1000']
    errors: list[tuple[list[str], str]] = [
        (['replay', *zero, '-'], 'TapeExhausted: missing choice at offset 0'),
        (['replay', *zero, '1'], 'ChoiceOutOfRange: offset=0, value=1, required value < 1'),
        (['replay', *zero, '0,0'], 'UnusedChoices: consumed=1, supplied=2'),
        (['sample', *(['0'] * 11), '0'], 'WorkLimit'),
        (['sample', '65', *zero[1:], '0'], 'CLI resource limit'),
        (['1', '33', '0'], 'CLI resource limit'),
        (['2', '1', str((1 << 64) - 1)], 'CLI resource limit'),
        (['replay', *zero, str(1 << 64)], 'exceeds u64'),
        (['replay', *(['0'] * 7), '3', '0', '0', '10', '0,2'],
         'ChoiceOutOfRange: offset=1, value=2, required value < 2'),
        (['replay', *(['0'] * 7), '1', '0', '0', '10', '0,1,0,65537'],
         'ChoiceOutOfRange: offset=3, value=65537, required value < 65537'),
        (['replay', *(['0'] * 7), '1', '0', '0', '10', '0,1,1,281474976710657'],
         'ChoiceOutOfRange: offset=3, value=281474976710657, required value < 281474976710657'),
        (['replay', *(['0'] * 7), '1', '0', '0', '10', '0,1,0,65536,1,1'],
         'ChoiceOutOfRange: offset=5, value=1, required value < 1'),
        (['replay', *(['0'] * 8), '1', '0', '10', '0,1,1,1112064'],
         'ChoiceOutOfRange: offset=3, value=1112064, required value < 1112064'),
        (['replay', *(['0'] * 8), '1', '0', '10', '0,1,2'],
         'ChoiceOutOfRange: offset=2, value=2, required value < 2'),
    ]
    errors.extend([
        (['replay', *(['0'] * 9), '1', '10', '0,2'],
         'ChoiceOutOfRange: offset=1, value=2, required value < 2'),
        (['replay', *(['0'] * 9), '1', '10', '0,1,0,0,0,2'],
         'ChoiceOutOfRange: offset=5, value=2, required value < 2'),
        (['replay', *(['0'] * 9), '1', '10', '0,1,0,0,0,1,4294967297'],
         'ChoiceOutOfRange: offset=6, value=4294967297, required value < 4294967297'),
    ])
    for args, expected in errors:
        result = subprocess.run([str(NATIVE), *args], env=environment, text=True,
                                capture_output=True, check=False, timeout=30)
        if result.returncode == 0 or result.stdout or expected not in result.stderr:
            raise AssertionError(f'Native did not reject {args!r} with {expected!r}: {result.stderr}')
    lean = translated(commands, errors, environment)
    if len(lean) != len(native_values) + len(errors):
        raise AssertionError(f'Native/Lean record counts differ: {len(native_values)}, {len(lean)}')
    for index, (native_value, lean_value) in enumerate(zip(native_values, lean[:len(native_values)], strict=True)):
        if native_value != lean_value:
            raise AssertionError(f'Full module/cursor/choices differ at sample {index}')
    for (_, expected), error in zip(errors, lean[len(native_values):], strict=True):
        if not isinstance(error.get('error'), str) or expected not in error['error']:
            raise AssertionError(f'Lean did not reject with {expected!r}: {error!r}')
    negative = mutations(targeted['inline_if'], targeted['self_call'], targeted['six_functions_wide_signatures_locals_aliases'])
    for address, minimum, maximum in (
        ('I32AT', 65537, None), ('I64AT', 281474976710657, None),
        ('I32AT', 1, 0), ('I64AT', 0, 281474976710657),
    ):
        negative.append(targeted['memory_only'] | {
            'MEMS': [{'MTYPE': {'MemoryT': [address, {'MIN': minimum, 'MAX': maximum}]}}]})
    for name, values in (('modules', modules), ('negative-modules', negative), ('reports', native_values)):
        (EVIDENCE / f'{name}.jsonl').write_text(''.join(json.dumps(value, separators=(',', ':')) + '\n' for value in values))
    outside_target = deepcopy(targeted['inline_if'])
    outside_target['EXPORTS'][0]['NAME'] = [120]  # A valid export named x, absent from generator support.
    outside_path: Path = EVIDENCE / 'outside-support.jsonl'
    outside_path.write_text(json.dumps(outside_target, separators=(',', ':')) + '\n')
    combined: Path = EVIDENCE / 'oracle-input.jsonl'
    combined.write_text((EVIDENCE / 'modules.jsonl').read_text() + outside_path.read_text()
                        + (EVIDENCE / 'negative-modules.jsonl').read_text())
    verdicts: list[bool] = check_modules(combined)
    if verdicts != [True] * (len(modules) + 1) + [False] * len(negative):
        raise AssertionError(f'Module_ok mismatch: {[i for i,v in enumerate(verdicts) if v != (i <= len(modules))]}')
    result: dict[str, object] = {
        'generated_lean_sha256': generated_hash,
        'legacy_modules': legacy_count, 'compared_complete_outputs': len(modules),
        'compared_sampling_errors': sampling_errors,
        'recorded_seed_replay_pairs': replay_pairs, 'targeted_cases': list(targeted),
        'distinct_modules': len({json.dumps(module, sort_keys=True) for module in modules}),
        'module_ok_pass': len(modules), 'module_ok_reject_mutations': len(negative),
        'native_and_lean_error_cases': len(errors) + sampling_errors,
        'module_ok_outside_support': ['export_named_x'],
    }
    if hashlib.sha256(generated.read_bytes()).hexdigest() != generated_hash:
        raise AssertionError('Generated Lean source changed during execution checks')
    (EVIDENCE / 'requests.json').write_text(json.dumps({'commands': commands, 'errors': errors}, indent=2) + '\n')
    (EVIDENCE / 'validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, separators=(',', ':')))


if __name__ == '__main__':
    main()
