#!/usr/bin/env python3
"""Run bounded native/replay/Rocq comparisons and the unchanged Module_ok oracle."""
from __future__ import annotations

from collections import Counter
from copy import deepcopy
import fcntl
import json
import os
from pathlib import Path
import subprocess
import time

from scripts.toolchain import PROJECT
from wasm_cases import Configuration, constant, replay_cases
from wasm_codec import array, functions, instruction_counts, local_count, module_term, record, signature_counts, signatures


EXPERIMENT: Path = PROJECT / 'experiments/generator-haskell'
BUILD: Path = PROJECT / 'build/generator-haskell'
EVIDENCE: Path = PROJECT / 'build/wasm/haskell-generality'
TRANSLATED: Path = BUILD / 'translated'
BASE: Path = BUILD / 'hs-to-rocq-5e6a7bddfa02b818a9e8490ed107b11bd52a84e4/examples/rocq9.0/base'
GHC: Path = BUILD / 'ghc-9.10.3-x86_64-unknown-linux/bin/ghc'
COQC: Path = Path('/home/min/.opam/cris-workshop/bin/coqc')
SIZES: tuple[int, ...] = (0, 1, 2, 4, 8, 13)
SEEDS: tuple[int, ...] = (0, 1, 17, 2026, 4294967295, 18446744073709551615)


def execute(name: str, command: list[str], seconds: int, expected_exit: int) -> str:
    environment: dict[str, str] = dict(os.environ)
    environment.update(CARGO_BUILD_JOBS='1', MAKEFLAGS='-j1', LEAN_NUM_THREADS='1',
                       OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1')
    timed: list[str] = [
        '/usr/bin/time', '-f', '%e', '-o', str(EVIDENCE / f'{name}.seconds'),
        'timeout', f'{seconds}s', *command,
    ]
    started: float = time.monotonic()
    result = subprocess.run(timed, cwd=PROJECT, env=environment, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False, timeout=seconds + 600)
    (EVIDENCE / f'{name}.log').write_text(result.stdout)
    (EVIDENCE / f'{name}.wall-seconds').write_text(f'{time.monotonic() - started:.3f}\n')
    if result.returncode != expected_exit:
        raise RuntimeError(f'{name} exited {result.returncode}, expected {expected_exit}; see {EVIDENCE / f"{name}.log"}')
    return result.stdout


def execute_locked(name: str, command: list[str], seconds: int, expected_exit: int) -> str:
    """Serialize heavy processes while measuring lock wait separately."""
    started: float = time.monotonic()
    with Path('/tmp/spec4pbt-wasm-build.lock').open('a') as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        (EVIDENCE / f'{name}.lock-seconds').write_text(f'{time.monotonic() - started:.3f}\n')
        return execute(name, command, seconds, expected_exit)


def parse_rows(text: str) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for line in text.splitlines():
        value: object = json.loads(line)
        if not isinstance(value, dict):
            raise ValueError(f'Expected JSON object: {line}')
        rows.append(value)
    return rows


def write_jsonl(path: Path, rows: list[dict[str, object]]) -> None:
    path.write_text(''.join(json.dumps(row, separators=(',', ':')) + '\n' for row in rows))


def config_term(config: Configuration) -> str:
    return '(WasmGenerator.GeneratorConfig ' + ' '.join(f'{value}%Z' for value in config) + ')'


def list_term(values: tuple[int, ...]) -> str:
    return '[' + '; '.join(f'({value})%Z' for value in values) + ']'


def output_check(name: str, call: str, row: dict[str, object]) -> str:
    return f'Example {name} : {call} = Data.Either.Right {module_term(row)}. Proof. vm_compute. reflexivity. Qed.'


def check_oracle(name: str, rows: list[dict[str, object]], expected: bool) -> None:
    path = EVIDENCE / f'{name}.jsonl'
    write_jsonl(path, rows)
    verdicts = parse_rows(execute_locked(name, ['python3', '-m', 'experiments.wasm.check', str(path)],
                                        180, 0 if expected else 1))
    if len(verdicts) != len(rows) or any(verdict.get('module_ok') is not expected for verdict in verdicts):
        raise AssertionError(f'Unexpected {name} oracle verdicts')


def negative_modules() -> list[dict[str, object]]:
    cases = {case.name: case.expected for case in replay_cases()}
    base = cases['u32-boundaries-local-mutation-arithmetic']
    negatives: list[dict[str, object]] = []
    for change in ('empty-body', 'bad-type', 'bad-local', 'bad-call',
                   'bad-export', 'duplicate-export', 'bad-start', 'set-underflow'):
        row = deepcopy(base)
        body = record(functions(row)[0], {'FTYPE', 'LOCALS', 'BODY'})
        if change == 'empty-body':
            body['BODY'] = []
        elif change == 'bad-type':
            body['FTYPE'] = 999
        elif change == 'bad-local':
            body['BODY'] = [{'LOCAL.GET': 999}]
        elif change == 'bad-call':
            body['BODY'] = [{'CALL': 999}]
        elif change == 'bad-export':
            row['EXPORTS'] = [{'NAME': [102, 48], 'EDESC': {'FuncExport': 999}}]
        elif change == 'duplicate-export':
            row['EXPORTS'] = array(row['EXPORTS']) * 2
        elif change == 'bad-start':
            row['START'] = {'SFUNC': 0}
        else:
            body['BODY'] = [{'LOCAL.SET': 0}, constant(0)]
        negatives.append(row)
    call_underflow = deepcopy(cases['forward-and-recursive-four-argument-calls'])
    record(functions(call_underflow)[0], {'FTYPE', 'LOCALS', 'BODY'})['BODY'] = [{'CALL': 1}]
    negatives.append(call_underflow)
    for body in ([constant(0)],
                 [{'BLOCK': [{'VarBlockType': 999}, []]}],
                 [{'BLOCK': [{'VarBlockType': 1}, []]}],
                 [constant(0), {'IF % % ELSE %': [{'VarBlockType': 0}, [constant(0)], []]}]):
        row = deepcopy(cases['parameterized-multivalue-block-if'])
        record(functions(row)[0], {'FTYPE', 'LOCALS', 'BODY'})['BODY'] = body
        negatives.append(row)
    return negatives


def counterexamples() -> list[dict[str, object]]:
    """Valid pinned ASTs deliberately outside the implemented intermediate restriction."""
    base = deepcopy(replay_cases()[3].expected)
    wide_constant = deepcopy(base)
    record(functions(wide_constant)[0], {'FTYPE', 'LOCALS', 'BODY'})['BODY'] = [constant(4294967296)]
    empty_name = deepcopy(base)
    empty_name['EXPORTS'] = [{'NAME': [], 'EDESC': {'FuncExport': 0}}]
    i64 = deepcopy(base)
    i64['TYPES'] = [{'RecT': [{'SubT': ['Final', [], {'DefFuncT': {'FuncT': [[], [{'NumT': 'I64T'}]]}}]}]}]
    i64['FUNCS'] = [{'FTYPE': 0, 'LOCALS': [], 'BODY': [{'CONST': {'I64': 0}}]}]
    return [wide_constant, empty_name, i64]


def main() -> None:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    execute_locked('native-build', [str(GHC), '-O2', '-Wall', '-Werror', '-fforce-recomp',
        '-i' + str(EXPERIMENT / 'src'), '-outputdir', str(BUILD / 'wasm'),
        str(EXPERIMENT / 'src/WasmSample.hs'), '-o', str(BUILD / 'wasm-sample'),
        '+RTS', '-M768m', '-RTS'], 180, 0)
    execute_locked('translation', ['bash', str(EXPERIMENT / 'translate-wasm.sh'), str(COQC.parent)], 300, 0)
    checks = ['From Stdlib Require Import ZArith NArith List.', 'Require Import WasmGenerator Data.Either.',
              'Import ListNotations. Open Scope Z_scope.']
    rows: list[dict[str, object]] = []
    for size in SIZES:
        for seed in SEEDS:
            batch = parse_rows(execute(f'native-size{size}-seed{seed}',
                [str(BUILD / 'wasm-sample'), '3', str(size), str(seed)], 30, 0))
            if len(batch) != 3:
                raise ValueError(f'Expected 3 modules for size {size}, seed {seed}')
            for index, row in enumerate(batch):
                call = f'WasmGenerator.generateSample {index}%Z (WasmGenerator.sizeConfig {size}%Z) {seed}%N'
                checks.append(output_check(f'seeded_{len(rows)}', call, row))
                rows.append(row)
    explicit_config: Configuration = (3, 8, 4, 3, 5, 12, 16)
    explicit_seed = 18446744073709551615
    batch = parse_rows(execute('explicit-config-sample', [str(BUILD / 'wasm-sample'), 'sample',
        '3', str(explicit_seed), *map(str, explicit_config)], 30, 0))
    if len(batch) != 3:
        raise ValueError('Expected 3 explicit-config modules')
    for index, row in enumerate(batch):
        checks.append(output_check(f'explicit_{index}',
            f'WasmGenerator.generateSample {index}%Z {config_term(explicit_config)} {explicit_seed}%N', row))
        rows.append(row)
    seeded_count = len(rows)
    for case in replay_cases():
        tape = EVIDENCE / f'{case.name}.tape'
        tape.write_text(' '.join(map(str, case.tape)) + '\n')
        batch = parse_rows(execute(f'replay-{case.name}', [str(BUILD / 'wasm-sample'), 'replay',
            *map(str, case.config), str(tape)], 30, 0))
        if batch != [case.expected]:
            raise AssertionError(f'{case.name} did not produce the independently authored AST')
        rows.extend(batch)
        checks.append(output_check('replay_' + case.name.replace('-', '_'),
            f'WasmGenerator.replayModule {config_term(case.config)} {list_term(case.tape)}', batch[0]))
    check_oracle('modules', rows, True)
    negatives = negative_modules()
    check_oracle('negative', negatives, False)
    check_oracle('known-exclusions', counterexamples(), True)

    errors: tuple[tuple[str, tuple[int, ...], str, str], ...] = (
        ('exhausted', (), 'tape exhausted', '(WasmGenerator.TapeExhausted 1)'),
        ('out-of-range', (1,), 'outside [0,1)', '(WasmGenerator.ChoiceOutOfRange 1 1)'),
        ('negative', (-1,), 'outside [0,1)', '(WasmGenerator.ChoiceOutOfRange 1 (-1))'),
        ('min-int', (-9223372036854775808,), 'outside [0,1)', '(WasmGenerator.ChoiceOutOfRange 1 (-9223372036854775808))'),
        ('max-int', (9223372036854775807,), 'outside [0,1)', '(WasmGenerator.ChoiceOutOfRange 1 9223372036854775807)'),
        ('unused', (0, 0, 0, 0, 0), 'unused choices', '(WasmGenerator.UnusedChoices 1)'),
    )
    for name, values, message, expected in errors:
        tape = EVIDENCE / f'error-{name}.tape'
        tape.write_text(' '.join(map(str, values)) + '\n')
        log = execute(f'error-{name}', [str(BUILD / 'wasm-sample'), 'replay', *(['0'] * 7), str(tape)], 30, 1)
        if message not in log:
            raise AssertionError(f'Missing specific error for {name}: {log}')
        checks.append(f'Example error_{name.replace("-", "_")} : WasmGenerator.replayModule '
            f'(WasmGenerator.sizeConfig 0) {list_term(values)} = Data.Either.Left {expected}. '
            'Proof. vm_compute. reflexivity. Qed.')
    for name, token, message in (
        ('hex-token', '0x0', 'decimal digits only'),
        ('wide-token', '9223372036854775808', 'exceeds signed 64-bit Int'),
        ('missing-digits', '-', 'decimal digits only'),
    ):
        tape = EVIDENCE / f'error-{name}.tape'
        tape.write_text(token + '\n')
        log = execute(f'error-{name}', [str(BUILD / 'wasm-sample'), 'replay', *(['0'] * 7), str(tape)], 30, 1)
        if message not in log:
            raise AssertionError(f'Missing tape parsing rejection for {name}: {log}')
    core_expression = 'print [case replayModule (sizeConfig (-1)) [] of Left InvalidConfig -> True; _ -> False, ' \
        'case replayModule (Config 0 0 0 9223372036854775806 0 0 1) [] of Left InvalidConfig -> True; _ -> False, ' \
        'case generateSample (-1) (sizeConfig 0) 0 of Left InvalidConfig -> True; _ -> False]'
    core_log = execute_locked('core-errors', [str(GHC), '-i' + str(EXPERIMENT / 'src'),
        '-outputdir', str(BUILD / 'wasm'), str(EXPERIMENT / 'src/WasmGenerator.hs'), '-e', core_expression,
        '+RTS', '-M768m', '-RTS'], 60, 0)
    if core_log.strip() != '[True,True,True]':
        raise AssertionError(f'Native invalid-config checks failed: {core_log}')
    for number, call in enumerate((
        'WasmGenerator.replayModule (WasmGenerator.sizeConfig (-1)) []',
        'WasmGenerator.replayModule (WasmGenerator.GeneratorConfig 0 0 0 9223372036854775806 0 0 1) []',
        'WasmGenerator.generateSample (-1) (WasmGenerator.sizeConfig 0) 0%N',
    )):
        checks.append(f'Example invalid_config_{number} : {call} = Data.Either.Left WasmGenerator.InvalidConfig. '
                      'Proof. vm_compute. reflexivity. Qed.')
    for name, arguments, message in (
        ('seed-overflow', ['1', '0', '18446744073709551616'], 'SEED must be between'),
        ('fuel-limit', ['sample', '1', '0', '1', '1', '0', '0', '0', '0', '513'], 'recursion safety limit'),
        ('allocation-limit', ['1', '1000', '0'], 'recursion safety limit'),
        ('batch-limit', ['sample', '1000000', '0', '1', '8', '4', '3', '5', '12', '32'], 'allocation estimate'),
    ):
        log = execute(name, [str(BUILD / 'wasm-sample'), *arguments], 30, 1)
        if message not in log:
            raise AssertionError(f'Missing CLI rejection for {name}: {log}')
    checks.extend(f'Print Assumptions WasmGenerator.{name}.' for name in
                  ('generateSample', 'generateModule', 'generateCode', 'replayModule'))
    (EVIDENCE / 'CompleteOutputs.v').write_text('\n'.join(checks) + '\n')
    rocq_log = execute_locked('complete-output-rocq', [str(COQC), '-Q', str(BASE), '',
        '-Q', str(TRANSLATED), '', str(EVIDENCE / 'CompleteOutputs.v')], 360, 0)
    if 'Axioms:' in rocq_log or rocq_log.count('Closed under the global context') != 4:
        raise AssertionError('Unexpected assumptions in Rocq output check')
    counts: Counter[str] = Counter()
    for row in rows:
        for function in functions(row):
            counts.update(instruction_counts(record(function, {'FTYPE', 'LOCALS', 'BODY'})['BODY']))
    result: dict[str, object] = {
        'positive_modules': len(rows), 'seeded_modules': seeded_count, 'replay_modules': len(replay_cases()),
        'negative_mutations': len(negatives), 'valid_known_exclusions': len(counterexamples()),
        'distinct_modules': len({json.dumps(row, sort_keys=True) for row in rows}),
        'complete_rocq_module_equalities': len(rows), 'native_rocq_error_checks': len(errors) + 3,
        'cli_resource_and_parse_rejections': 7,
        'function_counts': dict(Counter(len(functions(row)) for row in rows)),
        'parameter_counts': dict(Counter(signature_counts(item)[0] for row in rows for item in signatures(row))),
        'result_counts': dict(Counter(signature_counts(item)[1] for row in rows for item in signatures(row))),
        'local_counts': dict(Counter(local_count(item) for row in rows for item in functions(row))),
        'instruction_counts': dict(counts), 'closed_assumption_reports': 4,
    }
    (EVIDENCE / 'result.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
