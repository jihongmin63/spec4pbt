#!/usr/bin/env python3
"""Run the pinned artifact's full-property theorem scheduler at fixed size 2.

The official ``quickchick 2`` tactic defines a proof-local ``theorem`` checker.
Extraction inside that proof captures its generated checker, then each OCaml
``run (theorem 2) 2 seed`` call is counted as exactly one outer attempt.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check import Session, CheckError, COQ_FLAGS, ROOT
from cedar.serialization import (ADAPTER_PRELUDE, SerializationError, adapter_lemma,
                                 reconstruct_candidate, reconstruct_p0)

ENV = ROOT / 'environment/env.sh'
SUPPORT = Path(__file__).with_name('Support.v')
DRIVER = Path(__file__).with_name('driver.ml')
FIXED_SIZE = 2
FIXED_SEEDS = (101, 202, 303, 404, 505, 1101, 1202, 1303, 1404, 1505)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_for(candidate):
    if candidate == 'P0':
        return '''From QuickChick Require Import QuickChick.
From Coq Require Import List String ZArith.
Import ListNotations.
Import QcDefaultNotation.
Open Scope qc_scope.
Open Scope string_scope.
Require Import Specification.cedar.Spec Support Property.Original.
Check p0_packaging.
Theorem observation : forall ets acts rs e es ty expr,
  WfSchema Original.entity_names (MkSchema ets acts) ->
  ActionSchemaToRequestTypes acts [] rs ->
  SchemaToEnvironments (MkSchema ets acts) rs (e :: es) ->
  WfCedarType Original.entity_names ty ->
  HasType (somepaths []) e expr ty -> true = true.
Proof.
  quickchick 2.
  Print Assumptions theorem.
  Extraction "theorem.ml" theorem.
  intros; reflexivity.
Qed.
Print Assumptions observation.
'''
    if not candidate.startswith('v') or not candidate[1:].isdigit():
        raise ValueError('candidate must be P0 or vNNN')
    target = f'Property.candidates.{candidate}.Candidate'
    return f'''From QuickChick Require Import QuickChick.
From Coq Require Import List String ZArith.
Import ListNotations.
Import QcDefaultNotation.
Open Scope qc_scope.
Open Scope string_scope.
Require Import Specification.cedar.Spec Support {target}.
Theorem observation : forall x : Original.Input,
  {target}.predicate x -> true = true.
Proof.
  quickchick 2.
  Print Assumptions theorem.
  Extraction "theorem.ml" theorem.
  intros; reflexivity.
Qed.
Print Assumptions observation.
'''


def command(args, cwd, log, timeout=600):
    started = time.monotonic()
    with Path(log).open('w') as stream:
        try:
            done = subprocess.run(args, cwd=cwd, stdout=stream,
                                  stderr=subprocess.STDOUT, timeout=timeout)
        except subprocess.TimeoutExpired as error:
            raise RuntimeError(f'timed out: {args}; see {log}') from error
    if done.returncode:
        tail = Path(log).read_text(errors='replace')[-1800:]
        raise RuntimeError(f'command failed ({done.returncode}): {args}; see {log}\n{tail}')
    return {'command': list(map(str, args)), 'seconds': round(time.monotonic() - started, 6),
            'log': str(Path(log).name)}


def snapshot(property_dir, candidate, output):
    sources = output / 'sources'
    if candidate == 'P0':
        (sources / 'specification/cedar').mkdir(parents=True)
        (sources / 'property').mkdir()
        shutil.copy2(ROOT / 'specification/cedar/Spec.v',
                     sources / 'specification/cedar/Spec.v')
        shutil.copy2(property_dir / 'Original.v', sources / 'property/Original.v')
        checked = None
    else:
        session = Session(property_dir, selected=candidate, timeout=600)
        try:
            session.check()
            checked = str(session.finish())
        except Exception as error:
            session.finish(error)
            raise
        shutil.copytree(session.sources, sources)
    shutil.copy2(SUPPORT, sources / 'Support.v')
    shutil.copy2(DRIVER, sources / 'driver.ml')
    (sources / 'Bench.v').write_text(source_for(candidate))
    return sources, checked


def compile_source(sources, candidate, output):
    logs = []
    coq = ['bash', str(ENV), 'coqc', '-q', *COQ_FLAGS]
    if candidate == 'P0':
        for label, path in [('spec', 'specification/cedar/Spec.v'),
                            ('original', 'property/Original.v')]:
            logs.append(command([*coq, path], sources, output / f'{label}.log'))
    logs.append(command([*coq, 'Support.v'], sources, output / 'support.log'))
    logs.append(command([*coq, 'Bench.v'], sources, output / 'scheduler.log'))
    scheduler_log = (output / 'scheduler.log').read_text(errors='replace')
    if 'Theorem Schedule:' not in scheduler_log or 'Pieces:' not in scheduler_log:
        raise RuntimeError('official full-property theorem scheduler did not run')
    if 'theorem.ml' not in {p.name for p in sources.iterdir()}:
        raise RuntimeError('official scheduler checker was not extracted')
    logs.append(command(['bash', str(ENV), 'coqchk', '-silent', *COQ_FLAGS, 'Bench'],
                        sources, output / 'kernel.log'))
    ocaml = ['bash', str(ENV), 'ocamlfind', 'ocamlopt', '-package', 'zarith,unix',
             '-linkpkg', '-rectypes', '-w', '-a']
    logs.append(command([*ocaml, '-c', 'theorem.mli'], sources, output / 'interface.log'))
    interface = (sources / 'theorem.mli').read_text()
    evaluators = re.findall(
        r"^val (run\w*) : 'a1 g -> int -> randomSeed -> 'a1$",
        interface, flags=re.MULTILINE)
    if len(evaluators) != 1:
        raise RuntimeError(f'cannot identify unique extracted generator evaluator: {evaluators}')
    driver = sources / 'driver.ml'
    original_driver = driver.read_text()
    marker = 'run (theorem 2) 2 seed'
    if original_driver.count(marker) != 1:
        raise RuntimeError('sampler driver evaluator marker changed')
    driver.write_text(original_driver.replace(marker,
                                       f'{evaluators[0]} (theorem 2) 2 seed'))
    logs.append(command([*ocaml, 'theorem.ml', 'driver.ml', '-o', 'sampler'],
                        sources, output / 'compile-sampler.log'))
    logs[-1]['generator_evaluator'] = evaluators[0]
    return logs


def adapter_check(sources, output, candidate, generated):
    if candidate != 'P0':
        return []
    logs = []
    coq = ['bash', str(ENV), 'coqc', '-q', *COQ_FLAGS]
    for start in range(0, len(generated), 250):
        rows = generated[start:start + 250]
        name = f'Adapter{start // 250:04d}.v'
        body = ADAPTER_PRELUDE + '\n'.join(
            adapter_lemma(j, row['input_coq'], row['binder_literals'])
            for j, row in enumerate(rows))
        (sources / name).write_text(body)
        logs.append(command([*coq, name], sources, output / f'adapter-{start // 250:04d}.log'))
    return logs


def run_samples(sources, output, candidate, seed, attempts):
    expected = 5 if candidate == 'P0' else 1
    raw_path = output / 'raw-attempts.jsonl'
    with raw_path.open('w') as stream:
        subprocess.run([str(sources / 'sampler'), str(seed), str(attempts), str(expected)],
                       cwd=sources, stdout=stream, check=True, timeout=600)
    generated = []
    counts = {'generated': 0, 'discard': 0}
    input_path = output / 'attempts.jsonl'
    with raw_path.open() as raw, input_path.open('w') as stream:
        for i, line in enumerate(raw):
            row = json.loads(line)
            if row['attempt'] != i or row['seed'] != seed:
                raise RuntimeError(f'wrong outer-attempt index at row {i}')
            status = row['status']
            if status not in counts:
                raise RuntimeError(f'incomplete or failed generated attempt {i}: {status}')
            counts[status] += 1
            if status == 'generated':
                if candidate == 'P0':
                    expression, binders, scheduler_names = reconstruct_p0(row['fields'])
                    generated.append({'input_coq': expression, 'binder_literals': binders})
                else:
                    expression = reconstruct_candidate(row['fields'])
                    scheduler_names = None
                input_coq = expression
            else:
                input_coq = None
                scheduler_names = None
            stream.write(json.dumps({'id': f'{candidate}-{seed}-{i:05d}',
                                     'attempt': i, 'seed': seed,
                                     'scheduler_entity_names': scheduler_names,
                                     'input_coq': input_coq}, ensure_ascii=True) + '\n')
    if sum(counts.values()) != attempts:
        raise RuntimeError('interrupted batch: fewer outer attempts than requested')
    return counts, generated


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('property', type=Path)
    parser.add_argument('--candidate', required=True)
    parser.add_argument('--seed', type=int, required=True, choices=FIXED_SEEDS)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--attempts', type=int, default=10000)
    parser.add_argument('--test-mode', action='store_true',
                        help='permit a shorter batch for real Coq regression tests')
    args = parser.parse_args()
    if args.attempts <= 0 or (args.attempts != 10000 and not args.test_mode):
        parser.error('production batches require exactly 10000 outer attempts')
    prop = args.property.resolve()
    output = args.output_dir.resolve()
    if output.exists():
        parser.error('output directory already exists; evidence is append-only')
    if not output.is_relative_to(prop / '.runs'):
        parser.error('output must be inside the property-local .runs directory')
    output.mkdir(parents=True)
    result = {'status': 'running', 'candidate': args.candidate, 'seed': args.seed,
              'attempts': args.attempts, 'size': FIXED_SIZE,
              'test_mode': args.test_mode, 'source_hashes': {
                  'Original.v': sha(prop / 'Original.v'),
                  'Spec.v': sha(ROOT / 'specification/cedar/Spec.v')},
              'tool_hashes': {p.name: sha(p) for p in
                              (Path(__file__), SUPPORT, DRIVER,
                               Path(__file__).with_name('serialization.py'), ENV)},
              'commands': []}
    try:
        sources, checked = snapshot(prop, args.candidate, output)
        result['prefix_check'] = checked
        result['commands'].extend(compile_source(sources, args.candidate, output))
        counts, generated = run_samples(sources, output, args.candidate,
                                        args.seed, args.attempts)
        result['commands'].extend(adapter_check(sources, output, args.candidate, generated))
        result['counts'] = counts
        result['status'] = 'passed'
    except (CheckError, OSError, RuntimeError, ValueError, SerializationError,
            subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        result['status'] = 'failed'
        result['error'] = str(error)
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(output / 'result.json')
    return 0 if result['status'] == 'passed' else 1


if __name__ == '__main__':
    sys.exit(main())
