#!/usr/bin/env python3
"""Run the pinned artifact's full-property theorem scheduler at fixed size 2.

The official ``quickchick 2`` tactic defines a proof-local ``theorem`` checker.
Extraction inside that proof captures its generated checker, then each OCaml
``run (theorem 2) 2 seed`` call is counted as exactly one outer attempt.

P0 states the fixed entity list literally, as the upstream theorem does.  A
candidate is checked unmodified by ``check.py``; the scheduler receives the
audited derivation copy from ``derivation.py`` with version-unique relation
names.  Two guards stop a batch whose schedule generates anything other than
the theorem's variables or whose extracted code lacks a reachable relation.
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
from cedar.derivation import ENTITY_NAMES_LITERAL, RewriteError, write_derivation_copy

ENV = ROOT / 'environment/env.sh'
SUPPORT = Path(__file__).with_name('Support.v')
DRIVER = Path(__file__).with_name('driver.ml')
DERIVATION = Path(__file__).with_name('derivation.py')
P0_VARIABLES = {'ets', 'acts', 'rs', 'e', 'es', 'ty', 'expr'}
SCHEDULER_FRESH = re.compile(r'v[A-Za-z0-9_]*_\Z')
FIXED_SIZE = 2
FIXED_SEEDS = (101, 202, 303, 404, 505, 1101, 1202, 1303, 1404, 1505)


def parse_quickchick_result(log):
    """Read the pinned tactic's internal test outcome, independent of sampling."""
    patterns = (
        ('passed', re.compile(r'^\+\+\+ Passed (\d+) tests \((\d+) discards\)$', re.MULTILINE)),
        ('gave_up', re.compile(r'^\*\*\* Gave up! Passed only (\d+) tests\r?\nDiscarded: (\d+)$', re.MULTILINE)),
        ('failed', re.compile(r'^\*\*\* Failed (?:right )?after (\d+) tests and (\d+) shrinks\. \((\d+) discards\)$', re.MULTILINE)),
    )
    found = [(status, match) for status, pattern in patterns
             for match in pattern.finditer(log)]
    result_lines = re.findall(r'^(?:\+\+\+|\*\*\*) (?:Passed|Gave up|Failed).*$',
                              log, flags=re.MULTILINE)
    if len(found) != 1 or len(result_lines) != 1:
        reason = 'ambiguous' if len(found) > 1 or len(result_lines) > 1 else 'unrecognized'
        raise RuntimeError(f'{reason} internal QuickChick result; see scheduler.log')
    status, match = found[0]
    if status == 'failed':
        tests, shrinks, discards = map(int, match.groups())
        return {'status': status, 'tests': tests, 'discards': discards,
                'shrinks': shrinks, 'summary': match.group(), 'log': 'scheduler.log'}
    tests, discards = map(int, match.groups())
    return {'status': status, 'tests': tests, 'discards': discards,
            'summary': match.group(), 'log': 'scheduler.log'}


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
Example entity_names_literal : Original.entity_names = ENTITY_NAMES := eq_refl.
Theorem observation : forall ets acts rs e es ty expr,
  WfSchema ENTITY_NAMES (MkSchema ets acts) ->
  ActionSchemaToRequestTypes acts [] rs ->
  SchemaToEnvironments (MkSchema ets acts) rs (e :: es) ->
  WfCedarType ENTITY_NAMES ty ->
  HasType (somepaths []) e expr ty -> true = true.
Proof.
  quickchick 2.
  Print Assumptions theorem.
  Extraction "theorem.ml" theorem.
  intros; reflexivity.
Qed.
Print Assumptions observation.
'''.replace('ENTITY_NAMES', ENTITY_NAMES_LITERAL)
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
  {target}.predicate_{candidate} x -> true = true.
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
    """Return (sources, prefix audit, derivation rewrite record, sequence)."""
    sources = output / 'sources'
    (sources / 'specification/cedar').mkdir(parents=True)
    (sources / 'property').mkdir()
    shutil.copy2(ROOT / 'specification/cedar/Spec.v',
                 sources / 'specification/cedar/Spec.v')
    shutil.copy2(property_dir / 'Original.v', sources / 'property/Original.v')
    checked, record, sequence = None, None, []
    if candidate != 'P0':
        session = Session(property_dir, selected=candidate, timeout=600)
        try:
            session.check()
            checked = str(session.finish())
        except Exception as error:
            session.finish(error)
            raise
        sequence = list(session.sequence)
        if not sequence or sequence[-1] != candidate:
            raise RuntimeError(f'checked sequence {sequence} does not end in {candidate}')
        record = write_derivation_copy(session.sources / 'property', sequence,
                                       sources / 'property')
        record['checked_sources'] = str(session.sources)
        (output / 'derivation-rewrite.json').write_text(json.dumps(record, indent=2) + '\n')
    shutil.copy2(SUPPORT, sources / 'Support.v')
    shutil.copy2(DRIVER, sources / 'driver.ml')
    (sources / 'Bench.v').write_text(source_for(candidate))
    return sources, checked, record, sequence


def schedule_text(log):
    """The printed theorem schedule, from its header to the checked conclusion."""
    start = log.find('Theorem Schedule:')
    end = log.find('=> check conclusion', start)
    if start < 0 or end < 0:
        raise RuntimeError('scheduler.log lacks a complete theorem schedule')
    return log[start + len('Theorem Schedule:'):end]


def check_derivation(sources, candidate, log, record):
    """Fail closed on the two scheduler behaviours that change the measurement."""
    binders = re.findall(r"(?:\(|,)\s*([A-Za-z_][A-Za-z0-9_']*)\s*:\s",
                         schedule_text(log))
    allowed = P0_VARIABLES if candidate == 'P0' else {'x'}
    generated = [name for name in binders
                 if name not in allowed and not SCHEDULER_FRESH.fullmatch(name)]
    if not binders or generated:
        raise RuntimeError(f'theorem schedule generates non-variables {generated}; '
                           'see scheduler.log')
    guards = {'status': 'passed', 'schedule_binders': binders}
    if candidate != 'P0':
        extracted = (sources / 'theorem.ml').read_text()
        missing = [name for name in record['reachable_relations']
                   if not re.search(rf'(?<![A-Za-z0-9]){re.escape(name)}_', extracted)]
        if missing:
            raise RuntimeError(f'extracted checker lacks reachable relations {missing}')
        guards['reachable_relations'] = record['reachable_relations']
    return guards


def compile_source(sources, candidate, output, sequence=()):
    logs = []
    coq = ['bash', str(ENV), 'coqc', '-q', *COQ_FLAGS]
    for label, path in [('spec', 'specification/cedar/Spec.v'),
                        ('original', 'property/Original.v'),
                        *((f'derivation-{version}', f'property/candidates/{version}/Candidate.v')
                          for version in sequence)]:
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
                              (Path(__file__), SUPPORT, DRIVER, DERIVATION,
                               Path(__file__).with_name('serialization.py'), ENV)},
              'commands': [], 'derivation': {'status': 'not_confirmed'}}
    try:
        sources, checked, record, sequence = snapshot(prop, args.candidate, output)
        result['prefix_check'] = checked
        if record is not None:
            result['derivation_rewrite'] = 'derivation-rewrite.json'
        result['commands'].extend(compile_source(sources, args.candidate, output, sequence))
        scheduler_log = (output / 'scheduler.log').read_text(errors='replace')
        result['quickchick'] = parse_quickchick_result(scheduler_log)
        result['derivation_guards'] = check_derivation(sources, args.candidate,
                                                       scheduler_log, record)
        result['derivation'] = {'status': 'succeeded', 'log': 'scheduler.log',
                                'extracted_checker': 'sources/theorem.ml'}
        if result['quickchick']['status'] == 'failed':
            raise RuntimeError('internal QuickChick test failed; see scheduler.log')
        counts, generated = run_samples(sources, output, args.candidate,
                                        args.seed, args.attempts)
        result['commands'].extend(adapter_check(sources, output, args.candidate, generated))
        result['counts'] = counts
        result['status'] = 'completed'
    except (CheckError, OSError, RuntimeError, ValueError, SerializationError, RewriteError,
            subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        result['status'] = 'failed'
        result['error'] = str(error)
        if (output / 'scheduler.log').is_file() and 'quickchick' not in result:
            try:
                result['quickchick'] = parse_quickchick_result(
                    (output / 'scheduler.log').read_text(errors='replace'))
            except RuntimeError:
                result['quickchick'] = {'status': 'unrecognized', 'log': 'scheduler.log'}
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(output / 'result.json')
    return 0 if result['status'] == 'completed' else 1


if __name__ == '__main__':
    sys.exit(main())
