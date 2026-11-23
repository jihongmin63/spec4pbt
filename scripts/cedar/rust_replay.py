"""Replay preserved Coq inputs through the unmodified artifact Cedar server.

The printers mirror the pinned artifact, including its limited string escaping.
No input is regenerated, deduplicated, or repaired. Unsupported wire data fails
closed. This is a test adapter, not a proof of serialization equivalence.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import select
import signal
import shutil
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

ROOT = Path(__file__).resolve().parents[2]
TOKEN = re.compile(r'\s*("(?:[^\"]|\"\")*"|-?\d+|[A-Za-z_][\w.]*|%Z|[][(),;])')
ARITY = {}
for count, names in {
    0: 'true false principal action resource context star not_ neg equals mem less lessEq add_ sub_ mul_ contains containsAll containsAny setExprNil recExprNil intType stringType recordTypeNil tt_ ff_ anyBool allpaths EmptyString',
    1: 'boolean int stringLit entityUID justLit like is_ lit var boolType entityType setType somepaths Ascii.ascii_of_nat',
    2: 'MkName MkEntityUID andExpr orExpr unaryApp getAttr hasAttr setExprCons MkEntitySchemaEntry MkSchema MkEnvironment String',
    3: 'ite binaryApp recExprCons MkActionSchemaEntry',
    4: 'recordTypeCons MkRequest',
    7: 'Original.mkInput',
}.items():
    ARITY.update({name: count for name in names.split()})


def parse(source):
    tokens, pos = [], 0
    while pos < len(source):
        if not source[pos:].strip():
            break
        match = TOKEN.match(source, pos)
        if not match:
            raise ValueError(f'unsupported Coq text at {source[pos:pos+60]!r}')
        tokens.append(match[1]); pos = match.end()
    i = 0

    def term():
        nonlocal i
        if i >= len(tokens):
            raise ValueError('incomplete constructor')
        token = tokens[i]; i += 1
        if token == '(':
            values = [term()]
            while i < len(tokens) and tokens[i] == ',':
                i += 1; values.append(term())
            if i >= len(tokens) or tokens[i] != ')':
                raise ValueError('unclosed tuple/group')
            i += 1
            value = values[0] if len(values) == 1 else tuple(values)
        elif token == '[':
            value = []
            if i < len(tokens) and tokens[i] != ']':
                value.append(term())
                while i < len(tokens) and tokens[i] == ';':
                    i += 1; value.append(term())
            if i >= len(tokens) or tokens[i] != ']':
                raise ValueError('unclosed list')
            i += 1
        elif token.startswith('"'):
            value = token[1:-1].replace('""', '"')
        elif re.fullmatch(r'-?\d+', token):
            value = int(token)
        elif token in ARITY:
            args = [term() for _ in range(ARITY[token])]
            if token == 'EmptyString': value = ''
            elif token == 'Ascii.ascii_of_nat': value = chr(args[0])
            elif token == 'String': value = args[0] + args[1]
            else: value = (token, *args)
        else:
            raise ValueError(f'unsupported constructor {token}')
        if i < len(tokens) and tokens[i] == '%Z':
            if not isinstance(value, int): raise ValueError('noninteger Z scope')
            i += 1
        return value

    value = term()
    if i != len(tokens): raise ValueError('trailing Coq tokens')
    return value


def name(n):
    _, base, namespaces = n
    return '::'.join(s if s else '""' for s in [*namespaces, base])


def quote(s):
    # Deliberately matches escapeString in the pinned artifact.
    return '"' + s + '"'


def ident(s):
    return s if re.fullmatch('[A-Za-z0-9_]+', s) else quote(s)


def expr(e):
    tag, *a = e
    if tag == 'lit':
        p, v = a[0]
        if p == 'boolean': return v[0]
        if p == 'int': return str(v)
        if p == 'stringLit': return quote(v)
        if p == 'entityUID': return name(v[1]) + '::' + quote(v[2])
    if tag == 'var': return a[0][0]
    if tag == 'ite': return f'if ({expr(a[0])}) then ({expr(a[1])}) else ({expr(a[2])})'
    if tag in ('andExpr', 'orExpr'):
        return f'({expr(a[0])}) ' + ('&&' if tag == 'andExpr' else '||') + f' ({expr(a[1])})'
    if tag == 'unaryApp':
        op, x = a; s = '(' + expr(x) + ')'
        if op[0] in ('not_', 'neg'): return ('!' if op[0] == 'not_' else '-') + s
        if op[0] == 'is_': return s + ' is ' + name(op[1])
        if op[0] == 'like': return s + ' like ' + quote(''.join('*' if p[0] == 'star' else p[1] for p in op[1]))
    if tag == 'binaryApp':
        op, x, y = a
        operator = dict(equals='==', mem=' in ', less='<', lessEq='<=', add_='+', sub_='-', mul_='*',
                        contains='.contains', containsAll='.containsAll', containsAny='.containsAny')[op[0]]
        return '(' + expr(x) + ')' + operator + '(' + expr(y) + ')'
    if tag in ('getAttr', 'hasAttr'):
        return '(' + expr(a[0]) + ')' + ('.' if tag == 'getAttr' else ' has ') + ident(a[1])
    if tag == 'setExprNil': return '[]'
    if tag == 'recExprNil': return '{}'
    if tag == 'setExprCons':
        items = []
        while e[0] == 'setExprCons':
            items.append(expr(e[1])); e = e[2]
        if e != ('setExprNil',): raise ValueError('malformed set tail')
        return '[' + ', '.join(items) + ']'
    if tag == 'recExprCons':
        items = []
        while e[0] == 'recExprCons':
            items.append(ident(e[1]) + ': ' + expr(e[2])); e = e[3]
        if e != ('recExprNil',): raise ValueError('malformed record tail')
        return '{' + ', '.join(items) + '}'
    raise ValueError(f'unsupported expression {tag}')


def type_str(t):
    tag, *a = t
    if tag in ('intType', 'stringType', 'boolType'):
        return dict(intType='Long', stringType='String', boolType='Bool')[tag]
    if tag == 'entityType': return name(a[0])
    if tag == 'setType': return 'Set<' + type_str(a[0]) + '>'
    if tag == 'recordTypeNil': return '{}'
    if tag == 'recordTypeCons':
        fields = []
        while t[0] == 'recordTypeCons':
            fields.append((t[1], t[2], t[3])); t = t[4]
        if t != ('recordTypeNil',): raise ValueError('malformed record type')
        return '{ ' + attrs(fields) + ' }'
    raise ValueError(f'unsupported type {tag}')


def attrs(fields):
    fields = [(f[0][0], f[0][1], f[1]) if len(f) == 2 else f for f in fields]
    return ', '.join(ident(s) + ('?: ' if optional == ('true',) else ': ') + type_str(t)
                     for s, optional, t in fields)


def schema(ets, acts):
    out = ''
    for n, (_, ancestors, fields) in ets:
        out += 'entity ' + name(n)
        if ancestors: out += ' in [' + ', '.join(map(name, ancestors)) + ']'
        if fields: out += ' { ' + attrs(fields) + ' }'
        out += '; '
    seen = set()
    for uid, (_, principals, resources, fields) in acts:
        aid = uid[2]
        if aid in seen: continue
        seen.add(aid)
        out += ('action ' + quote(aid) + ' appliesTo { principal: [' + ', '.join(map(name, principals))
                + '], resource: [' + ', '.join(map(name, resources)) + '], context: {' + attrs(fields) + '} }; ')
    return out


def wire(fields):
    if len(fields) != 5 or any('|||' in s or '\n' in s or '\r' in s for s in fields):
        raise ValueError('ambiguous artifact FIFO protocol')
    return '|||'.join(fields)


def payload(input_coq):
    tag, ets, acts, rs, env, es, ty, ep = parse(input_coq)
    if tag != 'Original.mkInput' or env[0] != 'MkEnvironment': raise ValueError('not an input')
    _, principal, action, resource, context = env[2]
    return wire([schema(ets, acts), name(principal) + '::"e1"', 'Action::' + quote(action[2]),
                 name(resource) + '::"e2"', expr(ep[0])])


def branch_sets(export):
    """Unique source branch outcomes, collapsed across generic instantiations."""
    groups = {g: {'covered': set(), 'total': set()} for g in ('cedar', 'validator', 'typecheck')}
    for unit in export['data']:
        for file in unit['files']:
            path = file['filename']
            match = re.search(r'/(cedar-policy(?:-core|-formatter)?-4\.8\.2)/(.+)', path)
            if match:
                path = '/'.join(match.groups())
            else:
                generated = re.search(r'/build/(cedar-policy(?:-core|-formatter)?)(?:/[^/]+|-[^/]+)/out/(src/.+)', path)
                if not generated: continue
                path = generated[1] + '-4.8.2/generated/' + generated[2]
            scopes = ['cedar']
            if '/src/validator/' in path or path.endswith('/src/validator.rs'): scopes.append('validator')
            if '/src/validator/typecheck/' in path or path.endswith('/src/validator/typecheck.rs'): scopes.append('typecheck')
            for b in file.get('branches', []):
                for side in (0, 1):
                    key = (path, *b[:4], side)
                    for scope in scopes:
                        groups[scope]['total'].add(key)
                        if b[4 + side] > 0: groups[scope]['covered'].add(key)
    return groups


def read_batch(batch):
    verdicts = {}
    for line in (batch / 'verdicts.jsonl').read_text().splitlines():
        v = json.loads(line)
        if v['id'] in verdicts: raise ValueError('duplicate verdict id')
        verdicts[v['id']] = v
    rows, counts, seen = [], Counter(), set()
    for line in (batch / 'attempts.jsonl').read_text().splitlines():
        row = json.loads(line)
        if row['id'] in seen: raise ValueError('duplicate attempt id')
        seen.add(row['id'])
        v = verdicts.pop(row['id'])
        if not row.get('input_coq'):
            if v['overall'] != 'no_generation': raise ValueError('missing input has a verdict')
            counts['no_result'] += 1; continue
        if hashlib.sha256(row['input_coq'].encode()).hexdigest() != v['input_sha256']:
            raise ValueError('verdict/input hash mismatch')
        counts[v['overall']] += 1
        if v['overall'] == 'valid':
            rows.append({**row, 'payload': payload(row['input_coq'])})
    if verdicts: raise ValueError('unmatched verdicts')
    counts['attempts'] = len(seen)
    return rows, dict(counts)


def write_deadline(fd, data, timeout):
    deadline = time.monotonic() + timeout
    while data:
        remaining = deadline - time.monotonic()
        if remaining <= 0 or not select.select([], [fd], [], max(0, remaining))[1]:
            raise TimeoutError('Cedar server did not read its input')
        try:
            written = os.write(fd, data)
        except BlockingIOError:
            continue
        data = data[written:]


def replay(binary, rows, output, timeout=30):
    """One isolated server/profile. Every request has exactly one response."""
    output.mkdir(parents=True, exist_ok=False)
    pipes = output / 'pipes'
    env = {**os.environ, 'LLVM_PROFILE_FILE': str(output / 'profile-%p.profraw')}
    started = time.monotonic()
    with (output / 'server.log').open('w') as log:
        process = subprocess.Popen([str(binary), str(pipes)], stdout=log, stderr=subprocess.STDOUT, env=env)
        infd = outfd = None
        try:
            deadline = time.monotonic() + timeout
            while not (pipes / 'output').exists():
                if process.poll() is not None or time.monotonic() > deadline: raise RuntimeError('server did not start')
                time.sleep(.01)
            # RDWR avoids FIFO-open deadlocks. Reads are individually timed.
            infd = os.open(pipes / 'input', os.O_RDWR | os.O_NONBLOCK)
            outfd = os.open(pipes / 'output', os.O_RDWR | os.O_NONBLOCK)
            buffered = b''
            with (output / 'outcomes.jsonl').open('w') as outcomes:
                for row in rows:
                    data = (row['payload'] + '\n').encode()
                    write_deadline(infd, data, timeout)
                    deadline = time.monotonic() + timeout
                    while b'\n' not in buffered:
                        remaining = deadline - time.monotonic()
                        if remaining <= 0 or not select.select([outfd], [], [], max(0, remaining))[0]:
                            raise TimeoutError(f'no Cedar response for {row["id"]}')
                        buffered += os.read(outfd, 65536)
                    line, buffered = buffered.split(b'\n', 1)
                    response = line.decode()
                    outcomes.write(json.dumps({'id': row['id'], 'attempt': row['attempt'],
                        'input_sha256': hashlib.sha256(row['input_coq'].encode()).hexdigest(),
                        'payload_sha256': hashlib.sha256(row['payload'].encode()).hexdigest(),
                        'response': response}) + '\n')
            if buffered: raise RuntimeError('unexpected extra response')
        finally:
            if infd is not None: os.close(infd)
            if outfd is not None: os.close(outfd)
            if process.poll() is None: process.send_signal(signal.SIGINT)
            try: process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill(); process.wait(); raise
        if process.returncode != 0: raise RuntimeError(f'server exit {process.returncode}')
    return time.monotonic() - started


def verify_serialization(rows, output):
    """Compile concrete equalities against verbatim upstream printer functions."""
    output.mkdir(parents=True, exist_ok=False)
    cedar = (ROOT / 'specification/cedar/upstream/Cedar.v.txt').read_text()
    generator = (ROOT / 'properties/cedar_no_type_error/upstream/CedarWellTypedTermGenerator.v.txt').read_text()
    def between(text, first, last):
        return text[text.index(first):text.index(last, text.index(first))]
    pieces = [
        between(cedar, 'Fixpoint stringOfEntityName ', '(* Custom show instances removed'),
        between(cedar, 'Definition ascii_between ', '(* Custom ShowCedarExpr removed'),
        between(cedar, 'Definition stringOfEntityNameFull ', 'Fixpoint stringOfSchemaEts'),
        between(generator, 'Fixpoint typeToSchemaStr ', '(* Pull the context info'),
    ]
    # The third region also contains unrelated instances in some artifact versions;
    # stop immediately after the name-list printer's terminating end.
    p = pieces[2]
    end = p.index('  end.', p.index('Fixpoint stringOfEntityNameList')) + len('  end.')
    pieces[2] = p[:end]
    prelude = '''From QuickChick Require Import QuickChick.
Require Import String Ascii List ZArith Specification.cedar.Spec Property.Original.
Import ListNotations.
Open Scope string_scope.
'''
    body = '''
Definition wire_input (i : Original.Input) : string :=
  match Original.e i with
  | MkEnvironment _ (MkRequest p a r _) =>
    schemaToStr (MkSchema (Original.ets i) (Original.acts i)) ++ "|||" ++
    stringOfEntityNameFull p ++ "::""e1""|||" ++ actionUIDToCedarStr a ++ "|||" ++
    stringOfEntityNameFull r ++ "::""e2""|||" ++ stringOfExpr (fst (Original.expr i))
  end.
'''
    for i, row in enumerate(rows):
        expected = row['payload'].replace('"', '""')
        body += f'Example sample_{i} : wire_input ({row["input_coq"]}) = "{expected}".\nProof. vm_compute. reflexivity. Qed.\n'
    (output / 'Oracle.v').write_text(prelude + '\n'.join(pieces) + body)
    (output / 'sources.json').write_text(json.dumps({
        'printer_fragments_sha256': [hashlib.sha256(p.encode()).hexdigest() for p in pieces],
        'inputs': [row['id'] for row in rows], 'count': len(rows)}, indent=2))
    shutil.copyfile(ROOT / 'specification/cedar/Spec.v', output / 'Spec.v')
    shutil.copyfile(ROOT / 'properties/cedar_no_type_error/Original.v', output / 'Original.v')
    # Distinct physical roots preserve the exact logical module identities.
    (output / 'spec').mkdir(); (output / 'property').mkdir()
    (output / 'Spec.v').rename(output / 'spec/Spec.v')
    (output / 'Original.v').rename(output / 'property/Original.v')
    flags = ['-q', '-R', 'spec', 'Specification.cedar', '-R', 'property', 'Property']
    with (output / 'coqc.log').open('w') as log:
        for source in ('spec/Spec.v', 'property/Original.v', 'Oracle.v'):
            subprocess.run(['bash', str(ROOT / 'environment/env.sh'), 'coqc', *flags, source],
                           cwd=output, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=600)
        subprocess.run(['bash', str(ROOT / 'environment/env.sh'), 'coqchk', '-silent',
                        '-R', 'spec', 'Specification.cedar', '-R', 'property', 'Property', 'Oracle'],
                       cwd=output, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=600)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def coverage(binary, directory, llvm):
    profiles = sorted(directory.glob('*.profraw'))
    if len(profiles) != 1: raise ValueError('expected one isolated server profile')
    merged = directory / 'coverage.profdata'
    subprocess.run([str(llvm / 'llvm-profdata'), 'merge', '-sparse', str(profiles[0]), '-o', str(merged)], check=True)
    with (directory / 'coverage.json').open('w') as out:
        subprocess.run([str(llvm / 'llvm-cov'), 'export', str(binary), '-instr-profile=' + str(merged)],
                       stdout=out, check=True)
    groups = branch_sets(json.loads((directory / 'coverage.json').read_text()))
    if any(not g['total'] for g in groups.values()): raise ValueError('missing Cedar branch instrumentation')
    (directory / 'branches.json').write_text(json.dumps({k: {s: sorted(v) for s, v in g.items()}
                                                       for k, g in groups.items()}))
    return groups


def select_groups(summary, mode):
    """Use one seed split consistently; intermediate versions have no held-out batches."""
    if mode == 'all-versions':
        groups = [('P0', 'P0', summary['baseline'])]
        for run, result in sorted(summary['runs'].items()):
            groups.extend((run, row['id'], row['measurement']) for row in result['adopted'])
        return groups, [101, 202, 303, 404, 505]
    if mode == 'final-heldout':
        return [('P0', 'P0', summary['held_out_baseline'])] + [
            (run, result['last_candidate_id'], result['held_out']['measurement'])
            for run, result in sorted(summary['runs'].items())], [1101, 1202, 1303, 1404, 1505]
    raise ValueError('unknown measurement mode: ' + mode)


def run_experiment(source, output, workers=4, mode='final-heldout'):
    output = output.resolve()
    allowed = ROOT / 'properties/cedar_no_type_error/.runs'
    if not output.is_relative_to(allowed): raise ValueError('evidence must be property-local .runs')
    output.mkdir(parents=True, exist_ok=False)
    binary = ROOT / '_opam-testing-theorems/cedar-coverage-target/debug/cedar-server'
    toolchain = Path(subprocess.check_output(['bash', str(ROOT / 'environment/env.sh'),
                                             'cedar-rust', 'rustc', '--print', 'sysroot'], text=True).strip())
    llvm = toolchain / 'lib/rustlib/x86_64-unknown-linux-gnu/bin'
    artifact = ROOT / '_opam-testing-theorems/testing-theorems-artifact-context/cedar-server'
    summary = json.loads((source / 'summary.json').read_text())
    selected, seeds = select_groups(summary, mode)
    manifest = {'source': str(source), 'binary_sha256': sha(binary),
        'cargo_lock_sha256': sha(artifact / 'Cargo.lock'), 'server_source_sha256': sha(artifact / 'src/main.rs'),
        'adapter_sha256': sha(Path(__file__)), 'environment_sha256': sha(ROOT / 'environment/env.sh'),
        'rustc': subprocess.check_output([str(toolchain / 'bin/rustc'), '-Vv'], text=True),
        'llvm_cov': subprocess.check_output([str(llvm / 'llvm-cov'), '--version'], text=True),
        'flags': '-C instrument-coverage -Z coverage-options=branch -C debuginfo=2',
        'mode': mode, 'seeds': seeds, 'source_summary_sha256': sha(source / 'summary.json'),
        'selection': 'confirmed-valid, original order, duplicates retained',
        'budget': '10000 original outer attempts; additionally globally matched valid count',
        'cohorts': {}, 'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}
    snapshots = output / 'execution-sources'
    snapshots.mkdir()
    shutil.copyfile(__file__, snapshots / 'rust_replay.py')
    shutil.copyfile(ROOT / 'environment/env.sh', snapshots / 'env.sh')
    batches, oracle, seen_constructors = {}, [], set()
    for run, candidate, reference in selected:
        base = source / 'baseline-property/.runs' if run == 'P0' else source / run / 'staged-property/.runs'
        for seed in manifest['seeds']:
            batch = base / f'benchmark-{candidate}-{seed}'
            rows, counts = read_batch(batch)
            expected = reference['per_seed'][str(seed)]
            assert counts['attempts'] == 10000
            assert len(rows) == expected['confirmed_valid']
            assert counts.get('unknown', 0) == expected['undetermined']
            assert counts.get('invalid', 0) == expected['confirmed_invalid']
            assert counts.get('no_result', 0) == expected['no_result']
            key = f'{run}-{candidate}-{seed}'
            manifest['cohorts'][key] = {'counts': counts, 'candidate': candidate,
                'run': run, 'seed': seed, 'batch': str(batch),
                'attempts_sha256': sha(batch / 'attempts.jsonl'), 'verdicts_sha256': sha(batch / 'verdicts.jsonl'),
                'distinct_inputs': len({r['input_coq'] for r in rows}),
                'distinct_payloads': len({r['payload'] for r in rows})}
            batches[key] = rows
            with (output / f'{key}-inputs.jsonl').open('w') as f:
                for r in rows: f.write(json.dumps(r) + '\n')
            for n, r in enumerate(rows):
                constructors = set(re.findall(r'\b[A-Za-z_][\w.]*', r['input_coq'])) & ARITY.keys()
                if n < 10 or constructors - seen_constructors:
                    oracle.append(r); seen_constructors |= constructors
            print('prepared', key, counts, flush=True)
    matched = min(map(len, batches.values()))
    manifest['matched_valid_inputs'] = matched
    manifest['oracle_samples'] = len(oracle)
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2))
    verify_serialization(oracle, output / 'serializer-oracle')
    print('Coq serializer cross-check passed:', len(oracle), flush=True)
    # Startup must not contribute Cedar branches to the experimental comparison.
    replay(binary, [], output / 'empty-control')
    empty = coverage(binary, output / 'empty-control', llvm)
    assert all(not g['covered'] for g in empty.values()), 'Cedar coverage during startup'
    results = {}
    def measure(key, rows, budget):
        directory = output / budget / key
        seconds = replay(binary, rows, directory)
        groups = coverage(binary, directory, llvm)
        responses = Counter(json.loads(line)['response'] for line in (directory / 'outcomes.jsonl').read_text().splitlines())
        result = {'inputs': len(rows), 'seconds': seconds, 'responses': dict(responses),
            'coverage': {g: {'covered': len(v['covered']), 'total': len(v['total']),
                            'percent': 100 * len(v['covered']) / len(v['total'])} for g, v in groups.items()}}
        return key, budget, result
    with ThreadPoolExecutor(max_workers=workers) as pool:
        jobs = [pool.submit(measure, key, rows if budget == 'outer-10000' else rows[:matched], budget)
                for budget in ['outer-10000', 'equal-valid'] for key, rows in batches.items()]
        for job in as_completed(jobs):
            key, budget, result = job.result()
            results.setdefault(budget, {})[key] = result
            (output / 'results.json').write_text(json.dumps(results, indent=2))
            print('measured', budget, key, result['coverage'], result['responses'], flush=True)
    # All coverage denominators must refer to the same binary/source locations.
    for budget in results:
        for key in results[budget]:
            sets = json.loads((output / budget / key / 'branches.json').read_text())
            for group in empty:
                assert set(map(tuple, sets[group]['total'])) == empty[group]['total']
    if sha(binary) != manifest['binary_sha256']:
        raise ValueError('instrumented binary changed during experiment')
    (output / 'completion.json').write_text(json.dumps({'status': 'completed',
        'finished_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}, indent=2))
    return results


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--mode', choices=['final-heldout', 'all-versions'], default='final-heldout')
    args = parser.parse_args()
    run_experiment(args.source.resolve(), args.output, args.workers, args.mode)
