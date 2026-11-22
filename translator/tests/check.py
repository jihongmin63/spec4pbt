#!/usr/bin/env python3
"""Compile permanent AL-to-Coq suites and complete specifications in ignored runs."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]

def runtime() -> None:
    base = ROOT / '_opam-testing-theorems' / 'checks'
    base.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix='runtime.', dir=base))
    sources = sorted((ROOT / 'translator' / 'tests' / 'runtime').glob('*.v'))
    runtime_source = ROOT / 'translator' / 'coq' / 'Execution.v'
    paths = [runtime_source, ROOT / 'translator' / 'coq' / 'Values.v', *sources]
    report = {'suite': 'runtime', 'started': datetime.now(timezone.utc).isoformat(),
              'run': str(run), 'commands': [], 'status': 'failed'}
    try:
        for src in paths:
            shutil.copy2(src, run / src.name)
            command = ['bash', str(ROOT / 'environment' / 'env.sh'), 'coqc',
                       '-q', '-Q', str(run), 'ALCoq', src.name]
            record = {'command': command, 'source': str(src.relative_to(ROOT))}
            report['commands'].append(record)
            result = subprocess.run(command, cwd=run, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True)
            (run / f'{src.stem}.log').write_text(result.stdout)
            record['returncode'] = result.returncode
            if result.returncode:
                raise RuntimeError(f'{src.name}: exit {result.returncode}\n{result.stdout[-8000:]}')
        report['status'] = 'passed'
    finally:
        (run / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(f'runtime evidence: {run}', flush=True)

class SuiteRun:
    def __init__(self, name):
        base = ROOT / '_opam-testing-theorems/checks'
        base.mkdir(parents=True, exist_ok=True)
        self.path = Path(tempfile.mkdtemp(prefix=name + '.', dir=base))
        self.report = {'suite': name, 'run': str(self.path), 'started': datetime.now(timezone.utc).isoformat(),
                       'status': 'failed', 'commands': []}

    def execute(self, command, log_name, cwd=ROOT):
        command = list(map(str, command))
        log = self.path / log_name
        log.parent.mkdir(parents=True, exist_ok=True)
        record = {'argv': command, 'cwd': str(cwd), 'log': str(log)}
        self.report['commands'].append(record)
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
        record['returncode'] = result.returncode
        if result.returncode:
            raise RuntimeError(f'{self.report["suite"]}: exit {result.returncode}; {log}\n{log.read_text()[-6000:]}')
        return log

    def close(self):
        (self.path / 'report.json').write_text(json.dumps(self.report, indent=2) + '\n')
        print(f'{self.report["suite"]} evidence: {self.path}', flush=True)


def load_module(name, path):
    import importlib.util
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def backend_source(backend):
    state = ROOT / '_opam-testing-theorems'
    for candidate in backend.parents:
        if candidate.is_relative_to(state / 'build') and (candidate / 'dune-project').is_file():
            return candidate
    raise ValueError('backend must belong to a prepared target-local frontend build')


def prepare_backend(run, supplied=None):
    """Build only a new private copy; never mutate an active cached build."""
    import hashlib
    import tarfile
    driver = load_module('suite_translate_driver', ROOT / 'scripts/translate.py')
    profile = json.loads((ROOT / 'translator/profiles/p4.json').read_text())
    archive = driver.owned_path(ROOT, profile['frontend']['archive'])
    if hashlib.sha256(archive.read_bytes()).hexdigest() != profile['frontend']['archive_sha256']:
        raise ValueError('frontend archive SHA-256 mismatch')
    if supplied is None:
        source = driver.owned_path(ROOT, profile['frontend']['source_root'])
    else:
        backend = supplied.resolve()
        if not backend.is_file() or not backend.is_relative_to(ROOT / '_opam-testing-theorems'):
            raise ValueError('--backend must point to an executable under target _opam-testing-theorems')
        source = backend_source(backend)
    with tarfile.open(archive) as tar:
        for member in tar.getmembers():
            if member.isfile():
                candidate = driver.owned_path(source, member.name)
                if candidate.read_bytes() != tar.extractfile(member).read():
                    raise ValueError(f'frontend differs from pinned source: {member.name}')
    if supplied is None:
        source, _ = driver.prepare_backend(source, run.path)
        run.execute(['bash', ROOT / 'environment/env.sh', 'frontend', 'dune', 'build',
                     '--root', source, '-j', '2', 'p4spec/al_to_coq/main.exe'], 'backend-build.log')
        backend = source / '_build/default/p4spec/al_to_coq/main.exe'
    run.report['backend'] = {'path': str(backend), 'sha256': hashlib.sha256(backend.read_bytes()).hexdigest(),
                             'source_build': str(source), 'provided': supplied is not None,
                             'sources': {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                                         for path in sorted((source / 'p4spec/al_to_coq').iterdir())
                                         if path.suffix == '.ml' or path.name == 'dune'}}
    return backend, source


def frontend(backend=None):
    run = SuiteRun('frontend')
    try:
        executable, _ = prepare_backend(run, backend)
        driver = load_module('frontend_translate_driver', ROOT / 'scripts/translate.py')
        run.execute(['python3', '-B', ROOT / 'translator/tests/frontend/test_driver.py'], 'driver-tests.log')
        run.execute(['python3', '-B', ROOT / 'translator/tests/frontend/run.py', '--backend', executable,
                     '--run-dir', run.path / 'fixture'], 'fixture.log')
        run.report['profiles'] = {}
        for name in ['p4', 'wasm']:
            profile = json.loads((ROOT / f'translator/profiles/{name}.json').read_text())
            paths = driver.verify_inputs(ROOT, profile)
            target = run.path / name
            target.mkdir()
            command = ['bash', ROOT / 'environment/env.sh', 'frontend', executable, '--profile', name,
                       '--output', target, '--manifest', target / 'manifest.json', '--inventory']
            for path in paths:
                command += ['--input', path]
            run.execute(command, f'{name}/frontend.log')
            inventory = json.loads((target / 'inventory.json').read_text())
            manifest = json.loads((target / 'manifest.json').read_text())
            assert manifest['status'] == 'inventory-complete'
            assert inventory['translation_complete'] is False
            assert len(inventory['declarations']) == inventory['declaration_count']
            assert inventory['construct_counts']['BuiltinDecD'] == (47 if name == 'p4' else 76)
            assert inventory['consumed_metadata_count'] == inventory['construct_counts']['VarD']
            assert inventory['raw_al_declaration_count'] + len(inventory['normalizations']) == inventory['declaration_count']
            if name == 'wasm':
                restored = {entry['source_name']: entry for entry in inventory['normalizations']}
                assert restored['ftestop']['representation'] == 'TypD(VariantT[])'
            run.report['profiles'][name] = {'input_count': len(paths), 'source_declaration_count': inventory['source_declaration_count'],
                'raw_al_declaration_count': inventory['raw_al_declaration_count'], 'al_declaration_count': inventory['declaration_count'],
                'normalizations': inventory['normalizations'], 'evidence': str(target)}
        run.report['status'] = 'passed'
    finally:
        run.close()
    return run.path


def fixture_suite(name, backend=None):
    run = SuiteRun(name)
    try:
        executable, _ = prepare_backend(run, backend)
        if name == 'expressions':
            run.execute(['python3', '-B', ROOT / 'translator/tests/expressions/casts_run.py', '--full'], 'casts.log')
        run.execute(['python3', '-B', ROOT / 'translator/tests/lowering/run.py', '--suite', name,
                     '--backend', executable, '--run-dir', run.path / 'fixtures'], 'fixtures.log')
        fixture_report = json.loads((run.path / 'fixtures/report.json').read_text())
        assert fixture_report['status'] == 'passed' and fixture_report['coq_compiled'] is True
        run.report['fixture_report'] = str(run.path / 'fixtures/report.json')
        run.report['status'] = 'passed'
    finally:
        run.close()
    return run.path


def builtin_p4():
    run = SuiteRun('builtin-p4')
    try:
        # Both scripts build their own fresh source copies. Mapping compiles all
        # native declarations against actual AL signatures; native exercises the
        # unmodified pinned implementation rather than a recreated oracle.
        for name in ['native', 'mapping']:
            run.execute(['python3', '-B', ROOT / f'translator/tests/builtins/p4/{name}.py'], name + '.log')
        support = run.path / 'support'
        (support / 'Builtins').mkdir(parents=True)
        paths = ['Execution.v', 'Values.v', 'Builtins/Common.v', 'Builtins/P4.v']
        for relative in paths:
            shutil.copy2(ROOT / 'translator/coq' / relative, support / relative)
        shutil.copy2(ROOT / 'translator/tests/builtins/p4/P4Builtins.v', support / 'P4Builtins.v')
        for index, relative in enumerate(paths + ['P4Builtins.v']):
            run.execute(['bash', ROOT / 'environment/env.sh', 'coqc', '-q', '-Q', support, 'ALCoq', support / relative],
                        f'coq/{index:02d}-{Path(relative).stem}.log', cwd=run.path)
        run.report['status'] = 'passed'
    finally:
        run.close()
    return run.path


def builtin_wasm(backend=None):
    run = SuiteRun('builtin-wasm')
    try:
        _, source = prepare_backend(run, backend)
        run.execute(['python3', '-B', ROOT / 'translator/tests/builtins/wasm/run.py',
                     '--run-dir', run.path / 'numeric'], 'numeric.log')
        run.execute(['python3', '-B', ROOT / 'translator/tests/builtins/wasm/wrappers.py',
                     '--frontend-build', source, '--run-dir', run.path / 'wrappers'], 'wrappers.log')
        for name in ['numeric', 'wrappers']:
            report = json.loads((run.path / name / 'report.json').read_text())
            assert report['status'] == 'passed'
        run.report['status'] = 'passed'
    finally:
        run.close()
    return run.path


def inductive(backend=None):
    run = SuiteRun('inductive')
    try:
        executable, _ = prepare_backend(run, backend)
        run.execute(['env', f'INDUCTIVE_BACKEND={executable}', 'python3', '-B',
                     ROOT / 'translator/tests/inductive/test_inductive.py'],
                    'inductive.log')
        run.report['status'] = 'passed'
    finally:
        run.close()
    return run.path


def all_suites(backend=None):
    run = SuiteRun('all')
    try:
        executable, _ = prepare_backend(run, backend)
        names = ['runtime', 'frontend', 'data', 'expressions', 'lowering', 'inductive', 'builtin-p4', 'builtin-wasm']
        for name in names:
            command = ['python3', '-B', ROOT / 'translator/tests/check.py', '--suite', name]
            if name not in ['runtime', 'builtin-p4']:
                command += ['--backend', executable]
            run.execute(command, f'suites/{name}.log')
        checked = {}
        for name in ['p4', 'wasm']:
            log = run.execute(['python3', '-B', ROOT / 'scripts/translate.py', '--profile', name, '--check'], f'full/{name}.log')
            prefix = 'Coq source evidence: '
            results = [line[len(prefix):] for line in log.read_text().splitlines() if line.startswith(prefix)]
            if not results:
                raise RuntimeError(f'{name}: translation driver did not report generated source evidence')
            source = Path(results[-1]).resolve()
            if not source.is_relative_to(ROOT / '_opam-testing-theorems'):
                raise ValueError(f'{name}: source evidence outside target state')
            manifest = json.loads((source.parent / 'manifest.json').read_text())
            if manifest.get('status') != 'checked' or manifest.get('coq_compiled') is not True:
                raise RuntimeError(f'{name}: full Coq translation/compilation did not complete')
            checked[name] = source
        run.report['full_specifications'] = {name: str(path) for name, path in checked.items()}
        both = run.path / 'BothSpecifications.v'
        both.write_text('From P4Spec Require Import Spec.\nFrom WasmSpec Require Import Spec.\n'
                        'Check P4Spec.Generated.Program.Body.\nCheck WasmSpec.Generated.Program.Body.\n')
        # Wasm's support directory includes both common/P4 and Wasm support.
        # Both profile compiles above must have succeeded before this import.
        support = checked['wasm'].parent / 'support'
        run.execute(['bash', ROOT / 'environment/env.sh', 'coqc', '-q', '-Q', support, 'ALCoq',
                     '-Q', checked['p4'], 'P4Spec', '-Q', checked['wasm'], 'WasmSpec', both], 'both-namespaces.log', cwd=run.path)
        run.report['both_namespaces_compiled'] = True
        run.report['status'] = 'passed'
    finally:
        run.close()
    return run.path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite', required=True, choices=['runtime', 'frontend', 'data', 'expressions', 'lowering', 'inductive', 'builtin-p4', 'builtin-wasm', 'all'])
    parser.add_argument('--backend', type=Path, help='use an existing target-local executable without changing its frontend build')
    args = parser.parse_args()
    if args.suite == 'runtime':
        runtime()
    elif args.suite == 'frontend':
        frontend(args.backend)
    elif args.suite in ['data', 'expressions', 'lowering']:
        fixture_suite(args.suite, args.backend)
    elif args.suite == 'builtin-p4':
        builtin_p4()
    elif args.suite == 'builtin-wasm':
        builtin_wasm(args.backend)
    elif args.suite == 'inductive':
        inductive(args.backend)
    else:
        all_suites(args.backend)


if __name__ == '__main__':
    main()
