#!/usr/bin/env python3
"""Generate and compile permanent datatype, expression and lowering fixtures."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
STATE = ROOT / '_opam-testing-theorems'


def load_driver():
    spec = importlib.util.spec_from_file_location('al_translate_driver', ROOT / 'scripts/translate.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run(suite: str, backend: Path, run_dir: Path | None = None) -> Path:
    backend = backend.resolve()
    if not backend.is_relative_to(STATE) or not backend.is_file():
        raise ValueError('backend must be an executable in target _opam-testing-theorems')
    (STATE / 'checks').mkdir(parents=True, exist_ok=True)
    run_dir = run_dir.resolve() if run_dir else Path(tempfile.mkdtemp(prefix=suite + '.', dir=STATE / 'checks'))
    if not run_dir.is_relative_to(STATE):
        raise ValueError('run directory must be inside target _opam-testing-theorems')
    if run_dir.exists() and any(run_dir.iterdir()):
        raise ValueError('run directory must be new or empty; prior evidence is preserved')
    run_dir.mkdir(parents=True, exist_ok=True)
    report = {'suite': suite, 'status': 'failed', 'started': datetime.now(timezone.utc).isoformat(),
              'run': str(run_dir), 'backend': str(backend), 'backend_sha256': hashlib.sha256(backend.read_bytes()).hexdigest(),
              'commands': [], 'cases': {}, 'coq_compiled': False}
    driver = load_driver()

    def execute(command, log, cwd=run_dir):
        command = list(map(str, command))
        record = {'argv': command, 'cwd': str(cwd), 'log': str(log)}
        report['commands'].append(record)
        with log.open('w') as output:
            process = subprocess.run(command, cwd=cwd, stdout=output, stderr=subprocess.STDOUT)
        record['returncode'] = process.returncode
        if process.returncode:
            raise RuntimeError(f'{suite}: command failed ({process.returncode}): {log}\n{log.read_text()[-6000:]}')

    def case(name, profile, inputs, checks=None, *, data_only=False):
        target = run_dir / name
        target.mkdir()
        source = target / 'spec'
        source.mkdir()
        command = ['bash', ROOT / 'environment/env.sh', 'frontend', backend,
                   '--profile', profile, '--output', source, '--manifest', target / 'manifest.json']
        for path in inputs:
            command += ['--input', path]
        if data_only:
            command += ['--data-only']
        execute(command, target / 'generation.log')
        manifest = json.loads((target / 'manifest.json').read_text())
        expected = 'data-generated' if data_only else 'coq-generated'
        if name == 'fresh':
            inventory = json.loads((source / 'inventory.json').read_text())
            groups = [group for group in inventory['rule_groups'] if group['owner'] == 'Common']
            assert len(groups) == 1 and groups[0]['path_count'] == 2
            assert groups[0]['common_premise_count'] > 0
            assert any('fresh_typeId' in premise for premise in groups[0]['common_premises'])
        if manifest.get('status') != expected:
            raise RuntimeError(f'{name}: expected backend status {expected!r}, got {manifest.get("status")!r}')
        case_record = {'profile': profile, 'inputs': [{'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()} for path in inputs],
                       'status': 'failed', 'source': str(source), 'data_only': data_only}
        report['cases'][name] = case_record
        if data_only:
            support = target / 'support'
            support.mkdir()
            shutil.copy2(ROOT / 'translator/coq/Values.v', support / 'Values.v')
            namespace = 'DataFixture' if profile == 'fixture' else {'p4': 'P4Spec.Generated', 'wasm': 'WasmSpec.Generated'}[profile]
            coq = ['bash', ROOT / 'environment/env.sh', 'coqc', '-q', '-Q', support, 'ALCoq', '-Q', source, namespace]
            execute(coq + [support / 'Values.v'], target / 'Values.log')
            execute(coq + [source / 'Types_0000.v'], target / 'Types_0000.log')
        else:
            # This routine compiles every generated module in dependency order,
            # plus the profile's real builtin support; it never treats inventory
            # success as a compilation check.
            compiled = {'commands': []}
            try:
                driver.compile_generated(source, profile, target, compiled)
            finally:
                report['commands'].extend(compiled['commands'])
                case_record['coq_sources'] = compiled.get('coq_sources', [])
            support = target / 'support'
            namespace = {'p4': 'P4Spec', 'wasm': 'WasmSpec'}.get(profile, 'FixtureSpec')
            coq = ['bash', ROOT / 'environment/env.sh', 'coqc', '-q', '-Q', support, 'ALCoq', '-Q', source, namespace]
        if checks is not None:
            if not checks.is_file():
                raise FileNotFoundError(f'required permanent Coq fixture is missing: {checks}')
            destination = source / checks.name
            shutil.copy2(checks, destination)
            case_record['checks'] = {'path': str(checks), 'sha256': hashlib.sha256(checks.read_bytes()).hexdigest()}
            execute(coq + [destination], target / f'{checks.stem}.log')
        case_record['status'] = 'passed'

    try:
        tests = ROOT / 'translator/tests'
        if suite == 'data':
            case('representative', 'fixture', [tests / 'data/representative.watsup'], tests / 'data/RepresentativeChecks.v', data_only=True)
            for name in ['p4', 'wasm']:
                profile = json.loads((ROOT / f'translator/profiles/{name}.json').read_text())
                case(name, name, driver.verify_inputs(ROOT, profile), data_only=True)
        elif suite == 'expressions':
            case('operations', 'fixture', [tests / 'expressions/operations.watsup'], tests / 'expressions/OperationsChecks.v')
        elif suite == 'lowering':
            case('sequential', 'fixture', [tests / 'lowering/sequential.watsup'], tests / 'lowering/SequentialChecks.v')
            case('fresh', 'p4', [tests / 'lowering/fresh.watsup'], tests / 'lowering/FreshChecks.v')
        else:
            raise ValueError(f'unknown fixture suite: {suite}')
        report['coq_compiled'] = True
        report['status'] = 'passed'
    finally:
        (run_dir / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(f'{suite} fixture evidence: {run_dir}', flush=True)
    return run_dir


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite', required=True, choices=['data', 'expressions', 'lowering'])
    parser.add_argument('--backend', type=Path, required=True)
    parser.add_argument('--run-dir', type=Path)
    arguments = parser.parse_args()
    run(arguments.suite, arguments.backend, arguments.run_dir)
