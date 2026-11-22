#!/usr/bin/env python3
"""Build typed cast regressions in a fresh ignored pinned-frontend copy.

--full additionally inventories and compiles helpers for every actual AL cast
and RecurseSC occurrence in both complete specifications. This checks generated
Coq and concrete examples; it is not a semantic preservation proof.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--full', action='store_true')
    args = parser.parse_args()
    state = ROOT / '_opam-testing-theorems'
    (state / 'checks').mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix='casts.', dir=state / 'checks'))
    report = {'started': datetime.now(timezone.utc).isoformat(), 'commands': [],
              'status': 'failed', 'run': str(run), 'profiles': {}}

    def execute(command, cwd, log):
        result = subprocess.run(list(map(str, command)), cwd=cwd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        log.write_text(result.stdout)
        report['commands'].append({'argv': list(map(str, command)), 'cwd': str(cwd),
                                   'log': str(log), 'returncode': result.returncode})
        if result.returncode:
            raise RuntimeError(f'{log}:\n{result.stdout[-6000:]}')

    try:
        profile = json.loads((ROOT / 'translator/profiles/p4.json').read_text())
        archive = ROOT / profile['frontend']['archive']
        assert hashlib.sha256(archive.read_bytes()).hexdigest() == profile['frontend']['archive_sha256']
        build = Path(tempfile.mkdtemp(prefix='task4-casts.', dir=state / 'build')) / 'source'
        shutil.copytree(ROOT / profile['frontend']['source_root'], build,
                        ignore=shutil.ignore_patterns('_build', '_opam', '.git'))
        backend = build / 'p4spec/cast_tests'
        backend.mkdir()
        for name in ['context.ml', 'coq_ir.ml', 'data.ml', 'emit_data.ml', 'casts.ml']:
            shutil.copy2(ROOT / 'translator/src' / name, backend / name)
        shutil.copy2(HERE / 'casts_driver.ml', backend / 'cast_driver.ml')
        (backend / 'dune').write_text('(executable (name cast_driver) '
            '(modules cast_driver context coq_ir data emit_data casts) '
            '(libraries pass lang domain util diagnostic yojson unix))\n')
        env = ['bash', ROOT / 'environment/env.sh']
        execute(env + ['frontend', 'dune', 'build', '--root', build, '-j', '2',
                       'p4spec/cast_tests/cast_driver.exe'], ROOT, run / 'build.log')
        executable = build / '_build/default/p4spec/cast_tests/cast_driver.exe'
        for name in ['fixture'] + (['p4', 'wasm'] if args.full else []):
            target = run / name
            target.mkdir()
            if name == 'fixture':
                inputs = [HERE / 'casts.watsup']
            else:
                profile = json.loads((ROOT / f'translator/profiles/{name}.json').read_text())
                inputs = [ROOT / entry['path'] for entry in profile['inputs']]
                for entry, path in zip(profile['inputs'], inputs):
                    assert hashlib.sha256(path.read_bytes()).hexdigest() == entry['sha256']
            execute(env + ['frontend', executable, name, target] + inputs, ROOT, target / 'frontend.log')
            report['profiles'][name] = json.loads((target / 'casts.json').read_text())
            support = run / f'{name}-support'
            support.mkdir()
            shutil.copy2(ROOT / 'translator/coq/Values.v', support / 'Values.v')
            paths = [support / 'Values.v', target / 'Types.v', target / 'Casts.v']
            if name == 'fixture':
                shutil.copy2(HERE / 'casts_checks.v', target / 'Checks.v')
                paths.append(target / 'Checks.v')
            for path in paths:
                execute(env + ['coqc', '-q', '-Q', support, 'ALCoq', '-Q', target, '', path],
                        run, target / f'{path.stem}.log')
        report['status'] = 'passed'
    finally:
        (run / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(f'casts evidence: {run}', flush=True)


if __name__ == '__main__':
    main()
