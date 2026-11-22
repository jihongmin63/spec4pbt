#!/usr/bin/env python3
"""Build untouched pinned P4 builtins in a fresh target-owned source copy."""
from pathlib import Path
import json
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[4]

def main():
    run = Path(tempfile.mkdtemp(prefix='p4-native.', dir=ROOT / '_opam-testing-theorems' / 'checks'))
    source = run / 'source'
    shutil.copytree(ROOT / '_opam-testing-theorems/sources/p4-spectec', source,
                    ignore=shutil.ignore_patterns('.git', '_build'))
    harness = source / 'p4spec/p4_builtin_test'
    harness.mkdir()
    shutil.copy2(Path(__file__).with_name('native.ml'), harness / 'native.ml')
    (harness / 'dune').write_text('(executable (name native) (libraries builtin interface lang runtime domain util bignum))\n')
    command = ['bash', str(ROOT / 'environment/env.sh'), 'frontend', 'dune', 'exec',
               '--root', str(source), 'p4spec/p4_builtin_test/native.exe']
    result = subprocess.run(command, cwd=source, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (run / 'native.log').write_text(result.stdout)
    (run / 'report.json').write_text(json.dumps({'command': command, 'returncode': result.returncode}, indent=2) + '\n')
    print(f'native evidence: {run}', flush=True)
    print(result.stdout[-10000:], flush=True)
    return result.returncode

if __name__ == '__main__':
    raise SystemExit(main())
