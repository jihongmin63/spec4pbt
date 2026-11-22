#!/usr/bin/env python3
"""Exercise complete builtin dispatch against actual frontend AL signatures."""
from pathlib import Path
import json
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[4]

def main():
    run = Path(tempfile.mkdtemp(prefix='p4-mapping.', dir=ROOT / '_opam-testing-theorems' / 'checks'))
    source = run / 'source'
    shutil.copytree(ROOT / '_opam-testing-theorems/sources/p4-spectec', source,
                    ignore=shutil.ignore_patterns('.git', '_build'))
    harness = source / 'p4spec/p4_mapping_test'
    shutil.copytree(ROOT / 'translator/src', harness)
    shutil.copy2(Path(__file__).with_name('mapping_test.ml'), harness / 'mapping_test.ml')
    (harness / 'dune').write_text('(executable (name mapping_test) (modules mapping_test context coq_ir data emit_data casts render lower_expr wasm_bindings builtins) (libraries pass lang domain util diagnostic yojson unix))\n')
    command = ['bash', str(ROOT / 'environment/env.sh'), 'frontend', 'dune', 'exec',
               '--root', str(source), 'p4spec/p4_mapping_test/mapping_test.exe', '--',
               str(Path(__file__).with_name('mapping.watsup')), str(run)]
    result = subprocess.run(command, cwd=source, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (run / 'mapping.log').write_text(result.stdout)
    report = {'command': command, 'returncode': result.returncode, 'coq_commands': []}
    print(f'mapping evidence: {run}', flush=True)
    print(result.stdout[-20000:], flush=True)
    if result.returncode:
        (run / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        return result.returncode
    (run / 'Builtins').mkdir()
    for relative in ['Execution.v', 'Values.v', 'Builtins/Common.v', 'Builtins/P4.v']:
        shutil.copy2(ROOT / 'translator/coq' / relative, run / relative)
    for relative in ['Execution.v', 'Values.v', 'Builtins/Common.v', 'Builtins/P4.v', 'Types_0000.v', 'BuiltinMapping.v']:
        command = ['bash', str(ROOT / 'environment/env.sh'), 'coqc', '-q', '-Q', str(run), 'ALCoq', relative]
        result = subprocess.run(command, cwd=run, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (run / (Path(relative).stem + '.log')).write_text(result.stdout)
        report['coq_commands'].append({'command': command, 'returncode': result.returncode})
        print(f'{relative}: exit {result.returncode}', flush=True)
        if result.returncode:
            print(result.stdout, flush=True)
            break
    (run / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return result.returncode

if __name__ == '__main__':
    raise SystemExit(main())
