#!/usr/bin/env python3
"""Exercise actual pinned AL and donor byte functions at the OCaml int boundary."""
from pathlib import Path
import hashlib
import importlib.util
import json
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
TESTS = Path(__file__).resolve().parent

def main():
    run = Path(tempfile.mkdtemp(prefix='native-slices.', dir=ROOT / '_opam-testing-theorems/checks'))
    source = run / 'source'
    shutil.copytree(ROOT / '_opam-testing-theorems/sources/p4-spectec', source,
                    ignore=shutil.ignore_patterns('.git', '_build'))
    spec = importlib.util.spec_from_file_location('wasm_native', TESTS.parent / 'builtins/wasm/run.py')
    wasm = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(wasm)
    _, files = wasm.extract(run)  # Verifies every donor patch's SHA-256.
    harness = source / 'p4spec/slice_probe'
    harness.mkdir()
    shutil.copy2(TESTS / 'native_slices.ml', harness / 'native_slices.ml')
    (harness / 'value_array.ml').write_text(files['value_array.ml'])
    # Copy complete function definitions verbatim. Only namespacing/compatibility
    # setup is added; bounds arithmetic, exception paths and array code are native.
    nats = files['nats.ml']
    functions = nats[nats.index('let slice_bytes '):nats.index('\nlet ', nats.index('let replace_bytes ') + 4)]
    header = '''open Lang
open Xl
open Il
open Util.Source
module Extract = Builtin.Extract
open Builtin.Error
module Value = struct
  include Runtime.Value
  let get_list_array = Get.list
  let make typ value = Make.mk no_region typ value
end
let bigint_of_value value = value |> Value.Get.num |> Num.to_int
'''
    (harness / 'native_bytes.ml').write_text(header + functions)
    (harness / 'dune').write_text('(executable (name native_slices) (libraries pass lang domain util runtime interface interp_al builtin))\n')
    command = ['bash', str(ROOT / 'environment/env.sh'), 'frontend', 'dune', 'exec',
               '--root', str(source), '-j', '2', 'p4spec/slice_probe/native_slices.exe', '--',
               str(TESTS / 'native_slices.watsup')]
    result = subprocess.run(command, cwd=source, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (run / 'native.log').write_text(result.stdout)
    (run / 'report.json').write_text(json.dumps({'command': command, 'returncode': result.returncode,
        'status': 'passed' if result.returncode == 0 else 'failed',
        'byte_function_sha256': hashlib.sha256(functions.encode()).hexdigest(),
        'value_array_sha256': hashlib.sha256(files['value_array.ml'].encode()).hexdigest()}, indent=2) + '\n')
    print(f'native slice evidence: {run}', flush=True)
    print(result.stdout[-5000:], flush=True)
    return result.returncode

if __name__ == '__main__':
    raise SystemExit(main())
