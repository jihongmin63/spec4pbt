// V8 driver for implementations/wasm_adapter.py.
// Reads one Wasm binary from stdin and prints one JSON report:
//   {"ok": true}
//   {"ok": false, "stage": "compile" | "instantiate", "class": <error constructor>,
//    "wasm_exception": <is WebAssembly.Exception>, "message": <text>}
// Mode "validate" uses WebAssembly.validate and fetches the CompileError text
// only to report it; mode "instantiate" compiles and instantiates with no imports.
import { readFileSync } from 'node:fs';

const mode = process.argv[2];
const bytes = readFileSync(0);

function failure(stage, error) {
  return {
    ok: false,
    stage,
    class: error?.constructor?.name ?? typeof error,
    wasm_exception: error instanceof WebAssembly.Exception,
    message: String(error?.message ?? error),
  };
}

let report;
if (mode === 'validate') {
  if (WebAssembly.validate(bytes)) {
    report = { ok: true };
  } else {
    try {
      new WebAssembly.Module(bytes);
      report = { ok: false, stage: 'compile', class: 'CompileError', wasm_exception: false,
                 message: 'WebAssembly.validate returned false' };
    } catch (error) {
      report = failure('compile', error);
    }
  }
} else if (mode === 'instantiate') {
  let module;
  try {
    module = new WebAssembly.Module(bytes);
  } catch (error) {
    report = failure('compile', error);
  }
  if (!report) {
    try {
      new WebAssembly.Instance(module, {});
      report = { ok: true };
    } catch (error) {
      report = failure('instantiate', error);
    }
  }
} else {
  process.stderr.write(`unknown mode ${mode}\n`);
  process.exit(2);
}
process.stdout.write(JSON.stringify(report) + '\n');
