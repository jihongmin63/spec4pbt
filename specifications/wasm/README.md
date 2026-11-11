# Wasm specification experiment

This branch imports the complete `spec-wasm/` directory from
[kaist-plrg/wasm-ntt, branch `wantt`](https://github.com/kaist-plrg/wasm-ntt/tree/4773b2b7abe56e61f279ec2340ac0d3c836b5033/spec-wasm)
at revision `4773b2b7abe56e61f279ec2340ac0d3c836b5033`.
The 18 `.watsup` files in `spec/` are unchanged upstream source.

`upstream.json` records provenance, `LICENSE` is the upstream root license,
and `SHA256SUMS` covers the imported specification and license. Verify with:

```sh
(cd specifications/wasm && sha256sum --check SHA256SUMS)
```

The `wasm-spec-experiments` branch removes the authored P4 properties.
The pinned P4-SpecTec submodule remains the frontend/toolchain dependency.
Existing ignored bundles and saved execution evidence are retained.

`observations.toml` permits two external relations, `Module_ok` (validation)
and `Module_init_ok` (instantiation with no imports, including the start
function), both with `observe = []`. They are bound to Wasmtime 50.0.1
(`implementations/wasmtime.toml`) and Node.js 26.13.0 / V8 14.6
(`implementations/node.toml`) through `implementations/wasm_adapter.py`,
which encodes the module AST with `implementations/wasm_encoder.py`. The
encoder, engine-specific implementation limits, and resource exhaustion form
the trusted boundary: unencodable modules, modules beyond a limit, stack or
allocation exhaustion, and timeouts are adapter aborts, not verdicts. Importing
this specification does not establish certified Wasm execution; a property
still needs its own proof, generator, and check before `run`.
