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

No Wasm property, observation catalog, implementation adapter, proof, generator,
or certificate has been added. Implementation selection and relation analysis
are the next experiment steps. Importing this specification does not establish
translation support or certified Wasm execution.
