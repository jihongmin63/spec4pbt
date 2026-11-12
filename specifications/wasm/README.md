# Wasm specification

The shared foundation imports the complete `spec-wasm/` directory from
[kaist-plrg/wasm-ntt, branch `wantt`](https://github.com/kaist-plrg/wasm-ntt/tree/4773b2b7abe56e61f279ec2340ac0d3c836b5033/spec-wasm)
at revision `4773b2b7abe56e61f279ec2340ac0d3c836b5033`.
The 18 `.watsup` files in `spec/` are unchanged upstream source.

`upstream.json` records provenance, `LICENSE` is the upstream root license,
and `SHA256SUMS` covers the imported specification and license. Verify with:

```sh
(cd specifications/wasm && sha256sum --check SHA256SUMS)
```

The pinned P4-SpecTec submodule remains the frontend/toolchain dependency.
Wasm integration patches apply only to the copied build; their scope and sources
are recorded in [translator provenance](../../translator/PROVENANCE.md).

`observations.toml` permits two external relations, `Module_ok` (validation)
and `Module_init_ok` (instantiation), both with `observe = []`. Listing a relation
does not select it for every property or bind it to an implementation.
Authored properties, generators, engine adapters, and their execution conditions
belong to `pbt-experiments`. Importing this specification does not establish
certified Wasm execution; each property still needs its own proof, generator,
and check before `run`.
