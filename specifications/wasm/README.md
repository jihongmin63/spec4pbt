# Wasm specification reference for component planning

This branch imports the complete `spec-wasm/` directory from
[kaist-plrg/wasm-ntt, branch `wantt`](https://github.com/kaist-plrg/wasm-ntt/tree/4773b2b7abe56e61f279ec2340ac0d3c836b5033/spec-wasm)
at revision `4773b2b7abe56e61f279ec2340ac0d3c836b5033`.
The 18 `.watsup` files in `spec/` are unchanged upstream source.

These files were copied from repository commit
`33e314af20717d44709f5ad2c0862d057b` onto `plan-first` for the
`Module_ok` component plan. The P4 baseline sources and property examples
remain in place. `upstream.json` records provenance, `LICENSE` is the
upstream root license, and `SHA256SUMS` covers the imported specification
and license. Verify with:

```sh
(cd specifications/wasm && sha256sum --check SHA256SUMS)
```

The pinned P4-SpecTec submodule remains the frontend/toolchain dependency.
`PlanReference/Spec.lean` is a frozen generated semantics fixture from that
reference experiment; its source and limits are documented in
`docs/constructive-generator-lessons.md`. Importing this specification or
checking the component plan does not establish fresh full-Wasm translation,
generator certification, or external implementation execution.
