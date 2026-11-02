# Original Wasm generator source snapshot

These six Lean files are byte-for-byte copies of the corresponding
`properties/wasm_module_ok/*.lean` files in commit
`33e314af20717d44709f5ad2c0862d6ec02d057b`. They are source references
for the static component mapping; they are not compiled here because the
original implementation has a much larger proof dependency closure. The
`implementation.sha256` fields in `component-plan.json` pin the four files
directly mapped to components. `implementation_refs` also pins the root
`Generator.generator` and `ConstructiveModuleGeneration.modules` definitions.
`ConstructiveTypes.lean` shows the type construction for source review.

To compare a file with the Git object:

```sh
git show 33e314af20717d44709f5ad2c0862d6ec02d057b:properties/wasm_module_ok/ConstructiveModuleGeneration.lean | sha256sum
sha256sum scripts/tests/fixtures/wasm_plan_reference/ConstructiveModuleGeneration.lean
```
