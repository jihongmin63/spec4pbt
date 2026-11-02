# Generator component plans

## Contract and connection

A component has four semantic fields: `input`, `output`, `require`, and
`ensure`. Inputs and outputs are IDs of typed values. `require` is a Lean
proposition over inputs; `ensure` is a Lean proposition over those same inputs
and the outputs. The remaining fields in `component-plan.json` identify the
component and point to a source snapshot; they do not enlarge its semantic
interface. A value has one producer, and every use of its ID denotes the same
Lean binder. A computed value has a distinct ID and an explicit producing
component. Types and fields are elaborated by Lean, so a shared name or source
location cannot equate two different values.

For each target, a connection lists all source components whose guarantees
are used. The checker creates the exact obligation

```lean
∀ (all plan values), ensure_source₁ ∧ ... ∧ ensure_sourceₙ → require_target
```

This permits fan-in and reuse: one `ensure` can discharge several connections,
and two sources can jointly establish a requirement that neither establishes
alone. Value production and connection dependencies must form a DAG. Every
component gets a discharge proof, including producers' own requirements; an
empty source list is valid only when its requirement is provable without plan
facts. Thus circular justification cannot close a plan. The plan has no
remaining external `require` only after all these obligations succeed.

The final obligation is generated from the **original typed property**:

```lean
∀ (all plan values), ensure₁ ∧ ... ∧ ensureₙ → Contract.Premise finalOutput
```

The final value must have the exact `Contract.Input` type. The checker asks
the existing native property frontend to parse and type the original
`.watsup` property, compiles its plan with the original catalog and
restriction, and reconstructs `Contract.lean` with the maintained renderer.
It rejects a changed contract, changed specification source, stale Lean
semantic modules, missing proof, unsupported Lean term, forbidden axiom, or
failed exact declaration audit. The proof propositions are generated from
the graph, not entered as separate substitute goals. The tool writes scratch
Lean modules under `build/scratch/` and uses the existing
`#spec4pbt_verify` audit. `plan-check` does not issue a generator certificate
and changes no `emit/check/run` rule.

The implementation workflow is: parse the selected specification and
property with the existing frontend; name each shared or computed value and
write the four fields for each component; record the sources used at each
connection; supply Lean proofs for those connection implications and the
final premise implication; run `plan-check`. A later implementation task can
relate actual generator declarations to these conditional contracts and then
use the unchanged `emit/check/run` certification path. The planning check
does not require generator soundness, completeness, or nonemptiness proofs.

## Wasm `Module_ok` representation

`properties/wasm_module_ok/component-plan.json` represents the existing
constructive generator at six meaningful boundaries:

| Component | Actual construction represented | Values and dependency |
| --- | --- | --- |
| `prefix` | `ConstructiveModulePrelude.prefixGen`: types, imports, function headers | shares the selected headers |
| `sections` | `ConstructiveModulePrelude.generate` and `raw`: tables, memories, globals, tags, elements, data, exports | raw prelude retains those headers |
| `free_context` | `ConstructiveModulePrelude.finalContext`: compute original free summary and final context from raw prelude | one computed `free`/`ctx` pair, not resampled |
| `bodies` | `ConstructiveModuleFunctionList.generate`: typed bodies for selected headers | reads the shared context and header list |
| `start` | `ConstructiveModuleStart.generate` | reuses the same final context as bodies |
| `assembly` | `ConstructiveModuleGeneration.generate` / `module` | joins prelude, bodies, start into the original module input |

The `assembly` connection uses `sections`, `free_context`, `bodies`, and
`start` together. `sections` and `free_context` also discharge the `bodies`
requirements; `free_context` is reused for `start`. The assembly contract
ensures `Nonempty (Validity.ModuleOkTrace input.m)`. The original
`Validity.module_ok_of_full_trace` theorem proves this implies the exact
`Contract.Premise input`, which is `SpecTec.Module_ok input.m`. The trace has
all original `Module_ok` checks: free summary, contexts, types, imports,
functions, tables, memories, globals, tags, elements, data, function bodies,
START, and exports with ordered supply. No premise was removed.

The mapping is **static**. Source symbol and byte fingerprints establish
which implementation definitions it describes; this checker does not prove
that those definitions satisfy each component's `ensure`, nor that the
assembled value exists. The full implementation and its original soundness
and completeness proofs remain in reference commit
`33e314af20717d44709f5ad2c0862d057b`; this task does not import or
recertify its 743-property-file proof closure. The generator's own
soundness/completeness are not prerequisites for planning. The original
`emit/check/run` certificate and execution audits retain their separate
meaning.

## Reproducibility and boundary

The complete upstream Wasm SpecTec source and property come from the cited
reference commit. `scripts/tests/fixtures/wasm_plan_reference/` contains exact
tracked copies of four directly mapped implementation files, plus the root
`Generator.lean` and `ConstructiveTypes.lean` for source review. The plan's
`implementation_refs` pins `Generator.generator` and
`ConstructiveModuleGeneration.modules` as the implemented root. The
tracked `specifications/wasm/PlanReference/Spec.lean` is the original
generated ordered Lean specification from reference translation identity
`s41537f07a12c318563e6aabf63ee533b7bcdb33a44bfeb071c4af4b8ddd8bf9a`
(SHA256 `29460cc8274204692084ed05f108e7d7fbe3dc41a2bd8a6346cd8a989c683fb2`).
The original generated transport and contract were copied with only module
path changes into `properties/wasm_module_ok/PlanReference/`; the original
`Validity.lean` changes only its helper import. The checker fingerprints
these Lean modules and reconstructs the contract directly from the native
typed property IR, so a stale or substituted target is rejected. The
reference translator's Wasm builtins are absent from `P4-spectec-based`:
ordinary `emit` currently fails at builtin `$lsl_`. The frozen Lean source is
therefore a declared reference dependency, not a fresh baseline translation.

From the repository root, with the pinned submodule and local toolchain built:

```sh
python3 -m scripts.property inspect \
  --spec specifications/wasm/spec \
  --property properties/wasm_module_ok/property.watsup \
  --name wasm_module_ok
python3 -m scripts.property plan-check \
  --plan properties/wasm_module_ok/component-plan.json --timeout 900
python3 -m unittest scripts.tests.test_component_plan -v
```

The current outcome is six checked component contracts, every requirement
internally discharged, and an exact final `Module_ok` premise implication.
Unsupported input/output types or expressions fail Lean elaboration; the
tool does not infer contracts, connection proofs, or implementation
correspondence. A future implementation phase can attach verified generator
code to these boundaries without changing the plan's four-field contract.
