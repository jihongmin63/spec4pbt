# Historical screened generator and original-semantics runtime bridge

The paragraphs below describe the preserved pre-constructive hybrid. The current
entry point is documented in [ConstructiveGenerator.md](ConstructiveGenerator.md);
it no longer invokes this evaluator during generation. The proved runtime bridge
below remains available for tests.

The historical `Generator.generator`, `Generator.soundness`, and `Generator.completeness` used
the unchanged `bundle.Contract` and every original `SpecTec.module` value.
Completeness includes arbitrary original function bodies, rather than just the
bodies used by the productive proposal branch.

The fallback samples an encoding and a fuel parameter. A successful bounded run
returns that exact decoded module. An invalid encoding or a run without a
successful result uses the productive proposal branch. This substitution is
sound and retains every successful decoded input in support. It also avoids
requiring the sampler to recover from a failed search by backtracking.

The proposal branch constructs one to three memories or functions, with exports,
and screens the assembled module through the same proven runtime. Its fixed
fuel and selected shapes affect sampling productivity only. They do not bound
the complete fallback. The separate `Generator.search` preserves the raw exact
screening search for performance comparisons.

## Original-semantics bridge

- `PositiveCalls`: 231 validation-reachable typed calls and a proof-only mapping
  into the original call type. The smaller runtime representation avoids the
  constructor-tag limit of the full imported call type.
- `PositivePlans`: 884 typed clause/list declarations plus program dispatch.
  They retain original order, guards, continuations, outputs, and supply behavior.
- `PositiveErasure`, `PositiveCorrespondence`, `PositiveBody`: 653 clause
  erasure theorems and the full program-body correspondence, checked by Lean
  against the unchanged imported definitions.
- `PositiveComplete`: a safe fuel-bounded evaluator, monotonicity, and a proof
  by induction on every original finite evaluation derivation that sufficient
  fuel exists. The runtime is the imported `runEval` applied to the typed program.
- `PositiveSound`: every completed run has the corresponding original evaluation.
- `PositiveCheck`: successful bounded evaluation is equivalent, existentially
  over fuel, to original `SpecTec.Module_ok`. All body-correspondence parameters
  are instantiated with the proved `body_correct` theorem here.
- `GeneratorIndexAudit`: a recursive `Lawful` predicate proves monotonicity at
  every indexed node, including all bind and assume continuations. The indexed
  family used is the library's proved-monotone `arbNatAux`.

`accepts fuel m = false` means only that this bounded run did not witness success.
It does not prove logical rejection. The underlying runtime keeps normal
failure, abort, exhaustion, and unsupported primitives distinct.

Executable declarations use no classical choice, unsafe/partial definitions,
compiler substitutions, or custom axioms. Proof-only mapping and erasure may be
noncomputable. The executable-code audit separates those proof dependencies from
runtime dependencies. The existing independent `Proof.lean` remains unchanged.

Build the final property sources with:

```sh
lake build properties.wasm_module_ok.Generator properties.wasm_module_ok.GeneratorIndexAudit
```

The implementation record, source-generation scripts, failed experiments,
original-contract audits, and samples are preserved under
`build/research/module-ok-one-20261030-0500/` and the preserved worker worktree
`.worktrees/module-ok-one-20261030-0500/build/scratch/HybridOne/`. The research
report records commands and observed sampling limits. The orchestrator independently
rebuilt the sources and passed the original `python3 -m scripts.property check`
on 2026-10-30. The generated certificate stays in the ignored `bundle/`.
Sampling reproduced 1,600/1,600 nonempty hybrid outputs, but raw encoding search
produced none: practical coverage still comes from the restricted proposals.
No external implementation was invoked.
