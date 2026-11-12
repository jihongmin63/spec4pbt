# Constructive generator for original Module_ok

`Generator.generator : bundle.Contract.generatorValue` is now a constructive
module generator. `Generator.soundness` and `Generator.completeness` have the
exact generated contract types. `Contract.Premise input` remains definitionally
`SpecTec.Module_ok input.m`. Neither theorem has an additional readiness,
provenance, normalized-syntax, size, or implementation assumption. `Proof.lean`
stays separate and unchanged.

`ConstructiveModuleGeneration.modules_exact` states the full equivalence between
support and original Module_ok. Arbitrary original recursive groups, raw aliases,
function bodies, locals, names, strings, section lengths, and finite sizes are
covered. The theorem is about this repository's pinned original semantics;
it does not assert agreement with an external Wasm engine.

## Construction and completion

1. `ConstructiveTypes` constructs arbitrary fresh or copied recursive groups.
   The fresh branch fixes kinds and nominal parents before dependent signatures;
   the copy branch reifies all original raw aliases of an earlier closed group.
   Closed-group equality is used to split the backward proof, not to screen a
   proposed group. Stored raw signatures and history retain exact coverage.
2. `ConstructiveImports`, `ConstructiveModuleHeaders`, and the environment modules
   derive context readiness, provenance, nested-type readiness, and backing from
   actual preceding generated results. Function headers select existing function
   type metadata. Every header admits a body completion.
3. Initializers use `ConstructiveConstTargetPlan`: a productive target/production
   plan is selected before generating expression syntax. Tables/globals choose
   targets and initializers jointly. Empty element initializer lists also cover
   uninhabited valid reference types. Counts and plan depths are unbounded through
   the proven `Gen.arbNat` source and structural recursion.
4. Memory bounds reuse `ConstructiveLimits`: choose the lower bound within its
   range, then a delta within the remaining range. Legal indices come from bounded
   existing context entries. Active data/element offsets use productive numeric
   constants; mode selection uses existing memory/table type metadata.
5. The prelude temporarily permits all existing function indices in REFS.
   `ConstructiveFreeModule.moduleFree` then computes the original exact free record
   from the constructed prelude syntax. `ConstructiveModulePreludeFree` proves
   that every generated initializer reference occurs in that record; transport
   proofs reconstruct every original stage with these exact REFS. Function bodies
   and START are excluded from this summary by the original specification.
6. `ConstructiveBodyGeneration` constructs typed instruction productions, local
   state updates and recursive control blocks. `ConstructiveBodyCompleteness`
   covers every original finite body, all 95 raw opcode constructors / 100 original
   instruction clauses, and the original stack/control/local typing behavior.
   A normal empty ending is available when the stack metadata closes; an explicit
   legal UNREACHABLE production supplies completion at other stacks. It does not
   validate or repair a sampled complete body. Both normal and unreachable
   original bodies are included by the completeness proof.
7. Function definitions, arbitrary valid locals, START, and fresh exports complete
   the exact original module syntax. `ConstructiveModuleSoundness.original` builds
   a NEW original ModuleOkTrace from these local generated witnesses. It assumes
   no valid trace for the new output. `ConstructiveModuleCompleteness` uses an
   original successful trace only in the backward proof to recover each exact
   source field and the final original context.

The correspondence proofs retain ordered rules, normal unmatch/abort behavior,
and fresh supplies. Runtime construction is safe and total. Standard classical
logic occurs only in proofs, with axioms limited to propext, Classical.choice,
and Quot.sound.

## Screening audit

`Generator.structural` recursively excludes every Gen.assume node and proves
monotonicity of every indexed family, including every bind continuation.
`ConstructiveAttach` carries erased support proofs without deciding them; its
indexed lifting has its own monotonicity proof. `Generator.total` follows.
`GeneratorIndexAudit.lawful_generator` retains the older, weaker lawfulness
interface; that predicate alone is not an absence-of-screening claim.

Host decisions require a separate source review. The executable path uses:

- Existing type lookup/unrolling, subtype matching, defaultability, stack
  pop/push planning, and signature comparisons to choose structural productions.
  `ConstructiveBodyProductions.prepare` compares a production's fixed type effect
  with the current stack BEFORE sampling `p.instructions`.
- Productive constant tables containing typed generator plans. `planAt` tests
  the availability of a construction, not the validity of an expression AST.
- Existing index/type metadata for imports, headers, tags, active modes and START.
  The name `TagtypeValidation.tagtypeValid` on this path classifies an existing
  type index before a tag AST is constructed.
- Rank/unrank constructions for fresh names, finite bounded choices, structural
  list construction, and `Char.ofOrdinal` for every valid Unicode scalar.
- Syntax union for the original free summary. Set normalization here implements
  the specification's free-record operation; it does not normalize the AST.

No path generates arbitrary module/instruction/expression candidates and then
validates, discards, replaces or retries them. No prefiltered AST candidate pool
or screened fallback is used. Historical screened modules remain as preserved
prior work but are absent from the generator's runtime dependency graph.

The scratch `ModuleRuntimeGraph.lean` traverses compiled IR after proof erasure:
2,120 dependencies, no missing IR entries. It finds no PositiveRuntime evaluator,
accepts function, assumption constructor, filter, encoded-AST search, old screened
fallback, or executable classical choice on this generator path. Existing
functions with Validation/Decision names on the path are the metadata operations
listed above; proof-only classifier uses are erased. The repository executable
and compiler-policy audit also passes. This is worker audit evidence; independent
orchestrator review remains separate.

## Evidence and practical limits

All 127 promoted body modules and 40 promoted module-stage modules were rebuilt
from local source before entrypoint integration. Exact-contract compilation and
runtime/axiom audits passed. Evidence is preserved in
`build/scratch/ConstructiveWasm/`, including failed attempts and exact commands.

The integrated generator produced 900 samples over three seeds and sampler fuel
sizes 20/40/80, with retries disabled. All 2,700 original Module_ok checks passed
at supplies 0, 317 and 1,000,000. These are 293 distinct ASTs: fixed seeds repeat
across sufficiently large sampler fuel settings. Samples include 30 function
definitions (10 before cross-size repetition), nested LOOP/BLOCK/TRY_TABLE,
locals, reference/vector instructions and initializer arithmetic. The ordinary
sampling distribution favors small modules and often UNREACHABLE completions;
exact support is a proof result, not a uniformity or diversity claim.

Separate promoted body tests passed 900 original Block_ok calls for 300 samples;
section tests passed 840 original calls. Earlier targeted tests cover all body
families, recursive types, constants, bounds and aliases. The low-fuel size-3
sample failure is preserved: standard arbNat can exhaust finite sampler fuel.
Increasing that budget does not add screening or a retry path, and the formal
support has no fixed bound.

These are checks against the original semantics through the proved PositiveRuntime
bridge. No external Wasm-engine execution is claimed. See the final scratch report
for property certification status and reproducible commands.
