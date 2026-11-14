# Rust Wasm generator case study

The ultimate target is the pinned Wasm `Module_ok` in
`specifications/wasm/spec/2.5-validation.modules.watsup`. The generator constructs
typed modules without invoking the oracle or rejecting candidate modules. This is
an executable generalization experiment with handwritten Lean contracts and initial
proofs. Memory-import-only coverage, memory/data composition and successful import
execution soundness were checked at the preceding memory-import translation.
The current source also supports arbitrary-natural i64 constants; its complete
proof recheck is interrupted as described below. Globals and other missing
constructors still prevent full-spec completeness. Universal soundness,
termination and translation preservation remain unproved.

## External-server continuation checkpoint

Work is stopped at the user's request on 2026-11-14 for commit/push and continuation
on another server. No validation process from this task remains running. The exact
unrestricted targets in `proofs/WasmContract.lean` remain unchanged and unproved.

The applied source includes arbitrary-Nat i32/i64 constants, arbitrary `List String`
passive data, recursive sequences/natural bounds, exact control/type/ref witnesses,
completed type-comparison caching and memory imports. The current i64 source passed
23 native integration tests, fresh Charon/Aeneas translation, five core/runtime
modules, 63 full replay comparisons, 19 negative categories, 93 sampling outcomes
(including 15 exact errors), two wide comparisons and 143 original-oracle acceptances.
These finite checks do not prove unrestricted soundness or completeness.

At the current translation identity
`024052e064474f3e642a56947e1f9e20c63d10b783c49eb3a632977e429284ed`,
18 of 50 maintained proof modules are checked, including three unchanged
original-specification-only modules reused after source/artifact/dependency checks.
`WasmConstantReplay` and `WasmConstantSpecification` completed;
`WasmConstantSupport` was interrupted before its audit completed. The remaining
modules must be checked against this translation. Unit 9 is not sealed. Earlier
completed units establish their claims only at their recorded source identities.

Source-only drafts are included separately:

- [`constant-globals.patch`](../experiments/generator-rust/pending/constant-globals.patch)
  contains 35 unapplied file changes: both numeric widths/mutabilities, arbitrary
  global lists, codecs/tests and eight new proof modules (58 total). It includes
  an original-syntax inversion from `Module_ok`. None of these drafts has compiled.
- [`fresh-export-names.patch`](../experiments/generator-rust/pending/fresh-export-names.patch)
  is based on the globals patch and contains 11 incomplete, unapplied file changes.
  Prefix construction excludes used names directly over `List Nat`, without retry.
  The core, two native tests and two Lean helper drafts are preserved; existing
  name proofs still need migration, and all-success, full-module replay, original
  validity and validation-script work remain. Do not apply it as a finished unit.
- [`source-identities.json`](../experiments/generator-rust/pending/source-identities.json)
  records patch bases and outputs. Both patches were applied in order to a temporary
  source copy and checked byte-for-byte; this was not compilation or proof validation.

On the external server, bootstrap the pinned toolchain using
[`bootstrap.py`](../experiments/generator-rust/bootstrap.py), regenerate the current
Rust translation, then run the existing `prove` command below with that server's
ordered Wasm specification directory. Complete the current 50-module check before
applying the globals draft with `git apply --check` followed by `git apply`.
Run the real missing-feature test before applying a feature and preserve exact
native/Lean results, error cases and seed requests. Keep heavy builds sequential
unless the new server's measured resources justify changing that constraint.

Generated translations, compiled caches, certificates and execution traces remain
ignored and are not included in Git. Local evidence is preserved under
`build/rust-nat-extension-20261113/` (current state: `progress.md`, stopped run:
`unit9/current-state.json` and `unit9/user-stop.json`). The complete local Lean cache
is `/mnt/d/spec4pbt-lean-cache-20261113`; transfer these separately if reusing them,
and verify identities before reuse. New-server paths must be resolved locally.

## Interfaces and target

The actual Rust core exposes:

```rust
sample(config: Config, seed: u64) -> Result<(Module, Choices), GenerationError>
replay(config: Config, tape: Tape) -> Result<(Module, Choices), GenerationError>
```

`Config` contains `max_types`, `max_functions`, `max_parameters`, `max_results`,
`max_locals`, `max_exports`, `fuel`, `max_memories`, `max_datas`, `max_memory_imports`, and
`work_limit`, all represented by binary `Natural`. Numeric counts, indices and
fuel have no machine-word upper bound. `max_types` bounds both the number of raw
recursive groups and each group's width, independently; empty groups are retained.
All group headers precede signatures. A member is Final or NoFinal and may select
one earlier NoFinal parent. The current parent branch copies the parent's raw
signature exactly; general variance and differently spelled alias signatures remain
unimplemented. Unparented signatures may use i32/i64 and nullable/non-null static
references to previous or same-group definitions, including forward references.
Declared locals remain defaultable. Function indices refer to flattened members,
while output preserves the raw group structure and every written index.
Function declarations and exports precede body construction, so direct calls can
be forward, self-recursive, or mutually recursive. Exported function indices form
the current exact REFS context for ref.func; bodies and START cannot declare their
own references. Exports have
independent counts and targets, including aliases. Their names are distinct ASCII
`e0`, `e1`, … in export order. Start is absent or refers to a `[] -> []` function.
Memory declarations have an independent maximum and 32/64-bit address types.
Their minimum pages range inclusively through 65536 or 281474976710656 respectively;
an optional maximum is chosen directly between the minimum and that upper bound.
The memory section uses a boxed recursive Rust list, with a structural Lean embedding.
Its maximum, tape cursor and work budget use the actual binary-natural Rust representation.
At zero remaining maximum, generation consumes no choices. Otherwise a word choice
selects stop or continue; continuing constructs one memory and recursively generates
the tail under the decremented maximum. Multi-memory tapes therefore include a
continuation cell before each memory. The bounded CLI still accepts the same maximum
argument and converts it to this representation.

Memory imports use an independent `max_memory_imports` bound and run after type
generation, before function selection. Each entry constructs a memory descriptor
and two `Sequence<Natural>` names. Names preserve the original `List Nat` exactly;
Unicode, byte and machine-word restrictions do not apply. Import order and duplicate
names are retained. Zero import budget consumes no choices, so old explicit
configurations retain their execution when this field is zero. Legacy sized sampling
now gives imports the same size budget as the other sections.

Passive data uses boxed recursive `Datas` and `Text` lists. `max_datas` bounds the
number of segments; each string ends with an explicit stop choice. Scalar choices
range over Unicode ordinals excluding surrogates and preserve the exact original
`String`, including NUL and non-BMP characters. The section and payload lengths
have no machine-sized fields in the Rust core.

An independent intermediate target is the restriction of `Module_ok` to singleton
final function recursive types without supertypes; i32/i64 parameters, results and
locals; and well-typed sequences of arbitrary-natural i32/i64 constants, local.get/set/tee,
nop, drop, integer add/sub/mul, direct calls, block, loop, if, unreachable, br, and br_if. Blocks may use any
existing function type (including parameters and multiple results), or inline empty
or single-result types. Bodies have the declared stack effect, and indexed block
types, duplicate types, instruction order and literal bit patterns are retained.
Exports use the names above, start follows its actual validation rule, memories
have valid limits, data segments are passive, and other sections are empty. This domain is described by syntax and typing, not as the
image of a generator. Counts, indices, fuel and syntax lists use unbounded recursive
representations. Coverage of this restriction still requires actual replay witnesses
for every valid body and declaration arrangement.

**Known counterexamples to the ultimate target remain.** A valid immutable i32 global,
a function returning f32 or an export named `x` is
outside this generator. Other import kinds, globals, tables, tags, elements, active data,
general references/GC, float/vector types, variant subtype signatures, branch tables/reference branches, returns,
exceptions, indirect/tail calls and the other numeric/memory instructions remain
unsupported. Canonical names are a syntactic restriction, not a claim of exact AST
coverage up to renaming. The next expansion must extend these AST/context/section
and instruction cases; this intermediate restriction does not replace full `Module_ok`.

## Construction, choices and resources

The body builder works backward from a requested input/output stack. It chooses a
locally applicable last instruction and constructs the required preceding stack.
A task stack separates this from child block construction; call arity is a sequence
length rather than hard-coded cases. A base construction preserves a common stack
prefix, drops excess inputs and produces remaining values with constants, matching
initialized local reads, or declared ref.func producers. Closed alias equality compares
whole rolled/substituted groups and member positions, including nullability; it does
not rewrite raw AST indices or stand in for directional subtyping. A comparison threads
a private list of completed ordered-index results through the same immutable group
context. Only finished comparisons are reused; pending pairs and raw-index identity
do not bypass reference resolution. Nullable references
use ref.null. A non-null goal without a producer fails explicitly with
`NoReferenceProducer`. Non-null Drop predecessors currently come only from exports;
reads after initializing non-null declared locals and reference-valued unreachable/
branch prefixes remain outside the current construction. Each optional expansion consumes one fuel unit and divides the rest
between prefix and nested bodies. Fuel is shared, so increasing it does not copy an
entire budget into every branch. Base instructions also contribute to AST size:
`fuel` is an expansion budget, not an exact instruction count or a runtime call bound.

Each body task carries a linked label context. Function and block/if labels use
result types; loop labels use parameter types. Nested frames start with their own
parameters. Unreachable and unconditional branches choose a preceding stack prefix
before constructing it; branch arguments are appended from the selected label.
Conditional branches retain those arguments on fall-through. Preceding stack width
also contributes to the required construction fuel. Exact replay fixtures preserve
these instruction sequences without inserting instructions or normalizing blocks.
Wasm calls can recurse forever even when generator construction terminates. The
experiment executes the generator and validates its output; it does not execute
generated Wasm functions.

`work_limit` separately counts choice draws, task execution and base drops; exhaustion
returns `WorkLimit`. It is not a wall-clock or memory measurement: scans, copying,
allocation and serialization still cost resources. The CLI applies additional
explicit safety rejections; it never silently saturates a requested bound:

```text
wasm COUNT SIZE SEED
wasm sample MAX_TYPES MAX_FUNCTIONS MAX_PARAMETERS MAX_RESULTS MAX_LOCALS MAX_EXPORTS FUEL MAX_MEMORIES MAX_DATAS MAX_MEMORY_IMPORTS WORK SEED
wasm replay MAX_TYPES MAX_FUNCTIONS MAX_PARAMETERS MAX_RESULTS MAX_LOCALS MAX_EXPORTS FUEL MAX_MEMORIES MAX_DATAS MAX_MEMORY_IMPORTS WORK TAPE_CSV
```

Legacy `COUNT SIZE SEED` prints complete module JSONL. `COUNT` is 1..1024, `SIZE` is
0..32 and sets each of the ten bounds, work is 100000 per module, and
`SEED+COUNT-1` must fit u64. Explicit commands accept maxima at most 64, fuel at most
128, and work at most 1000000; they print `{module,choices,state,remaining}`. Replay
uses comma-separated u64 cells (`-` for an empty tape), with at most 1000000 cells.
These are frontend execution limits; the core represents arbitrary natural bounds.
For example, the CLI cannot produce 65 functions even though the translated core
accepts that count bound. Any future coverage statement over larger configurations
must name the actual translated `sample`/`replay` function interface; it cannot
attribute that support to this CLI.

Seeded sampling uses the unchanged shared SplitMix64 word function and modulo
selection. It records every actual bounded index or literal word. Replay executes
the same core: bounded cells must be strictly below the current bound. An i32 or i64
constant cell below 2^32 selects that literal; cell 2^32 selects a recursive positive
binary numeral (tags 0=one, 1=double, 2=double-plus-one). Exhaustion, out-of-range cells and unused
trailing cells are distinct errors. There is no seed fallback, tape padding or
implicit truncation. Successful replay returns the consumed tape and null PRNG
state; successful sampling returns the final u64 state. Both report remaining work.

For a fixed configuration, counts, expansion fuel, work and input representation
restrict support. The union across configurations and finite tapes is a different
coverage question from any finite experiment. The current core cannot cover the unrestricted mathematical AST merely by taking
the union of its configurations: missing constructors and canonical export names still restrict the output. Numeric syntax lists, indices,
counts, fuel, tape, trace, cursor, memory/data sections, i32/i64 literals, passive payload
strings and work budget use recursive Rust representations without machine bounds.
Original `Module_ok` does not impose a total module/instruction-list size bound.
Exact names are `List Nat`, so replacing fixed export names with byte vectors alone
would also be insufficient. Passive data payloads are `String` in the translated AST.
[WasmDomainWitnesses.lean](../experiments/generator-rust/proofs/WasmDomainWitnesses.lean)
proves that the original ordered `Module_ok` accepts a memory import with any two
`List Nat` names and a passive data segment with any `String` payload. These are
symbolic families, not a finite test corpus or a replacement support model.
The remaining representation work includes arbitrary-natural export
names, the remaining recursive/reference type constructors, and the missing section/instruction constructors.
The numeric builder uses the proved sequence and natural-index primitives directly;
representation coverage alone does not prove its execution completeness.

A Word64 seed space is not arbitrary
independent choices; recording/replay does not prove that a particular tape is
reachable from a seed. Nor do larger bounds prove fixed-size PRNG reachability.
Support is defined by success of these actual translated entry points, with
both Rust errors and Aeneas failure/divergence excluded. A future coverage
statement must relate that support to the independent domain above, including a
syntax-based sufficient resource bound, rather than define the target as support.

## Translation and trust boundaries

Pinned Charon/Aeneas translate the actual AST, choice engine, body builder, module
assembly, seeded sampler and replay entry point. The generated
`build/generator-rust/lean/GeneratorRust.lean` is not edited. Translation uses the
installed Lake manifest without rerunning dependency-update hooks; Lean compilation
uses one worker and an explicit memory ceiling. Source syntax, task and result
stacks use boxed recursive lists. Fallible traversals use explicit recursion;
conditional branches continue their recursion separately so that ownership joins
remain translatable. Arbitrary call parameter counts no longer require a mutually
recursive argument loop. These are Rust implementation changes, not Lean substitutes.

The experimental translation runner uses `-all-computable` and rejects emitted
axiom/sorry/admit/noncomputable declarations. Core sequence construction uses
`Sequence::Empty` and a boxed cons cell; native vectors occur only in adapters
and test harnesses.

Rust usize/u32/u64 map to bounded Lean scalars; this experiment uses the pinned
64-bit platform. Vec and Box use Aeneas library mappings. Generated functions still
use `Result`/`partial_fixpoint`; compilation and finite success do not establish
universal success, termination, scalar safety, library correspondence or behavior
under physical resource exhaustion.

The native and handwritten Lean CLI/JSON wrappers remain outside core translation.
They encode complete module records, singleton `RecT/SubT/DefFuncT` types, optional
start, memory declarations with optional maxima, inline/indexed block types and all supported instructions. Their embedding,
scalar/byte encoding and decoding by the unchanged native AL oracle remain trust
boundaries. Full JSON comparisons test these boundaries for a finite corpus; they
do not prove codec injectivity or equivalence to all specification ASTs. Oracle
guards, pinned sources and catalog are unchanged. See the shared
[oracle contract](../experiments/wasm/README.md).

## Validation

The preceding sealed memory-import implementation passed all 22 native integration tests,
including arbitrary-natural names, original memory bounds, duplicate imports and
129 entries. The real missing-feature test failed before implementation. Fresh
translation and native/Aeneas comparison pass: 65 replay reports, 19 negative
categories, 87 sampling outcomes including 15 exact error messages, and two wide
configurations agree. All 139 emitted modules pass the original oracle. The import
family's 22 axiom audits pass, including completeness from original `Module_ok` to
actual full replay for memory-import-only modules with arbitrary `List Nat` names,
list length, order and duplicates. All 50 maintained proof modules pass at this
translation. Four composition audits connect arbitrary imports, defined memories
and passive data in one exact full replay and original-validity proof. Three
soundness audits establish original memory validity for every successful actual
import entry/section execution, from any choice source and natural bound. The
[checked memory-import unit](../build/rust-nat-extension-20261113/unit8/result.json)
ties these proofs to the source and execution identities. The unrestricted
contracts remain unproved; the valid missing-global counterexample still applies.

The preceding completed-comparison cache unit has 20 passing native integration tests and
fresh Charon/Aeneas translation. Native regression preserves all 64 full reports,
16 negative error categories, and the expanded corpus of 111 module outputs plus
15 exact sampling errors. The problematic `4 16 2026` request retains its exact
`NoReferenceProducer` result and takes about 0.075 seconds, versus 4.52 seconds
before caching. The translated core and runner compile, and all
99 expanded requests finish in 90 seconds: 111 module outputs and 15 sampling error
messages exactly match native, all 16 negative error categories pass, and all 111
modules pass the original oracle. Cache lookup correctness, repeated shared-alias
execution, and rejection of early/later dangling references now pass kernel and
axiom checks. The four recursive/reference replay, embedding, and original-spec
chains also pass against this translation. All 42 maintained proof modules now
pass at this source identity, including the universal constant/passive families,
six numeric control families, original-domain memory representation and final
axiom audit. The [complete checked unit](../build/rust-nat-extension-20261113/unit7a/result.json)
ties those proofs to that translation and execution evidence; unrestricted
Soundness and Completeness remain unproved.

The preceding recursive-context translation has
[preserved checked proofs and incomplete runtime evidence](../build/rust-nat-extension-20261113/unit7/incomplete-result.json):
42 proof modules, arbitrary-Nat constants, arbitrary-List-String passive data, six
numeric control families, four recursive/reference families, and the memory
original-domain representation bridge passed. Its 64 full native/Aeneas reports
and 16 negative error categories also passed. The expanded comparison did not
finish: the combined evaluation exceeded 1800 seconds, and a later line-buffered
run was stopped at 755 seconds after 19 requests and 62 exact outcomes. Actual
comparison tracing identifies repeated closure expansion as the bottleneck.

The expanded 35-command sampling corpus preserves every requested seed, including
successful prefixes of failed batch commands. It emits 63 modules accepted by the
original oracle and 15 explicit `NoReferenceProducer` errors. The current 99-request
translated batch additionally contains successful replay pairs, targeted fixtures,
and negative cases. No failed seed is replaced. These finite checks do not establish
universal soundness, sampling totality, or completeness.

The prior [numeric-builder verification result](../build/rust-nat-extension-20261113/unit6/result.json)
preserves its 40 checked source/artifact identities and immutable source snapshots,
universal constant/passive families, 49 matching native/Aeneas reports, and 14 errors.
Its release binary and proof artifacts apply to that sealed source identity.
The [sealed primitive execution result](../build/rust-nat-extension-20261113/unit5/runtime-result.json)
records **47 complete native/Aeneas outputs matching** and 14 matching error cases.
The corpus includes 31 authored fixtures, six arbitrary-natural i32 literal cases,
three sample/replay pairs, and four passive-payload families. Comparisons include
module AST, choice tape, PRNG state and remaining work. All 47 outputs pass the
original `Module_ok`. Thirteen native integration tests also pass, including a
129-segment data list through the core API. Sequence and subtraction primitives
add 21 matching native/Aeneas reports, including indices and operands above 2^64,
underflow, missing elements and oversized splits. The
[sealed natural-bound choice unit](../build/rust-nat-extension-20261113/unit4/result.json)
records five matching native/Aeneas success states and four matching error cases;
these comparisons include unused tape, cursor, reverse trace and remaining work.

Payload cases cover NUL, combining characters, non-BMP characters, the surrogate
boundaries, U+10FFFF, and U+0085/U+2028/U+2029. JSONL readers separate records only
on LF, preserving these other valid string scalars. The real oracle regression
checks valid and invalid modules, malformed constructors, and unescaped Unicode
line-separator payloads. The authored fixtures also cover wide signatures,
aliased exports, calls, indexed/nested blocks, optional start, memory limits,
polymorphic unreachable sequences, loop labels, outer labels and conditional branches.
The original oracle rejects all 12 negative mutations, including a mismatched
concrete operand after unreachable and a fresh block frame missing its result.
These are finite execution checks; the universal constant and passive-list
statements are established separately by the Lean proofs below. The
[completed natural/passive proof unit](../build/rust-nat-extension-20261113/unit2/result.json)
preserves its exact source/artifact snapshot. The
[numeric control proof unit](../build/rust-nat-extension-20261113/unit3/result.json)
records six exact full replay witnesses, their original-specification proofs,
30 axiom audits, and the revalidated proof chain for its sealed translation.
Recursive groups, raw aliases and reference contexts have four checked exact full
replay witnesses linked to exact embeddings and original Module_ok proofs. Their
23 audited declarations, including the comparator execution checks, use only
propext, Classical.choice and Quot.sound.

Run from the repository root using the existing pinned tools:

```sh
export CARGO_BUILD_JOBS=1 MAKEFLAGS=-j1 LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MALLOC_ARENA_MAX=2
export RUSTC="$PWD/build/generator-rust/rustup/toolchains/nightly-2026-09-17-x86_64-unknown-linux-gnu/bin/rustc"
export CARGO_HOME="$PWD/build/generator-rust/cargo"
flock /tmp/spec4pbt-wasm-build.lock timeout 180 \
  build/generator-rust/rustup/toolchains/nightly-2026-09-17-x86_64-unknown-linux-gnu/bin/cargo \
  build --manifest-path experiments/generator-rust/native/Cargo.toml \
  --target-dir build/generator-rust/native-target --release --locked --offline
flock /tmp/spec4pbt-wasm-build.lock timeout 900 python3 -m experiments.generator-rust.translate
flock /tmp/spec4pbt-wasm-build.lock timeout 900 python3 -m experiments.generator-rust.wasm_case_study
flock /tmp/spec4pbt-wasm-build.lock timeout 900 python3 -m scripts.tests.rust_generator_translation
flock /tmp/spec4pbt-wasm-build.lock timeout 180 python3 -m unittest scripts.tests.wasm_generator_oracle -v
```

Evidence includes `modules.jsonl`, `reports.jsonl`, `requests.json`,
`negative-modules.jsonl`, `outside-support.jsonl`, `oracle-input.jsonl` and
`lean-execution.log` in `build/wasm/completeness-rust/`. The result records the
unchanged generated-source hash; the hash is provenance, not a certificate.
Pinned Wasm and imported translator source checksum checks also pass.

Remaining proof obligations are the independent grammar's relation to `Module_ok`,
stack/context and declaration invariants, actual translated Result success and
termination, replay witness construction with independently bounded resources,
Rust/Lean arithmetic/library correspondence, and correspondence between the total
proof embedding and the CLI's AST/JSON encoding.
Full-spec generation must expand the exclusions above before full `Module_ok`
completeness can even be a candidate claim.

## Handwritten Lean contracts and initial proofs

The sealed unit 7a validates the established families below. The current import
extension changes the Rust translation, so its migration and new proof modules
must compile before these results are attributed to the new source identity.

[WasmContract.lean](../experiments/generator-rust/proofs/WasmContract.lean) defines
`ReplayReturns config tape output` by equality of the **actual translated**
`wasm.replay config tape` to `Result.ok (.Ok (output, finalState))` for some final
state. Thus both the Aeneas computation and Rust Result must succeed.
`ReplaySupport config m` existentially quantifies the tape and output, requiring
`embed output = m`. `SampleSupport` independently quantifies a U64 seed for
`wasm.sample`; arbitrary replay support does not imply seed reachability.

The manually authored propositions are:

```text
Soundness:       ∀ config m, ReplaySupport config m → Module_ok m
Completeness:    ∀ m, Module_ok m → ∃ config, ReplaySupport config m
CompleteFor T:   ∀ config m, Module_ok m → T config m → ReplaySupport config m
```

`SamplingSoundness` and `SamplingCompleteness` use `SampleSupport` instead.
These quantify over the core interface with natural-number configuration fields,
independently of the CLI caps. `CompleteFor` is a parameterized proposition; no
independent bounded target predicate or proof has yet been supplied. No claim
here establishes termination for every call, sampling probabilities, or efficiency.

[WasmEmbedding.lean](../experiments/generator-rust/proofs/WasmEmbedding.lean) is a
total structural conversion to the original specification AST. Traversing Aeneas's
boxed `Sequence` structure directly makes nested instruction recursion checkable
without the runner's partial JSON serialization. This does not establish equivalence
between that serializer and the proof embedding.

[WasmSpecificationWitnesses.lean](../experiments/generator-rust/proofs/WasmSpecificationWitnesses.lean)
proves that the original memory-only example satisfies ordered `Module_ok`.
The former theorem that every embedded module has `MEMS = []` no longer applies:
actual Rust modules now contain a memory section. Its historical proof is preserved
in the proof-loop's immutable initial snapshot. The same module now has positive
actual replay coverage, described below. The sealed cache unit proved
`not_complete : ¬ Completeness` using `importsOnly_ok` and `importsOnly_not_generated`.
The current import extension removes that obsolete negative theorem, introduces
positive exact import coverage, and moves the remaining obstruction to
`globalsOnly`. These witnesses and the positive import family compile for the current
translation. `memory_imports_module_complete` in
[WasmMemoryImportRepresentation.lean](../experiments/generator-rust/proofs/WasmMemoryImportRepresentation.lean) derives
actual replay support from original validity and the memory-descriptor-only shape;
it does not narrow the unrestricted Contract. `dataOnly_ok` remains an original witness.

[WasmReplayWitness.lean](../experiments/generator-rust/proofs/WasmReplayWitness.lean)
proves an actual successful replay: all ten bounds are zero, work is one, tape
is `[0]`, and the result is the empty module with the tape consumed and work zero.
`empty_generated_valid` connects this execution to support and original `Module_ok`.
This is one concrete end-to-end proof, not universal soundness. The positive proof
uses Aeneas's WP lemmas and recursive unfolding equations; neither generated code
nor Rust code is replaced by a model or modified for these proofs.

[WasmConstantSupport.lean](../experiments/generator-rust/proofs/WasmConstantSupport.lean)
connects every `n : Nat` to a full successful `wasm.replay`, exact embedding with
body `[CONST (I32 n)]`, and the original `Module_ok`. `WasmNaturalChoice.lean`
proves the actual recursive numeral chooser and its exact replay state;
`WasmConstantReplay.lean` lifts it through module construction. There is no
machine-integer premise on `n`, and no seed-based completeness claim.

[WasmDataSupport.lean](../experiments/generator-rust/proofs/WasmDataSupport.lean)
proves full `wasm.replay` coverage for every `payloads : List String`, with exact
passive DATAS embedding and original `Module_ok`. `WasmDataEncoding.lean` proves
valid scalar representation and exact String roundtrip; `WasmDataChoice.lean`
proves the actual text/section chooser executions and final replay state.
`dataOnly_supported` supplies the former missing-DATAS counterexample's execution
witness. This result does not cover active data or the other missing AST cases.

[WasmControlSupport.lean](../experiments/generator-rust/proofs/WasmControlSupport.lean)
connects six exact full replays to their embeddings and original `Module_ok`:
unreachable followed by i32.add, one concrete operand after unreachable, a
nonempty predecessor stack, a loop parameter label, a branch to an outer block,
and br_if retaining its argument. `WasmControlReplay.lean` proves the complete
return values and final replay states. `WasmControlSpecification.lean` proves the
original judgments using checked `Eval` constructor proofs from
`WasmGroundEvaluation.lean`. All 30 replay/embed/specification/support declarations
pass the axiom audit. These fixed witnesses do not establish universal soundness
or completeness of control-flow generation.

[WasmMemoryWitness.lean](../experiments/generator-rust/proofs/WasmMemoryWitness.lean)
proves successful actual replay with all old bounds zero, `max_memories = 1`, work
five, and tape `[0,1,0,0,0]`. `memory_generated_valid` connects the resulting exact
memory-only AST to `Module_ok`. `WasmChoices.lean` proves an exact translated `pick`
step with its tape cursor, recorded trace and budget. `WasmMemoryProperties.lean`
proves the original ordered memory-type judgment from explicit page-limit bounds,
and that every finite list of represented memories embeds structurally without a
Vec length cap. `WasmMemorySupport.lean` and `WasmMemorySpecification.lean` connect
all bounded memory lists to full replay and original `Module_ok`.
[WasmMemoryRepresentation.lean](../experiments/generator-rust/proofs/WasmMemoryRepresentation.lean)
inverts original `Limits_ok` and `Memtype_ok` executions and proves exact
representation of every original valid memory type. It connects every such finite
memory list to actual replay and original module validity, preserving order and
duplicates. Word bounds follow from the specification's page bounds; they add no
extra restriction. General preservation of the builder's invariants remains unproved.

The replay input and recorded trace are boxed recursive `Tape` values. `Source.Replay`
keeps the unused suffix and a canonical binary-natural cursor; `Choices.remaining`
and `Config.work_limit` use the same unbounded Rust natural representation. The
trace is stored newest-first and both JSON frontends restore chronological order.
Frontend work/tape limits remain explicit runtime input restrictions. Bounded
scalar choices return `u64`; syntax indices use `pick_natural` without narrowing.
`WasmNatural.lean` and `WasmChoices.lean` prove actual binary arithmetic and tape
consumption. `WasmNaturalWord.lean` proves exact optional word conversion, including
overflow, and the inverse conversion. `WasmNaturalIndex.lean` proves that the actual
`pick_natural` executes every index below every positive natural bound with an exact
finite tape witness, preserving arbitrary trailing state. Its total WP theorem also
proves that every successful result is in range and the translated primitive cannot
panic or diverge; explicit generation errors remain allowed. All eight primitive
audit declarations use only `propext`, `Classical.choice` and `Quot.sound`.

`WasmSequence.lean` proves both representation roundtrips and exact execution of
append, snoc, length, lookup, consuming selection, last, reverse and exact split
for arbitrary lists and natural indices. Its Rust container boxes the entire cons
cell, including its head, so it also supports recursive AST elements.
`WasmNaturalDifference.lean` proves termination and exact binary subtraction for
all naturals, returning `None` exactly on underflow. All 16 declarations pass
fail-closed axiom audits in the sealed primitive unit.

The numeric module builder now uses these recursive sequences and natural indices.
`WasmModuleCoverage.lean` proves actual generation of every finite numeric value-type
list below a sufficient natural bound, selection of every list element, and full
empty-module replay for arbitrary values of all seven numeric bounds. Its four
declarations also pass the current recursive-context translation's axiom audit.
These results have no sampling-completeness claim; missing Wasm constructors still obstruct unrestricted
completeness.

Reproduce after the existing Rust translation command, with an explicit directory
containing the pinned ordered `Spec.lean` and `identity.json`:

```sh
flock /tmp/spec4pbt-wasm-build.lock \
  python3 -m experiments.generator-rust.prove \
  /home/min/spec4pbt/build/worktrees/wasm-spec-experiments/specifications/wasm/translated/s01a96470d72cdf8cb989d156704a6b06dd5a6eecbcd2529de55a842b29f240d9
```

The runner validates all 18 recorded specification source hashes against this
checkout and the generated specification hash, then compiles that specification,
the existing Aeneas output and the authored proof modules locally with one thread.
It does not import cached property proofs from the donor. `WasmProofAudit.lean`
checks the dependencies of the contracts and claimed theorems, allowing only
`propext`, `Classical.choice` and `Quot.sound`; no `sorry`, added axiom or
`native_decide` is used. Logs and a source-hash/result summary are written under
`build/generator-rust/manual-proof/`. This is not a property certificate or a proof
of Charon/Aeneas, native Rust, JSON transport, or specification translation.

The next general soundness proof needs declaration/context and backward-stack
invariants for the actual translated helpers, including nested task execution.
Full completeness additionally requires the missing AST constructors and their
constructive typing stages. Valid global modules remain outside every
current embedding; export names also remain restricted.
Recursive function groups, raw aliases and export-derived function-reference contexts
are now implemented for the subset described above; general subtype variance and
the remaining type kinds are still missing. Haskell and automatic proposition extraction are outside
this manual Rust proof experiment.
