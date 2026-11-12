# Rust Wasm generator case study

The ultimate target is the pinned Wasm `Module_ok` in
`specifications/wasm/spec/2.5-validation.modules.watsup`. The generator constructs
typed modules without invoking the oracle or rejecting candidate modules. This is
an executable generalization experiment; no soundness, completeness, termination,
or translation-preservation theorem has been attempted or completed.

## Interfaces and target

The actual Rust core exposes:

```rust
sample(config: Config, seed: u64) -> Result<(Module, Choices), GenerationError>
replay(config: Config, tape: Vec<u64>) -> Result<(Module, Choices), GenerationError>
```

`Config` contains `max_types`, `max_functions`, `max_parameters`, `max_results`,
`max_locals`, `max_exports`, `fuel` (usize), and `work_limit` (u64). The first seven
bounds and parameter-plus-local maximum must fit u32. Types and functions have
independently chosen counts, including zero. Types can be shared, duplicated or
unused; functions select arbitrary existing type indices. Signatures and locals
are vectors of i32/i64, with arbitrary counts within their respective maxima,
including zero and multiple results. Function declarations precede body construction,
so direct calls can be forward, self-recursive, or mutually recursive. Exports have
independent counts and targets, including aliases. Their names are distinct ASCII
`e0`, `e1`, … in export order. Start is absent or refers to a `[] -> []` function.

An independent intermediate target is the restriction of `Module_ok` to singleton
final function recursive types without supertypes; i32/i64 parameters, results and
locals; and well-typed sequences of full-width integer constants, local.get/set/tee,
nop, drop, integer add/sub/mul, direct calls, block, loop, and if. Blocks may use any
existing function type (including parameters and multiple results), or inline empty
or single-result types. Bodies have the declared stack effect, and indexed block
types, duplicate types, instruction order and literal bit patterns are retained.
Exports use the names above, start follows its actual validation rule, and other
sections are empty. This domain is described by syntax and typing, not as the
image of a generator. Executable coverage additionally requires counts and chosen
fuel/tape lengths to fit the core representation, including the global maximum
parameter count plus maximum local count fitting u32. Coverage of even this
restriction remains a future obligation.

**Known counterexamples to the ultimate target remain.** A valid memory-only module,
a function returning f32, an export named `x`, or an `unreachable` instruction is
outside this generator. Imports, globals, tables, memories, tags, elements, data,
references/GC, float/vector types, subtyping/recursive type groups, branches, returns,
exceptions, indirect/tail calls and the other numeric/memory instructions remain
unsupported. Canonical names are a syntactic restriction, not a claim of exact AST
coverage up to renaming. The next expansion must extend these AST/context/section
and instruction cases; this intermediate restriction does not replace full `Module_ok`.

## Construction, choices and resources

The body builder works backward from a requested input/output stack. It chooses a
locally applicable last instruction and constructs the required preceding stack.
A task stack separates this from child block construction; call arity is a vector
length rather than hard-coded cases. A base construction preserves a common stack
prefix, drops excess inputs and produces remaining values with constants or matching
local reads. Each optional expansion consumes one fuel unit and divides the rest
between prefix and nested bodies. Fuel is shared, so increasing it does not copy an
entire budget into every branch. Base instructions also contribute to AST size:
`fuel` is an expansion budget, not an exact instruction count or a runtime call bound.
Wasm calls can recurse forever even when generator construction terminates. The
experiment executes the generator and validates its output; it does not execute
generated Wasm functions.

`work_limit` separately counts choice draws, task execution and base drops; exhaustion
returns `WorkLimit`. It is not a wall-clock or memory measurement: scans, copying,
allocation and serialization still cost resources. The CLI applies additional
explicit safety rejections; it never silently saturates a requested bound:

```text
wasm COUNT SIZE SEED
wasm sample MAX_TYPES MAX_FUNCTIONS MAX_PARAMETERS MAX_RESULTS MAX_LOCALS MAX_EXPORTS FUEL WORK SEED
wasm replay MAX_TYPES MAX_FUNCTIONS MAX_PARAMETERS MAX_RESULTS MAX_LOCALS MAX_EXPORTS FUEL WORK TAPE_CSV
```

Legacy `COUNT SIZE SEED` prints complete module JSONL. `COUNT` is 1..1024, `SIZE` is
0..32 and sets each of the seven bounds, work is 100000 per module, and
`SEED+COUNT-1` must fit u64. Explicit commands accept maxima at most 64, fuel at most
128, and work at most 1000000; they print `{module,choices,state,remaining}`. Replay
uses comma-separated u64 cells (`-` for an empty tape), with at most 1000000 cells.
These are frontend execution limits, distinct from the core's machine bounds.
For example, the CLI cannot produce 65 functions even though the translated core
accepts that count bound. Any future coverage statement over larger configurations
must name the actual translated `sample`/`replay` function interface; it cannot
attribute that support to this CLI.

Seeded sampling uses the unchanged shared SplitMix64 word function and modulo
selection. It records every actual bounded index or literal word. Replay executes
the same core: bounded cells must be strictly below the current bound, i32 constants
use 0..2^32-1 and i64 constants use 0..2^64-1. Exhaustion, out-of-range cells and unused
trailing cells are distinct errors. There is no seed fallback, tape padding or
implicit truncation. Successful replay returns the consumed tape and null PRNG
state; successful sampling returns the final u64 state. Both report remaining work.

For a fixed configuration, counts, expansion fuel, work and input representation
restrict support. The union across configurations and finite tapes is a different
coverage question from any finite experiment. A Word64 seed space is not arbitrary
independent choices; recording/replay does not prove that a particular tape is
reachable from a seed. Nor do larger bounds prove fixed-size PRNG reachability.
Support must be defined by success of these actual translated entry points, with
both Rust errors and Aeneas failure/divergence accounted for. A future coverage
statement must relate that support to the independent domain above, including a
syntax-based sufficient resource bound, rather than define the target as support.

## Translation and trust boundaries

Pinned Charon/Aeneas translate the actual AST, choice engine, body builder, module
assembly, seeded sampler and replay entry point. The generated
`build/generator-rust/lean/GeneratorRust.lean` is not edited. The installed Vec model
lacks pop/swap_remove, so the source task/result stacks use an ordinary boxed list.
Aeneas rejected error returns inside reconstructed loops; fallible traversals use
explicit tail recursion, with signature predicates separated to close borrows
before branching. Arbitrary call parameter counts no longer require a mutually
recursive argument loop. These are Rust implementation changes, not Lean substitutes.

The experimental translation runner uses `-all-computable` and rejects emitted
axiom/sorry/admit/noncomputable declarations. Source vector construction uses
`Vec::new`/`push`: the pinned lowering of `vec!` introduced an unused opaque
`MaybeUninit` type, and `Vec::is_empty` lacked an executable mapping. Neither is
retained or supplied with an axiom.

Rust usize/u32/u64 map to bounded Lean scalars; this experiment uses the pinned
64-bit platform. Vec and Box use Aeneas library mappings. Generated functions still
use `Result`/`partial_fixpoint`; compilation and finite success do not establish
universal success, termination, scalar safety, library correspondence or behavior
under physical resource exhaustion.

The native and handwritten Lean CLI/JSON wrappers remain outside core translation.
They encode complete module records, singleton `RecT/SubT/DefFuncT` types, optional
start, inline/indexed block types and all supported instructions. Their embedding,
scalar/byte encoding and decoding by the unchanged native AL oracle remain trust
boundaries. Full JSON comparisons test these boundaries for a finite corpus; they
do not prove codec injectivity or equivalence to all specification ASTs. Oracle
guards, pinned sources and catalog are unchanged. See the shared
[oracle contract](../experiments/wasm/README.md).

## Validation

The [saved result](../build/wasm/completeness-rust/validation.json) records **123
complete native/Lean outputs matching** (79 distinct modules), including 12
seed-to-recorded-tape replay pairs and 13 authored witnesses. Explicit reports also
match choice tapes, final PRNG state and remaining work. All 123 generated modules
pass the unchanged `Module_ok`; 10 mutations are rejected. Eight tape, integer,
configuration and work-budget errors are rejected by both executables. An additional
valid module with export name `x` passes the oracle and is outside generator support.

Witnesses include six functions sharing a type, four mixed parameters, three locals,
two results, full u32/u64 constants, 12 aliased exports, empty/type-only modules,
forward/self/mutual calls, indexed blocks with parameters and multiple results,
eight nested blocks, a 64-NOP body, and an optional void start. The wider seeded
corpus reaches 15 functions and signatures/locals with 16 entries. The unchanged
toy regression passes 193 complete AST/final-state comparisons; the common oracle
regression passes its valid, invalid and malformed-input checks. These are finite
execution checks, not general coverage or validity theorems.

Run from the repository root using the existing pinned tools:

```sh
export CARGO_BUILD_JOBS=1 MAKEFLAGS=-j1 LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
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
Rust/Lean arithmetic/library correspondence, and exact AST/JSON/spec embedding.
Full-spec generation must expand the exclusions above before full `Module_ok`
completeness can even be a candidate claim.
