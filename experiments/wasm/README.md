# Wasm generator case study

The unchanged 18-file SpecTec Wasm specification is in `specifications/wasm/spec`.
Its source revision is recorded in `specifications/wasm/upstream.json`; every source
and its license is checked against `SHA256SUMS`. The target is the real `Module_ok`
relation in `2.5-validation.modules.watsup`, not an independently written validator.

## Execution boundary

`oracle.ml` decodes canonical module JSON and invokes `Module_ok` through the
repository's native SpecTec AL interpreter with guards enabled. External calls
are blocked. Builtins use the existing Wasm integration. The oracle is trusted
test infrastructure; its verdict is neither a proof nor a property certificate.
Malformed JSON/ASTs and interpreter aborts are errors, distinct from a false verdict.

Build with an explicit existing Wasm-enabled repository toolchain:

```sh
python3 -m experiments.wasm.build_oracle /home/min/spec4pbt/build/worktrees/wasm-spec-experiments
python3 -m unittest scripts.tests.wasm_generator_oracle -v
python3 -m experiments.wasm.check build/wasm/modules.jsonl
```

The builder verifies the donor's source/binary freshness, adds only an isolated
target inside its ignored build tree, and copies the executable locally. The
manifest records both toolchain and specification identities. Checks reject stale
source, binary, or specification hashes. Native SpecTec is shared infrastructure;
it is not part of either generator's Rust/Haskell-to-ITP translation.

## Generator interface

Retain the existing `COUNT SIZE SEED` command-line shape. State exactly what SIZE
bounds for modules; it need not mean the toy experiment's exact AST node count.
Print one complete module per JSONL line. Keep CLI/JSON serialization separate
from the pure translated generator. Translate the actual AST-building body,
including state, recursive instructions, and module assembly.

Canonical JSON uses all module fields (`TYPES`, `GLOBALS`, `TABLES`, `MEMS`, `TAGS`,
`FUNCS`, `START`, `ELEMS`, `DATAS`, `IMPORTS`, `EXPORTS`). Records are objects,
lists are arrays, absent options are null. Nullary constructors are strings;
unary constructors are single-key objects; multiargument constructors use an array
payload. Names follow the existing Lean translator's constructor naming. Example:

```json
{"TYPES":[{"RecT":[{"SubT":["Final",[],{"DefFuncT":{"FuncT":[[],[{"NumT":"I32T"}]]}}]}]}],"GLOBALS":[],"TABLES":[],"MEMS":[],"TAGS":[],"FUNCS":[{"FTYPE":0,"LOCALS":[],"BODY":[{"CONST":{"I32":7}}]}],"START":null,"ELEMS":[],"DATAS":[],"IMPORTS":[],"EXPORTS":[]}
```

The integration test checks empty and nonempty valid modules and rejects wrong
result stacks, function type indices, local indices, export indices, and start
signatures. It also checks malformed constructor handling.

## Study requirements

Construct valid modules using typing/context invariants; do not use the oracle as
a rejection filter. Specify the supported fragment, finite bounds, random choice
model, and omitted features. Exercise nontrivial state and recursive instruction
construction, and retain diverse seed/size corpora. Empty modules alone do not
satisfy this study. Compile generated Lean/Rocq and compare native/translated
outputs on a bounded corpus where possible. Generated target source must remain
unmodified; record library mappings and trusted boundaries explicitly.

Future work must distinguish validity, completeness for a specified fragment,
choice-tape reachability versus finite-PRNG reachability, termination/fuel,
serialization correspondence, and translation/library semantic preservation.
No full soundness or completeness claim is made by these execution tests.

## Resource discipline

Run heavy builds and translated execution under the shared lock:

```sh
flock /tmp/spec4pbt-wasm-build.lock COMMAND ARGUMENTS...
```

Use `CARGO_BUILD_JOBS=1`, `MAKEFLAGS=-j1`, `LEAN_NUM_THREADS=1`, and one GHC/Rocq
compiler process. Reuse the installed pinned tools and cached dependencies. Avoid
Lake native builds of Aeneas/mathlib; direct Lean compilation and `#eval` already
work. Save logs and progress under the branch's ignored `build/wasm/` directory.
