# Translator provenance

The Lean backend in `src/` was imported byte for byte from the development
checkout of P4-SpecTec at commit
`d150aa6e53e3f572bc4b02299c05d6d6cee9d6c0`. That checkout originated from
`jihongmin63/p4-spectec`; it is source provenance, not a build dependency.
The backend's original path was `p4spec/lib/lean-skeleton/`.

The frontend and interpreter libraries remain an official
[kaist-plrg/p4-spectec](https://github.com/kaist-plrg/p4-spectec) submodule at
`2730cfd9e74048bb5439da0f8afcef124079a064`. No private repository or Docker
checkout is needed to obtain the imported backend sources.

`patches/algo-defs.patch` is the exact diff from that official commit to the
development commit for these three files:

- `p4spec/lib/pass/algo/algo.ml`
- `p4spec/lib/pass/pass.ml`
- `p4spec/lib/pass/pass.mli`

It adds `Pass.algo_defs`, allowing independent definitions to survive when
another definition's directional conversion fails. It makes no other
frontend or interpreter changes. The build applies this patch to its private
copy under `../build/translator/p4-spectec/`; the official submodule stays unchanged.

`patches/extern-singleton.patch` changes the copied Lean backend's ordered
translation of `extern syntax` to independent inductive types with the single
nullary constructor `mk`. It also permits arbitrary external type names in that
mode. The declarative backend retains its imported external-type model. The build
copies `src/` before applying patches so backend adaptations, like frontend
patches, affect only the disposable build tree.

`patches/shared-spec-extension.patch` adds ordered helper extensions over an
imported specification module. It reuses the base runtime and inlines acyclic
authored helper plans, preserving failure, abort, and fresh-value supply. The
maintained native extension regressions compare these outcomes with a combined
translation. This patch also applies only to the copied backend.

`patches/wasm-lsl.patch` adds the Wasm `$lsl_(int, int) : int` builtin to the
copied native dispatcher and Lean backend. The native implementation is copied
from `kaist-plrg/wasm-ntt` revision
`4773b2b7abe56e61f279ec2340ac0d3c836b5033`,
`p4spec/lib/interface/builtin/numerics.ml`. Its shift count is clamped to
`[0, 4096]`: nonpositive counts leave the value unchanged, and larger positive
counts use 4096. The Lean definition preserves that behavior, including negative
base values and counts outside machine-integer range. This is the imported
implementation's bounded operation, not an unrestricted mathematical shift.

`tests/` retains 33 unchanged files from the development commit's
`p4spec/test/backend-lean/`: three CLI regression suites, the case-corpus
verification helper, and their required small specifications, programs, and
Lean proofs. The large P4 oracle corpus and the original Dune test alias are
not included. These regression suites run without the P4C submodule.
Maintained integration tests and fixtures live in `../scripts/tests/`. The native
helpers under `bridge/` and the Python toolchain driver at `../scripts/toolchain.py`
are maintained by this repository.
These files are outside the imported checksums.

`SHA256SUMS` records every imported backend file, test file, and the original
`LICENSE`. Check the imported bytes from this directory with:

```sh
sha256sum --check SHA256SUMS
```

The imported code and tests retain their original Apache-2.0 license. The
complete original license and attribution are in `LICENSE`. The imported backend
and original regression files have no local edits. The native `bridge/` helpers,
Python drivers and additional integration tests are maintained by this repository.
The backend's original README is retained in `src/README.md`;
its command paths describe the original P4-SpecTec checkout.

`patches/wasm-native-builtins.patch` imports the Wasm numeric implementation from
[kaist-plrg/wasm-ntt](https://github.com/kaist-plrg/wasm-ntt) revision
`4773b2b7abe56e61f279ec2340ac0d3c836b5033`. The numeric dependency closure contains
23 interpreter modules (34 `.ml`/`.mli` files), all unchanged, plus the donor's
numeric builtin registrations and value conversion hooks. The numeric library's
Apache-2.0 `LICENSE` is retained in the patch. The donor root license is also
Apache-2.0; source and integrated hashes, exact paths, and local adaptations are
recorded in `WASM_NATIVE_PROVENANCE.json`.

The donor uses array-backed SpecTec lists. The copied bridge instead uses a
small immutable-list compatibility module matching this repository's pinned
runtime, with three explicit source adaptations in `nats.ml`, `wrap.ml`, and
`construct.ml`. Dune builds only the numeric library and hook library; upstream
CLI, JavaScript, and test targets are omitted. `property_exec.ml` initializes the
hooks before interpreting property expressions. These additions provide native
builtin execution, and do not constitute Lean proofs or property certificates.

`patches/wasm-generic-sets.patch` replaces the text-only set restriction with
structural comparison keys. Their tags, notation ordering, tuple layout, and
record ordering follow the pinned AL runtime's `Value.compare`; generic calls
carry the required comparison dictionaries. `patches/wasm-structures.patch`
adds parameterized structures, preserves explicitly declared empty syntax
types, and translates nested list/record updates with their bounds checks.

`patches/wasm-scalar-builtins.patch` supplies 42 scalar and byte operations.
`patches/wasm-zz-execution.patch` supplies 31 numeric, SIMD, and memory operations.
The Lean implementations follow the donor numeric library cited above. Floating
point operations use integer bit patterns and exact rational rounding, including
the donor's intermediate binary64 rounding for binary32 arithmetic and its NaN
selection. They do not use host float primitives or compiler substitutions.
Partial builtin helpers return `Option`; the ordered translation preserves
native builtin errors as aborts and keeps numeric traps as explicit `NumTrap`
results. These implementations remain subject to the normal proof, generator,
dependency, and executable audits.

`patches/wasm-zz-identifiers.patch` quotes the Lean keywords `mut`, `catch`, and
`local`.
`patches/wasm-zzz-specialization.patch` specializes fixed named callback inputs
that participate in recursive dependency groups, such as `$free_instr` passed
to `$free_list`. It retains the generic declarations, clause order, guards,
and premises, and recomputes typeclass requirements for the specialized
definitions. Nonuniform recursive instantiation is rejected explicitly.
The metadata bridge instantiates parameterized record fields before deriving
JSON transport for closed input types, including Wasm's `memop<A,B>`.

`patches/wasm-zzzz-nested-equality.patch` prints the recursive datatype equality
decision as two nested constructor matches. It retains the field comparisons,
constructor-index guard, and impossible-case proofs, while avoiding one flat
match with a quadratic number of alternatives that exceeds Lean's elaborator
recursion limit for Wasm's 95-constructor `instr` type.

`patches/wasm-zzzzz-comparison-arguments.patch` normalizes runtime dictionary
type aliases before compiling ordered clauses, as the declarative ordering
pass already does. Explicit comparison dictionaries use `inferInstance` for
primitive and parameter types instead of unsolved named-argument placeholders.
The metadata bridge orders JSON codec derivations by type dependency components,
so external dependencies of mutually recursive Wasm types are derived first.
