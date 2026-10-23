# Translator provenance

The Lean backend in `src/` was imported byte for byte from the development
checkout of P4-SpecTec at commit
`8003aba7af8331dfb34f3d20a24f288e8dd2c062`. That checkout originated from
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

The imported backend's ordered translation already represents each
`extern syntax` declaration as an independent inductive type with the single
nullary constructor `mk`, so no external-type patch is needed. The build copies
`src/` before applying patches so backend adaptations, like frontend patches,
affect only the disposable build tree.

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

`tests/` retains 36 unchanged files from the development commit's
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
