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
copy under `_build/p4-spectec/`; the official submodule stays unchanged.

`tests/` contains 33 unchanged files from the development commit's
`p4spec/test/backend-lean/`: three CLI regression suites, the case-corpus
verification helper, and their required small specifications, programs, and
Lean proofs. The large P4 oracle corpus and the original Dune test alias are
not included. These regression suites run without the P4C submodule.

`SHA256SUMS` records every imported backend file, test file, and the original
`LICENSE`. Check the imported bytes from this directory with:

```sh
sha256sum --check SHA256SUMS
```

The imported code and tests retain their original Apache-2.0 license. The
complete original license and attribution are in `LICENSE`. Backend and test
sources have no local edits; integration code outside `src/` is maintained by
this repository. The backend's original README is retained in `src/README.md`;
its command paths describe the original P4-SpecTec checkout.
