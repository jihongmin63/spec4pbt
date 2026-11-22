# Fixed specification profiles

`p4.json` and `wasm.json` use schema version 1. Paths are relative to this
worktree root, never the current shell directory. `frontend.source_root` names
an independent, unpatched source snapshot extracted by `git archive` under
`_opam-testing-theorems/sources/`; it is not another worktree or a symlink.
`frontend.revision` fixes the frontend; `source` fixes each language input.

`inputs` is the complete, ordered list of `.watsup` inputs with SHA-256 hashes.
The order matches `Util.Filesys.collect_files`: bytewise sorted recursive
traversal, excluding directories named `include`. Pass this list unchanged to
`Pass.algo`; its original `Frontend.Parse.parse_files` preserves explicit file
order. Verify input hashes before invoking the frontend.

`builtin_inventory` records static source declaration lines, not elaborated AL
signatures or implemented Coq mappings. `builtin_bindings` now records the
validated actual AL signatures and concrete implementations for all 47 P4 or
76 Wasm declarations.
Dispatch must distinguish declaration kind and profile as well as name.
`validation` records only checks that have been performed. Source counts and
source hashes are not evidence of AL conversion or Coq generation.

To restore the P4 snapshot without using a mutable reference checkout, run
`git archive --format=tar 2730cfd9e74048bb5439da0f8afcef124079a064` in an
object database containing the pinned P4-SpecTec commit and extract into the
profile's source_root. The profile records the resulting archive SHA-256.
`git archive` preserves internal symlinks and does not materialize the unrelated
`p4c` submodule. Build only another target-owned copy under the ignored build
directory. The original snapshot must remain byte-identical to the archive.

The complete Wasm import is tracked under `specification/wasm/source/` with its
original LICENSE, SHA256SUMS, upstream.json, README.md and observations.toml.
`source/PROVENANCE.md` explains the donor layout and pinned import.

Successful full checks record `publication.managed_files` hashes and the verified
run in each profile. Only final .v sources are published; compiled artifacts
and evidence remain under the ignored state. The final acceptance index is
`_opam-testing-theorems/logs/al-to-coq-final-report.json`.
