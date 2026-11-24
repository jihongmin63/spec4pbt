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

Profiles retain the source revisions, ordered input hashes and authored execution
policy. Derived inventories, validated AL signatures, builtin mappings and stage
results are recorded in ignored run manifests and `profile-results.json`.
Generation never rewrites these input profiles. Dispatch must distinguish the
source declaration kind and profile as well as its name.

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

Successful full checks record managed output hashes in
`_opam-testing-theorems/publication/<profile>.json`. This local registry lets the
driver archive previous managed bytes before replacement and reject unrelated
files. New checkouts start without a registry and regenerate ignored `Spec.v`
and `Generated/` sources. Compilation and run evidence remain in ignored state.
