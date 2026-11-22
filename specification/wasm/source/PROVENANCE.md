# Fixed Wasm source import

This directory preserves the complete `specifications/wasm/` tree from repository
commit `16142ff23b30611a3fba1bb0ceb0dd7928187d58`, extracted from its git object.
The 18 `spec/*.watsup` files, LICENSE, SHA256SUMS, README.md, observations.toml,
and upstream.json are byte-for-byte copies. `README.md` is the retained donor
document; its relative paths describe that donor layout.

Upstream is https://github.com/kaist-plrg/wasm-ntt.git revision
`4773b2b7abe56e61f279ec2340ac0d3c836b5033`, directory `spec-wasm/`.
The upstream root license is preserved in LICENSE. upstream.json records the
original import date and no source modifications. No Lean or frontend patches
are applied to these files.

Run `sha256sum --check SHA256SUMS` from this directory to verify the specification
and license. The ordered translation inputs and individual hashes are recorded
in `translator/profiles/wasm.json`, relative to the repository root.

This source import is not evidence of successful AL conversion or Coq generation.
