Wasm builtin regressions use Coq 8.20 through `environment/env.sh`. They leave
source snapshots, compiled files, native binaries, hashes and logs under the
target-owned ignored `_opam-testing-theorems/checks/` directory.

Run the arithmetic, native opcode comparison and boundary regressions with:

```
python3 -B translator/tests/builtins/wasm/run.py
```

The native oracle extracts the exact recorded donor git object and verifies
patch hashes before compiling its unchanged numeric modules. Generated Coq
proofs compare exact integer bit patterns, including NaN payloads, signed zero,
rounding, conversions, and every direct lane opcode branch in native eval_vec.
The finite native samples are regression evidence, not a semantic equivalence
proof or generator correctness proof.

Check all 74 Wasm-specific typed AL adapters against the actual full 18-file
specification using a previously prepared pinned frontend source build:

```
python3 -B translator/tests/builtins/wasm/wrappers.py \
  --frontend-build _opam-testing-theorems/build/al-to-coq-durebzgo/source
```

The wrapper check copies that build and never modifies it. It compiles the
complete source datatypes, all builtin adapters, and execution examples through
the adapters. It also rejects profile, declaration-kind and signature mismatch.
The other two Wasm builtins, union_set and diff_set, use the shared set adapter.
This isolated check does not replace the complete specification translation.

The pure numeric support uses binary `Z` internally; source aliases remain `nat`
at the generated boundary. This preserves typing and values but evaluating huge
unary source naturals inside Coq can consume substantial resources. Allocation
failure is not modeled as a successful native result.

Source and license provenance are in PROVENANCE.json and LICENSE. The explicit
I32 ExtendS Pack64 branch preserves the observed pinned OCaml host behavior;
that source operation supplies an out-of-range negative native shift count,
whose behavior OCaml leaves unspecified across implementations.
