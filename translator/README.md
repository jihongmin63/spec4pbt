# SpecTec to Lean translator

This directory contains the OCaml translation backend and its Lean execution
support. The parser, elaborator, and interpreter libraries come from the
official P4-SpecTec submodule in `external/p4-spectec`. The repository build
combines these sources in an ignored directory and leaves the submodule
unchanged. No prebuilt Docker translator is required.

Follow the dependency installation and build instructions in the
[repository README](../README.md). `scripts/build-translator` builds the
translator and observation metadata helper from the checked-out sources.
The resulting translator executable is:

```text
translator/_build/p4-spectec/_build/default/p4spec/lib/lean-skeleton/main.exe
```

From the repository root, translate a specification with the command wrapper:

```sh
scripts/translate-spec specifications/p4record/spec.watsup
```

The wrapper resolves the locally built executable and forwards its arguments.
The executable also supports declarative relations, executable plans, modular
output, and case export. The retained [backend README](src/README.md) explains
their semantics and flags; substitute `scripts/translate-spec` for its original
executable paths.

To run the imported regressions from the repository root after building, use
the repository's pinned Lean toolchain:

```sh
export ELAN_TOOLCHAIN="$(cat lean-toolchain)"
python3 translator/tests/check_direct_relations.py \
  --exe translator/_build/p4-spectec/_build/default/p4spec/lib/lean-skeleton/main.exe
python3 translator/tests/check_ordered_relations.py \
  --exe translator/_build/p4-spectec/_build/default/p4spec/lib/lean-skeleton/main.exe
python3 translator/tests/check_case_corpus.py \
  --exe translator/_build/p4-spectec/_build/default/p4spec/lib/lean-skeleton/main.exe
```

[PROVENANCE.md](PROVENANCE.md) records the source revisions, compatibility patch,
license, and imported-file checksums.
