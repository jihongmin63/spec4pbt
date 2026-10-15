# P4 SpecTec Lean specification

These modules are the ordered Lean 4 translation of `spec/` in the
`p4-spectec` repository, branch `il-to-lean4-fresh`, commit
`d150aa6e53e3f572bc4b02299c05d6d6cee9d6c0`.

The source was generated in the `dev` container with:

```sh
_build/default/p4spec/lib/lean-skeleton/main.exe \
  --emit-modules /tmp/p4-spectec-lean-export spec
```

`SpecTecAll.lean` is the import entry point. The generated modules require
Lean 4.34.1 and compile in this order: `SpecTecCore`, `SpecTecSupport`, the
numbered `SpecTecDecl` modules, `SpecTecAll`, `SpecTecProofs`, and
`SpecTecCases`. Set `LEAN_PATH` to this directory when importing them.

`SpecTecCases.lean` contains no P4 test case propositions; those are exported
separately by the upstream corpus exporter.
