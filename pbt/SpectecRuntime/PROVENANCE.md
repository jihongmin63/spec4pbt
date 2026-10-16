# Donor runtime

`Execution.lean` and `RunEval.lean` are copied from
`implementations/p4-spectec/p4spec/lib/lean-skeleton/lean/SpecTecExecution.lean`
and `SpecTecRunEval.lean` at donor commit
`d150aa6e53e3f572bc4b02299c05d6d6cee9d6c0`.
The only initial adaptation is an import of `pbt.SpectecRuntime.Execution`
in `RunEval.lean`. The accompanying Apache-2.0 LICENSE is copied from the donor.

The independent translator uses the donor's typed executable plans, ordered
fallback, semantic outcomes, fuel-bounded interpreter and proved soundness
refinement. It does not use the donor's P4 parser or its obsolete AL adapter.

`Printing.lean` is extracted from the donor backend's `printer.ml` prelude.
It provides the shared `SpecTecPrint` instances, concrete rendering helpers,
and string-set primitives. Generated modules import this module instead of
redeclaring its global definitions, so separate generated namespaces coexist.
