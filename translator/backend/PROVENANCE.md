# Lean backend provenance

The core OCaml backend files were ported from
`implementations/p4-spectec/p4spec/lib/lean-skeleton` at donor commit `d150aa6e53e3f572bc4b02299c05d6d6cee9d6c0`.
The retained code includes the Lean AST, translator, dependency ordering,
printer, builtins, relation builtins, external model descriptions, and ordered
execution lowering. The donor project is distributed under Apache-2.0;
its license is retained as `LICENSE`.

`legacy_il.ml`, `legacy_atom.ml`, and `legacy_mixfix.ml` retain the backend input
shape from the donor. JSON serialization and the donor parser, elaborator,
interpreter, P4 frontend, and runtime are excluded. Small compatibility modules
provide source locations, presentation hints and diagnostics. The public adapter
converts validated current SpecTecX IL to these local compatibility types.

The execution lowering accepts already directionalized clauses from the current
SpecTecX pipeline. It does not invoke the donor AL pass. Generated output imports
`pbt.SpectecRuntime.RunEval` for the checked shared execution semantics.

Port adaptations also parameterize the emitted namespace, import shared printing
support, and scope external type classes to each generated namespace. Arithmetic
matches the pinned current SpecTecX interpreter: natural subtraction checks for
underflow; division requires a nonzero divisor and an exact quotient. List
indexing checks bounds before extracting a value, so an invalid index aborts
without selecting a fallback rule. Ordered
execution represents arithmetic failure as abort; declarative emission retains
these requirements as premises.

Builtin implementations retain the donor's explicitly selected profile. Native
SpecTecX builtin declarations specify signatures, not implementations. The public
adapter therefore requires an explicit donor profile before using these bodies;
they do not establish equivalence with a different target's builtin registry.
Builtin signatures are checked before emission, including type parameters,
argument types and result types. Unsupported signatures produce diagnostics.
