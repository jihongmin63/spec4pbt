# Independent SpecTecX to Lean translator

This executable parses and elaborates native SpecTecX with the pinned upstream
`spectec.pass` library, checks a small local IR, and emits typed Lean data,
ordered execution plans and a manifest. It has no P4 frontend dependency.

From the repository root, after installing the pinned core package:

```sh
opam exec --switch=spectecx -- dune build --root translator
lake build pbt.SpectecRuntime.RunEval
translator/_build/default/main.exe --namespace AeSpec \
  --output /tmp/AeSpec.lean --manifest /tmp/AeSpec.json \
  external/spectecx/spectec/specs/itpl/ae/spec.spectec
lake env lean /tmp/AeSpec.lean
python3 -m unittest discover -s translator/tests -v
```

Both output paths must be fresh and distinct. Unsupported source constructs
exit nonzero before either output is created. Parse/elaboration errors retain
upstream diagnostics. `SPEC...` files are concatenated in argument order.

Generated `Namespace.Relation` declarations are propositions with arguments in
original source order. `Namespace.runRelation fuel inputs...` executes with
fuel; zero outputs use `Unit`, one uses its type directly, and multiple outputs
use right-associated products. An outcome is success, unmatch or abort; fuel
exhaustion and unavailable primitives are separate incomplete results.
The generated relation uses the donor's unbounded `Eval` semantics. A successful
fuel-bounded execution establishes that relation through `runEval_sound`.
This is a theorem about emitted programs, not a formal proof that this OCaml
translator preserves all source semantics.

Variant constructors are `c0`, `c1`, etc., in source order. For native AE,
`expr.c0 n` is `_NUM n`, `expr.c1 a b` is addition, and `expr.c2 a b` is
subtraction. Types derive `DecidableEq`, `Repr`, `Lean.ToJson` and
`Lean.FromJson`. JSON uses Lean's derived codec schema. Recursive JSON parsers
are executable but need not reduce in the kernel; codec tests execute them.
Manifest v1 records exact Lean identifiers, source type and field names,
relation slots and input indices. Plain aliases have
`{"kind":"alias","lean":"Namespace.name","type":"target_key"}`.
Safe source identifiers are retained; reserved/unsafe identifiers and names
starting `s_` use an injective `s_` plus UTF-8-byte hexadecimal encoding.

Supported fragment:

- Monomorphic `bool`, `nat`, `int`, `text`, source-order aliases and records,
  and directly recursive variants. Record fields and constructor arguments
  use supported monomorphic types.
- Literals, variables, record construction/projection, variant construction
  and pattern guards, elaborated binding premises, relation calls including
  recursive and mutually recursive calls, ordinary conditions and `otherwise`.
- Integer addition/subtraction/multiplication; natural addition/multiplication;
  numeric unary plus/minus, natural-to-integer casts; Boolean negation, and/or;
  equality/inequality and numeric comparisons.
- Rules retain source order within the ordinary and fallback groups; all
  ordinary rules precede all fallback rules, matching upstream IL execution.
  Failed conditions and applicability guards both backtrack. Their diagnostic
  trace distinction is not represented. Failed recursive calls backtrack;
  abort and incomplete execution never select a fallback.

Explicitly unsupported: polymorphism; functions and builtins; tuples/options/
lists as source types; iteration and relation assertions; debugging premises;
subtype membership checks and downcasts; mutually recursive type declarations and forward
references; natural subtraction, division, modulo and exponentiation. These
numeric operators have partial source semantics that must not be replaced by
Lean's total arithmetic. Generated declaration-name collisions are rejected.

Runtime files and proof provenance are documented in
`pbt/SpectecRuntime/PROVENANCE.md`. The tests' independent `reference.exe` loads
native source and invokes upstream `Eval_il.run` with an empty target; it never
imports translator code. Tests compare expected values against upstream IL
and Lean, and exercise record JSON, recursive variant JSON, ordered overlapping
rules, fallback declared before ordinary rules, recursive failure, fuel,
abort, unsupported primitives and rejection without writes.
