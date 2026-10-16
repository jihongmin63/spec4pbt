# Independent SpecTecX to Lean translator

This executable parses and elaborates native SpecTecX with the pinned upstream
`spectec.pass` library. It has two backend paths during the migration:

| Backend | Output | Purpose |
| --- | --- | --- |
| `observation` (default) | Lean + manifest v1 + JSON codecs | Existing certified observation/PBT workflow, with the smaller fragment below |
| `ported` | Lean using the imported backend's declarations | Broader SpecTecX translation; observation manifests/codecs are not connected yet |

Neither path depends on the P4 frontend or accepts the old P4 dialect as a
separate input language. The official SpecTecX submodule remains unchanged.

## Ported backend

`backend/` contains the donor Lean AST, expression/function translation,
dependency/SCC ordering, printer and ordered execution lowering. This is a port
of those modules, rather than an extension of the small observation IR.
`current_adapter.ml` converts current typed IL into a backend-local compatibility
model. It uses the bindings already elaborated by SpecTecX and reconstructs
iteration/subtype metadata; it never runs the old AL pass.
See [backend provenance](backend/PROVENANCE.md) for the donor revision and changes.

```sh
scripts/build-translator
lake build
translator/_build/default/main.exe --backend ported --namespace PortedExample \
  --output /tmp/PortedExample.lean \
  translator/tests/fixtures/ported-functions.spectec
lake env lean /tmp/PortedExample.lean
python3 -m unittest discover -s translator/tests -v
```

The default ported output is executable ordered semantics. For example, evaluate
`SpecTecCall.Compute` from that fixture with:

```lean
open PortedExample SpecTecExecution
example : runEval specTecExecutableProgram (PrimitiveRunner.unavailable _) 500
    (.call (SpecTecCall.Compute 8)) 0 = .done (.success 9) 0 := by decide
```

Use `--noncomputable` for ordered logical plans without an executable evaluator,
or `--declarative` for inductive relation declarations. These modes are exclusive.
Declarative output rejects `otherwise`, as the donor declarative semantics does
not model ordered fallback. Some normalized execution constructs also require
the ordered mode. All destinations must be fresh; `--manifest` is rejected for
the ported path before writing either artifact.

The integration suite checks emitted Lean and compares native executions against
the pinned upstream interpreter for:

- Lists, options and tuples; constructors, concatenation, length and record data.
- Polymorphic types/functions, higher-order function parameters, calls and forward
  dependencies; mutually recursive datatypes with executable equality.
- List/optional expression and premise iteration, output binding, and mismatched
  iteration shapes.
- Numeric/variant subtype membership and narrowing through lists, options and tuples.
- Relation assertions (`holds` / `does not hold`), ordered rules and fallback.
- Boolean implication/equivalence and arithmetic, including partial natural
  subtraction, exact division and bounds checks for list indexing/slicing/updates.

Invalid arithmetic and out-of-bounds list operations abort instead of selecting
an `otherwise` rule. The upstream arithmetic implementation can raise an OCaml
assertion on undefined operands; the port represents this as an explicit abort.
This is tested as an error outcome, not successful computation or backtracking.

Builtin declarations supply signatures, not implementations. By default the
ported backend rejects them. `--builtin-profile donor` explicitly selects the
donor's builtin implementations and signature checks; it does not assert that an
arbitrary SpecTecX target, or the current P4 target, uses those meanings. The
tests check selected builtins directly in Lean, not against the target-free oracle.
The `bits` family additionally requires the representation `bits = bool*`.

Remaining boundaries include donor-unsupported power expressions, polymorphic
function parameters (ordinary polymorphic functions work), some nested update
paths and mutual declaration shapes, and erased standalone function-value types.
Text length/concatenation and valid UTF-8 literals work, but invalid UTF-8 byte
literals and byte indexing/slicing/update are rejected:
SpecTecX can produce an invalid UTF-8 byte fragment that Lean `String` cannot
represent. Composite values, update replacements, function arguments and return
values whose negated natural operands disagree with their IL type annotations are
also rejected; explicit integer casts avoid that ambiguity. Scalar subtype checks
use the actual numeric runtime type, including negated naturals.
Unsupported cases are diagnostics, never replacement axioms or dummy results.
Broad translation support does not yet imply broad observation/JSON support.

## Observation backend

The existing default path checks a small local IR and emits typed Lean data,
ordered execution plans and a manifest.

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

Supported observation fragment:

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

Explicitly unsupported in the observation backend: polymorphism; functions and builtins; tuples/options/
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
