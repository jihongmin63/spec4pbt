# Cedar candidate shape gate

Run before asking the prover for `Equivalence.v`:

```sh
python3 scripts/cedar/syntax.py PROPERTY_ROOT \
  --candidate v001 --evidence-dir PROPERTY_ROOT/.runs/attempt-001/syntax
```

The evidence directory must be new. `--env-script PATH` selects the installed
Coq 8.20.0 / OCaml 4.14.2 launcher when the script is run from an isolated
source copy. Exit status 0 means `result.json` has `"status": "passed"`;
otherwise it has `"status": "failed"` and an `error`. The CLI prints the
absolute report path. Source snapshots, compilation logs, elaborated `Print`
output, and individual type probes remain in that directory.

`Candidate.v` must declare one `predicate : Original.Input -> Prop` as an
`Inductive`, and may declare additional Prop-valued inductive helpers. No new
definitions, axioms, or other declarations are accepted. For each new
constructor, data binders may carry values and witnesses. A logical premise
must elaborate to an application of a fixed `Specification.cedar.Spec`
inductive relation, a verified predecessor relation, or one of the new
inductive relations. New equality,
Boolean/function checks, implication/conjunction, higher-order premises,
and nested `forall`, `match`, or `if` are rejected. Multiple premises express
conjunction; multiple constructors express disjunction. Fixed Spec
constructors are compiled but not subjected to the new grammar.

The gate snapshots the fixed repository specification, checks the staged
`Original.v` byte-for-byte against the fixed repository original, copies
`Candidate.v` files through the selected candidate, compiles them with
the local Coq switch, and inspects every candidate in that prefix. It does
not need any `Equivalence.v` in that prefix and does
not derive a generator. The existing `scripts/check.py` checks the completed
equivalence chain after proof; the benchmark performs actual automatic
generator derivation.
