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
definitions, axioms, or other declarations are accepted. The only candidate
commands are `Inductive`, `Require Import`, `Import` of `ListNotations` or
`StringNotations`, and `Open Scope` for `bool_scope`, `list_scope`,
`string_scope`, or `nat_scope`. Imports are limited to the fixed
`Specification.cedar.Spec` and `Property.Original`, earlier candidate
modules in the selected prefix, and the standard data libraries `Bool`,
`List`, `String`, and `Coq.Init.Datatypes` (including their fully qualified
Coq names). `From ... Require Import` is accepted when it resolves to one
of those modules. Importing QuickChick or another arbitrary module is
rejected because it can change the available generation instances.

Hints, instance declarations, options, tactics, notations, and other
vernacular commands are rejected, including `Remove Hints` and
`Existing Instance`, even when they create no declaration in Coq's `.glob`
file. This keeps the benchmark support policy fixed. For each new
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
the local Coq switch, and inspects every candidate in that prefix. The
command check is followed by Coq compilation, declaration inspection,
elaborated `Print` output, and type probes. Coq may abbreviate a verified
predecessor's relation in `Print` output, so the gate asks Coq to resolve each
printed global head and compares its full inductive identity with the permitted
declarations. A name bound earlier in the constructor is treated as local;
its type probe must show that it is data rather than a logical premise.
Source text alone does not establish a valid relation. The gate does not need
any `Equivalence.v` in that prefix and does
not derive a generator. The existing `scripts/check.py` checks the completed
equivalence chain after proof; the benchmark performs actual automatic
generator derivation.
