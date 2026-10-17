# Lean Skeleton

The default translation preserves SpecTec's sequential clause execution. Each
relation or function supplies a clause list to the shared Lean library
[`SpecTecExecution.lean`](lean/SpecTecExecution.lean). Only `unmatch` moves to
the next clause; success selects its result and abort stops the call.
`otherwise` is appended as the final clause. Earlier relation premises are
never negated to implement fallback.

`execution_translate.ml` uses AL binding and guard analysis, translates input
patterns and premises in execution order, and computes outputs last. It
reuses `translator.ml` for data, expressions and builtin definitions. Tables
check each row's own pattern coverage, so a failing row result can reach a
later wildcard row. `execution_ir.ml` records original input positions and
output types. Noncontiguous inputs, multiple outputs and predicates with no
outputs retain their public argument order and arity.

AL binding analysis turns a pattern of a subtype into a subtype guard followed
by a downcast. The downcast follows the interpreter's recursion through tuples,
lists and options. Unchanged components are copied, integers use `Int.toNat?`,
and each variant component uses a generated helper that rebuilds the target's
cases and returns `none` for the others. A value outside the subtype therefore
yields `unmatch` and can reach a later clause.

Generated `SpecTecCall O` constructors contain only inputs, and their output
index also checks higher-order callback types. Recursive calls are request
nodes in `Plan`, interpreted by the common inductive `Eval`; clause functions
do not recurse in Lean. A public `R inputs outputs : Prop` means that the call
has a finite `Eval` derivation from fresh supply zero with those outputs,
existentially hiding the final supply. Changing the requested
outputs cannot make the callee retry a later clause. Data values such as
`FAIL`, `false` and `none` remain successful results.

In default output, the transparent execution definitions are `noncomputable`
because the native Lean runtime cannot compile a single call datatype with this
many constructors. Their kernel definitions remain available to proofs.
`--executable` additionally supports native execution for specifications within
the runtime's limits, using the typed refinement in
[`SpecTecRunEval.lean`](lean/SpecTecRunEval.lean); see
[Executable plans and soundness](#executable-plans-and-soundness).

`Eval` supplies execution
constructors, `firstSuccess_success_iff` identifies the selected clause,
`firstSuccess_unmatch_iff` characterizes independent `AllUnmatch` attempts,
and `eval_deterministic` proves outcome and final-supply uniqueness for the same
initial supply, assuming deterministic primitive
executions. A divergent call has neither a success nor an `unmatch` derivation,
and consequently supplies no evidence for selecting fallback.

Extern relations and functions expose an unconditional inductive relation:
the `allowed` constructor admits every combination of well-typed arguments,
including every output. They require no execution model or validity predicates.
`SpecTecExternTypes` supplies the external types and equality instances only.
Regular clause calls use a fixed primitive bridge that admits typed successes
through the extern relation and excludes `unmatch` and abort. This abstraction
does not select a particular output or supply a concrete external runner. It
admits multiple outputs for the same input, so primitive determinism and global
result uniqueness cannot generally be established. A caller may reach fallback
after its own output pattern or guard rejects a successful extern output.
An empty output type supplies no value to return; totality requires inhabited
output types.

Named clause definitions let the generated clause lists and proofs refer to
each clause. Pattern/iteration helpers handle intermediate bindings and nested
calls. These names are generated implementation details; the original public
relation retains exactly its original data arguments. Intermediate values
remain local to its execution derivation, although helper definitions and
their signatures are visible in the generated Lean source. Naming a clause
separately is a convenience; it could instead be an anonymous list entry.

Failed builtin adapters distinguish caught `BuiltinError` from uncaught host
exceptions; the latter become abort with normalized messages. Abort also
preserves runtime errors in partial operations, independently of externs:
an invalid slice or division by zero stops execution rather than selecting
the next clause. Only matching failure (`unmatch`) permits fallback.

`--relation-semantics declarative` retains the previous inductive API, including
its source-located rejection of `otherwise`. Existing constructor/cases/induction
proofs can use this mode while migrating to `Eval` proofs. Ordinary relation
names, argument order and notation are preserved in ordered mode. Function
parameters now accept typed call builders rather than arbitrary propositions.
Declarative mode retains its previous extern validity models and supported
extern-name restrictions. Ordered mode accepts external function/relation
signatures without those restrictions. The entire generated call graph uses
the selected mode.

Ordered mode supports `$fresh_typeId` through the shared fresh supply described
below. Declarative mode continues to reject it. Nominal name representations
and WFS are outside this backend.
`--keep-going` reports only the first unsupported construct of each definition
and removes that definition with its helpers and callers before creating the
global program, so a caller's diagnostic names the missing dependency. It never
replaces an omitted callee
with a failing plan. Operation preconditions (slice/update bounds, replacement
size and division by zero) propagate abort; matching guards still produce
`unmatch`. Text
operations retain the backend's valid UTF-8 fragment. An in-bounds source byte
operation can succeed with an invalid UTF-8 result that Lean `String` cannot
represent. The adapter explicitly aborts with `text result is not valid UTF-8`
in that unsupported case, preserving the fact that fallback cannot be chosen.
It does not claim an equivalent successful output outside this fragment.

`main.ml` owns CLI behavior, `pipeline.ml` selects the translation mode,
`order.ml` validates dependency graphs, and `printer.ml` renders data and the
compatibility API. Recursive negative calls retain the existing rejection
policy. The canonical execution library is checked independently and embedded
by Dune once in standalone output or `SpecTecCore`.

## Fresh supply and compositional proofs

`Eval program plan initial outcome final` connects fresh supplies in the common
execution relation. `Plan.freshId` returns the string `FRESH__n` and advances
`n` to `n + 1`. Calls inherit the current supply; bind starts its continuation
at the preceding execution's final supply. A failed alternative records its
consumed supply in its own derivation, but fallback retries from the choice's
original supply. Negated calls retain allocations in their own outcome, and an
abort commits its allocations because it does not select fallback.
`supply_monotone` proves that execution cannot decrease the supply. Extern
primitives preserve this supply and retain their original unconditional public
API.

Requests and clauses have no supply parameters. The translator validates
`$fresh_typeId` as a zero-input, non-polymorphic builtin with text output
(including aliases such as `typeId`), and lowers it to a typed request whose
body is `.freshId`. Ordinary functions with the same name keep their source
body. Recursive `$fresh_typeIds`, repeated calls inside iterations, and regular
callbacks that call fresh all use the usual request/bind lowering. Direct
builtin callbacks remain unsupported: AL/SL invoke a rebound builtin using the
local callback name rather than the original builtin name.

Ordered debug premises retain expression evaluation, including fresh calls,
iteration helpers, failure and abort, while discarding the printed value.

A regular public relation has the boundary meaning
`∃ final, Eval specTecProgram (.call request) 0 (.success output) final`.
Nested executions call requests, not public wrappers, so their supplies never
reset at relation boundaries. To compose execution proofs, state the lemmas
using `Eval` with explicit initial and final supplies and connect them with
`Eval.bind_success`. Two public relation proofs from zero are independent runs;
they do not establish execution of the second call at the first call's final
supply. Introduce the existential only after the complete outer execution.
`ordered-fresh-proof.lean` demonstrates a supply-polymorphic internal lemma and
an unchanged public relation signature.

Uniqueness concerns generated names within one run. The runtime's `FRESH__`
prefix policy does not avoid arbitrary input names. Fresh support preserves
that policy; it does not add input-name scanning or an alpha-equivalence
quotient. Existing fixed oracle output terms retain their exact strings.

## Executable plans and soundness

Pass `--executable` with ordered translation to generate
`specTecExecutableProgram`. Its clauses have type
`ExecutablePlan SpecTecCall α`: calls and binds retain their result type,
and guards carry constructive `Decidable` instances. The existing clause names,
`specTecBody`, `specTecProgram`, and public relation predicates remain available
through erasure into `Plan` and `Eval`. Default output and declarative mode keep
their existing representation. The executable option is incompatible with
declarative, obligations-only, corpus export (`--emit-cases`), and oracle modes.
Standalone and `--emit-modules` output use the same execution library.
Executable generic guards add the required `DecidableEq` parameters and pass
them through callers; data argument order is unchanged.

For the generated `ordered-choice.watsup` example:

```lean
namespace SpecTec
open SpecTecExecution

def noPrimitives : PrimitiveRunner specTecExecutableProgram := .unavailable _

#eval runEval specTecExecutableProgram noPrimitives 20
  (.call (SpecTecCall.Caller 7)) 0
-- SpecTecExecution.RunResult.done (SpecTecExecution.Outcome.success 30) 0

example : Caller 7 30 :=
  ⟨0, runEval_sound specTecExecutableProgram noPrimitives 20
    (.call (SpecTecCall.Caller 7)) 0 (.success 30) 0 rfl⟩
end SpecTec
```

`runEval` is a total definition structurally recursive on `Nat` fuel. At zero it
returns `RunResult.outOfFuel`; at a successor each subevaluation receives the
predecessor. Fuel bounds evaluation-tree height, not total instructions or the
work inside a guard, pure function, or primitive implementation. Computational
adapters must themselves terminate. The fresh supply is a separate argument.

`RunResult.done outcome finalSupply` records success, unmatch, or abort.
`unsupportedPrimitive` reports that the primitive runner declined a request.
Neither fuel exhaustion nor a missing primitive selects fallback or counts as
successful negation. Only completed unmatch selects fallback, which retries
from the original supply. Bind and negation preserve the existing supply rules.

Externs remain abstract relations. A `PrimitiveRunner program` provides
`run : {α : Type} → SpecTecCall α → Option (Outcome α)` plus `sound`, proving that
every returned answer satisfies `program.primitive` after packing. `none`
means unavailable, not unmatch. `PrimitiveRunner.unavailable` is sufficient for
programs without executed extern calls. The primitive relation of generated
externs permits typed successes only, so a certified implementation cannot
return semantic unmatch or abort for them.

The shared theorem `runEval_sound` proves:

```lean
runEval program primitives fuel plan start = .done outcome final →
  Eval program.erase plan.erase start outcome.pack final
```

It applies to all completed outcomes, with no determinism assumption and no
new axioms, `sorry`, unsafe casts, or `native_decide` in its proof. Concrete
examples use kernel reduction (`rfl`) for the computation premise.
`runEval_mono` proves that increasing fuel preserves any completed outcome and
final supply. This is soundness relative to the generated `Eval` semantics and
the primitive certificate; it is not a formal verification of the OCaml
translator. Completeness and native execution of the entire P4 specification
are outside this feature. In particular, `--executable` does not remove Lean's
large-constructor-datatype runtime limits. Guard compilation must find an
executable decider; there is no classical fallback.

Run the checked generated example:

```sh
_build/default/p4spec/lib/lean-skeleton/main.exe --executable \
  p4spec/test/backend-lean/ordered-choice.watsup > /tmp/run-eval-example.lean
cat p4spec/test/backend-lean/run-eval-generated-proof.lean >> /tmp/run-eval-example.lean
ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1 lean /tmp/run-eval-example.lean
```

## Modular Lean output

`--emit-modules DIR` writes into a new or empty directory instead of stdout.
The output contains `SpecTecCore`, `SpecTecSupport`, numbered `SpecTecDecl`
modules, and a `SpecTecAll` import entry point. Import `SpecTecCases` for any
requested P4 case propositions. `SpecTecProofs` is a compatibility import;
ordered relations expose the shared `Eval` constructors and induction principle.
Declarative mode retains each relation's original inductive constructors.

`--module-split-bytes N` sets the target declaration bytes per module (default
2,000,000), with at most 32 declaration groups in one module. A mutual group
is never split and may exceed the target. Compile the files with the output
directory on `LEAN_PATH`, in import order: Core, Support, numbered Decl files,
then All, Proofs, and Cases. `--keep-going` can emit supported modules, but
still exits with status 1 if any declarations were rejected. It cannot be
combined with case propositions. Modular output requires translated semantics
and therefore cannot be combined with `--obligations-only` or oracle modes.

## Branch history

`il-to-lean4-fresh` retains the original 13 backend commits through `47cfe700`,
immediately before the WFS implementation. Subsequent commits remove
otherwise splitting, reapply the independent P4 case/oracle tools and all
nine corpus data commits, and adapt extern models and modular output to the
direct inductive API. WFS evaluators, supply/counter threading, fresh-specific
tests, and their proof interfaces were not carried over. The original
`analysis/il-to-lean4` branch remains unchanged.
Ordered execution subsequently adds the shared fresh supply without restoring
per-relation supply parameters or WFS. The optional typed `runEval` refinement
adds fuel-based execution while preserving this relation-based proof API.

Verification on this branch used the installed `spectecx` opam switch and
Lean 4.34.1:

```sh
ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1 opam exec --switch=spectecx -- \
  dune build @backend-lean --profile=release
opam exec --switch=spectecx -- \
  dune build p4spec/bin/main.exe p4spec/bin/boot.exe \
    p4spec/test/lang/test.exe p4spec/test/run/test.exe p4spec/test/sim/test.exe \
    p4spec/test/parse/test.exe p4spec/test/boot/test.exe \
    @speclang @micro --profile=release
```

The backend suite includes 16 declarative compatibility tests, 31 ordered CLI
integration tests, standalone execution proofs, and sequential AL/SL oracle
comparisons. The ordered tests cover first success, callee output mismatch,
normal `FAIL`/`false`/`none` results, recursion, explicit negative calls,
unconditional extern outputs, exclusion of extern failure/abort, runtime errors,
UTF-8 result limitations, higher-order calls, downcasts to instantiated generic
variants and through tuples, lists and options, pruning of whole definitions,
fresh names and consumed supplies across nested calls, recursive lists,
iterations, callback wrappers, transactional failed alternatives, negation,
debug evaluation and abort,
standalone/module output, and executable fuel/soundness tests. The latter cover
native generated calls, recursion, higher-order functions, finite builtin guards,
generic equality propagation, certified polymorphic primitives, and compatibility
with existing execution proofs. Existing tuple,
update, slice, set, table, notation, equality, printer and extern fixtures also
compile in ordered mode.

Run the slower actual-spec integration separately:

```sh
ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1 python3 \
  p4spec/test/backend-lean/verify_ordered_spec.py \
  --exe _build/default/p4spec/lib/lean-skeleton/main.exe --spec spec

_build/default/p4spec/test/backend-lean/ordered_oracle.exe \
  p4spec/test/backend-lean/ordered-choice.watsup \
  p4spec/test/backend-lean/ordered-functions.watsup spec \
  p4c/testdata/p4_16_errors/annotation.p4 p4c/p4include
```

The first command checks the actual supported spec as a standalone file and
an import chain, with proofs for `Cast_expl_neq` returning both `OK` and normal
`FAIL`, and all four `$join_flow` cases. Unsupported declarations remain diagnostics; this does not assert a
complete `Program_ok` proof. The second compares sequential AL/SL clauses and
actual casts, and checks the chosen P4 result against deterministic execution.
Archived corpus answers are never regenerated by these checks.

As root, the existing unreadable-directory language test requires dropping
`CAP_DAC_OVERRIDE` and `CAP_DAC_READ_SEARCH`, using
`setpriv --bounding-set=-dac_override,-dac_read_search` with a fresh build directory.

## P4 type-checking proof obligations

The corpus exporter separates selection (`case_manifest.ml`), translation of
runtime values against declared types (`case_value.ml`), logical targets
(`case_obligation.ml`), and streaming package output (`case_export.ml`).
All cases import one shared ordered semantics tree. Public `Program_ok` starts
from supply zero, so accepted IRs retain their exact `FRESH__n` names.

Generate the full 1,909-case package from the repository root:

```sh
_build/default/p4spec/lib/lean-skeleton/main.exe \
  --emit-cases p4spec/test/backend-lean/generated/typecheck-corpus \
  --manifest p4spec/test/backend-lean/typecheck-cases.tsv \
  -I p4c/p4include spec

ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1 python3 \
  p4spec/test/backend-lean/verify_case_corpus.py \
  --directory p4spec/test/backend-lean/generated/typecheck-corpus --jobs 4
```

The destination must be absent or empty. Generation publishes the directory
only after every selected case succeeds. The package contains:

- `semantics/`: the shared `SpecTecAll` import tree.
- `cases/CaseNNNNData.lean`: parsed P4 input and, for accepted cases, the full
  fixed IR value. These transparent `noncomputable def` values still reduce in
  kernel proofs; they skip runtime code generation for large data constants.
  Only one case is materialized at a time during export.
- `cases/CaseNNNN.lean`: a short, independently importable `case_N : Prop`.
- `index.md`: all original sources, data/goal links and the exact logical target.
- `index.tsv`: the same selection with stable IDs, oracle paths and goal kinds.
- `checks.json` and `checks.md`: per-case declaration checks from the verifier.

Use `--case-range START COUNT` to export a subset while retaining its global
IDs. An accepted target asserts both `Program_ok input expected` and uniqueness
of every successful output. A rejected target is
`¬ (∃ output : p4programIR, Program_ok input output)`; it does not require an
operational `.unmatch` derivation. `abort-reject` keeps that negative conjecture
and is labelled `rejection-conjecture`, because an observed interpreter abort
does not establish rejection in the Lean extern semantics.

The verifier compiles shared modules first, then each data/goal pair, in a fresh
temporary directory. Its imports cannot use package caches or the caller's
`LEAN_PATH`, and it removes its temporary compiled files afterwards. Each run
replaces earlier reports with an in-progress record before validation and
records failures, including missing sources and compiler launch errors. It
reports ill-typed data separately from an ill-typed proposition. Successful
checking validates declarations; it does not prove the 1,909 propositions.
Generated bulk files stay in the Git-ignored `generated/` directory. To compile
modules for later imports, follow the import-order instructions above with both
`semantics/` and `cases/` on `LEAN_PATH`.
The older `--case`, `--reject-case`, `--manifest`, `--obligations-only` and
`--emit-modules` forms remain clients of the same translation/goal units.

The executable also parses P4 files with the repository's P4 parser and turns
each parsed `p4program` value into a Lean term. The term is translated using the
constructor signatures of the elaborated SpecTec IL, including the parser's
internal list nodes whose runtime type annotations differ from the declared
SpecTec type. An accepted case supplies a fixed `p4programIR` answer. Its
proposition requires both `Program_ok input expected` and that every possible
`Program_ok` output equals `expected`. A rejected case requires
`¬ (∃ output : p4programIR, Program_ok input output)`. The generated definitions
contain no proofs.

`p4spec/test/backend-lean/discover_typecheck.py` inventories the repository's
SL static-semantics suites. They record 1,948 P4 cases: 1,282 expected to
pass, 550 expected to fail, and 116 excluded. The p4c boot suite covers the
same 1,918 p4c files; 34 of its negative results say `(unknown)` and therefore
cannot serve as rejection evidence. The parse-only and STF simulation suites
are outside this type-checking inventory. Run the script with `--list` for
every source path, recorded outcome, and originating suite.

The proof corpus is in `p4spec/test/backend-lean/typecheck-cases.tsv`.
It contains 1,909 targets: 1,334 accepted, 574 rejected by relation nonmatch,
and one `abort-reject` conjecture. Every accepted case has a fixed, compressed
Lean output term in `p4spec/test/backend-lean/oracles/full/`, captured from the
repository's deterministic SL interpreter running `Program_ok`. The companion
`typecheck-audit.tsv` records the original suite outcome and actual interpreter
result for all 1,948 inputs; `-` marks an empty diagnostic. The remaining 39
inputs failed parsing, so no
`p4program` value is available for a `Program_ok` proposition. The aborting
case is a negative proof target, but the interpreter did not establish its
rejection: `p4_16_errors/issue3188.p4` aborts on a V1 model version check.
Existing `.expected` files record only pass, fail, or exclude
status; the test runners discard the actual P4 IR output. The p4c `*_outputs`
files are compiler artifacts, not SpecTec `p4programIR` answers.

All 116 originally excluded cases were evaluated. Of those, 111 were
parseable. The current SpecTec interpreter rejected 59 and accepted 52.
The audit preserves both the original suite category and the observed outcome.

The manifest uses tab-separated `accept<TAB>P4<TAB>expected-Lean-term`,
`reject<TAB>P4`, or `abort-reject<TAB>P4`; paths are relative to the manifest
file. Answer files may be plain text or `.gz`. Blank lines and lines starting
with `#` are ignored. The fixed answers make output changes visible before
any Lean proof is attempted.

From the repository root, compare every answer file and recorded outcome with
the current SL interpreter:

```sh
python3 p4spec/test/backend-lean/discover_typecheck.py
python3 p4spec/test/backend-lean/verify_oracles.py \
  --exe _build/default/p4spec/lib/lean-skeleton/main.exe \
  --manifest p4spec/test/backend-lean/typecheck-cases.tsv \
  --audit p4spec/test/backend-lean/typecheck-audit.tsv \
  --spec spec --include p4c/p4include
```

Repeat the verifier with `--reverse` to check that IR answers do not depend
on the order in which cases are evaluated.

From the repository root, generate the current corpus's propositions with:

```sh
dune exec p4spec/lib/lean-skeleton/main.exe -- \
  --obligations-only -I p4c/p4include \
  --manifest p4spec/test/backend-lean/typecheck-cases.tsv spec \
  > typecheck-obligations.lean
```

The full output is about 390 MB. For proof work, `--case-range START COUNT`
generates a smaller piece while retaining each case's global `case_N` index.
For example, `--case-range 0 50` generates the first 50 propositions.

To refresh the answers after an intentional SpecTec change, create a path
list with `discover_typecheck.py --paths`, run the executable with
`--batch-cases PATHS -I p4c/p4include spec` to capture a TSV scan, then run
`capture_typecheck.py --scan SCAN`. This overwrites the answer files, audit,
and manifest; review the changed outcomes before accepting them.

Use `--case FILE EXPECTED` and `--reject-case FILE` for individual inputs.
`--dump-output FILE` prints the deterministic SL interpreter's `Program_ok`
output as a Lean term, for creating or auditing an answer file.
`--batch-cases PATHS` evaluates a newline-separated list of P4 paths in one
interpreter session. Each program starts with an initialized builtin runtime
and cleared interpreter caches. `capture_typecheck.py`
turns a complete batch scan into the manifest, audit, and compressed oracle
files.
`--check-rejection FILE` succeeds only when `Program_ok` fails by relation
nonmatch; syntax errors and interpreter aborts fail the check. Without
`--obligations-only`, the executable appends the propositions to the translated
specification. The resulting Lean file can then be extended with proof
theorems for the generated `case_N` propositions.

Fresh allocation no longer causes `Program_ok` or its callers to be pruned.
The corpus propositions still contain no proofs; fresh support alone does not
prove the full type-checking corpus. `--keep-going` remains disallowed with
cases because unsupported definitions can otherwise cause dangling
propositions. The small
`case-obligation.watsup` fixture in `p4spec/test/backend-lean` exercises the
complete parse, translate, proposition, and Lean type-checking path.
