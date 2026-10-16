# spec4pbt

Property-based testing from a supplied specification and Lean proposition.

Use the Lean version pinned in `lean-toolchain` and Python 3.12 or later. The
Python tools use only the standard library. Run commands from the repository root.

## SpecTec specifications and observable properties

The `spectec-based` branch adds a complete path from native SpecTecX source to
testing a supplied property on an implementation's actual observations:

```text
SpecTecX parser/typechecker → independent Lean translator → typed observation view
                                                                ↓
certified input generator → implementation adapter → certified property checker
```

`external/spectecx` is the official [SpecTecX repository](https://github.com/kaist-plrg/spectecx)
as a submodule, pinned at `d5dd1382143f3ea300bf7997d3098b03120556ec`.
We maintain the adapter and Lean backends in `translator/`; upstream source stays clean.
The broader `--backend ported` path reuses the p4-spectec backend's translation,
declaration ordering and printer, adapted to native SpecTecX IL. Its provenance
is recorded in [backend/PROVENANCE.md](translator/backend/PROVENANCE.md); the shared
Lean runtime is documented in [runtime provenance](pbt/SpectecRuntime/PROVENANCE.md).

Use an existing OCaml >= 5.1 opam switch, or create one once. This checkout was
verified with OCaml 5.1.1:

```sh
opam switch create spectecx 5.1.1  # only when the switch does not exist
scripts/bootstrap-spectecx
scripts/build-translator
lake build
scripts/check-spectec-examples
```

Bootstrap installs exactly the submodule revision, including on subsequent runs.
The build script verifies the checkout and installed library fingerprint. An
upstream update is deliberate: checkout and stage the new submodule commit,
bootstrap again, update the translator if necessary, then run the tests. This
does not track the moving upstream branch automatically. Scripts accept an
alternative opam switch as their first argument.

The default `observation` backend supports recursive arithmetic relations,
records, aliases, guards and ordered fallback with manifests and JSON codecs.
The separate `--backend ported` path adds collections, polymorphism, functions,
iteration, subtype checks, mutually recursive types and partial arithmetic.
Its broader output is not yet connected to observation manifests. Builtin meanings
require an explicit donor profile. P4 source-dialect support is outside this work.
[The translator documentation](translator/README.md) gives commands and exact limits.
Execution soundness of emitted plans is proved in Lean; correctness of the
OCaml translation itself is checked by comparisons with the upstream interpreter,
and is not a formal compiler correctness theorem.

### Declare what an implementation can observe

Keep an observation TOML beside the specification:

```toml
schema_version = 1
[[observations]]
id = "value"
relation = "Eval_expr"
observe = ["%1"]
```

Slots are zero-based positions in the original relation. Input roles come from
SpecTecX's elaboration of `hint(input ...)`. Use `%1.VALUE` to select one record
field. Inputs cannot be selected as outputs; missing, duplicate or overlapping
selectors are errors. The generated view exposes `Input`, `Observation`,
`FullOutput`, `project`, `Specification`, frozen JSON codecs and `profileId`.
Multiple selected values use right-associated products in selector order.
`Specification` expresses existence of a full specification result with the
selected observation; it is available to the user but never replaces `Target`.

For a new translation, choose fresh output paths:

```sh
translator/_build/default/main.exe --namespace MySpec \
  --output specifications/MySpec.lean --manifest specifications/my-spec.json \
  external/spectecx/spectec/specs/itpl/ae/spec.spectec
python3 -m pbt.observations \
  --manifest specifications/my-spec.json --config specifications/ae/observations.toml \
  --observation value --spec-module specifications.MySpec \
  --namespace MyView --output pbt/MyView.lean
```

Generated files are never overwritten by these commands. Source modules use the
Lake project's root directory convention. A view binds the validated manifest,
selected configuration, source import closure and Lean/build configuration.
The runner checks its complete generated source, not just its stored profile ID.

### Supply the property and generator

The property module defines the following declarations, with no extra assumptions:

```lean
Premise : View.Input → Prop
Target : View.Input → View.Observation → Prop
check : View.Input → View.Observation → Bool
check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o)
```

Declare `Premise` as `fun _ => True` when no input restriction is needed. Supply
a `Spec4Pbt.CorrectGen Premise` in a separate generator module. The runner rebuilds
and audits the exact declarations, including module ownership, transitive
axioms and executable implementations. Unsafe/partial checkers, unproved claims,
additional hypotheses, and custom runtime replacements cannot certify a run.
The first version also rejects custom `csimp` compiler rewrites and imported
project declarations containing axioms, `sorry`, or unsafe proofs, including
unused declarations. This prevents compiler changes from bypassing the audited
checker or generator body.
The proof establishes agreement of the checker and the user's property; it does
not prove that the implementation satisfies that property.

JSON codecs are fixed when the view is generated, so later property instances
cannot reinterpret observations or forge Boolean verdicts. The Lean toolchain,
generated codecs, translator and implementation adapter remain trusted parts of
the integration. There is no generic proof that an arbitrary adapter faithfully
observes an arbitrary external implementation. The adapter must obtain selected
values from the actual result; it must not substitute a specification witness.

### Run the examples

The arithmetic example translates upstream's native AE specification. Its
certified input domain contains natural literals, `n + 2` and `n - 2`; it does
not claim to sample every arithmetic tree. Its user property compares the
observed value with a separately defined recursive evaluator:

```sh
python3 -m pbt.run_observable \
  --manifest specifications/ae/manifest.json --config specifications/ae/observations.toml \
  --observation-id value --spec-module specifications.ae.Spec \
  --view-module pbt.ae.View --view-namespace AeView \
  --property-module pbt.ae.Property --premise AeProperty.Premise \
  --target AeProperty.Target --check AeProperty.check --check-correct AeProperty.check_correct \
  --generator-module pbt.ae.Generator --generator AeProperty.correctGenerator \
  --adapter-command '["python3", "pbt/ae/adapter.py"]' \
  --output test_cases/ae-run --count 8 --size 5 --seed 0
```

The adapter receives `{"input": ...}` on stdin and must return exactly
`{"observation": ...}` on stdout. Its arguments are passed directly, without a
shell. Add `"--wrong"` to the arithmetic adapter command and choose another fresh
run folder to see a counterexample. The record example in `specifications/record`
and `pbt/record` observes only `VALUE` and checks the user property `VALUE > input`.
It accepts an implementation with a different hidden `TRACE`, while detecting an
observed violation. Its generator covers all nonnegative integer inputs.

A run saves metadata/configuration snapshots, sampler/checker fingerprints,
samples, exact requests, actual observations, process stdout/stderr and verdicts.
Replay the implementation portion of a saved arithmetic case with:

```sh
python3 pbt/ae/adapter.py < test_cases/ae-run/case-000000/request.json
```

Exit codes are `0` for passed, `1` for a counterexample, and `2` for an error.
Timeouts, malformed or ill-typed observations and implementation failures never
pass. `count` must be positive, and each generator call produces an input. The
result JSON retains `skipped` with value `0` for compatibility. Runs stop on the
first failed case or execution error. Source changes invalidate the ephemeral
certificate. An empty premise cannot have a certified total generator.

```sh
python3 -m unittest discover -s translator/tests -v
python3 -m unittest discover -s pbt -p 'test_*.py' -v
```

## Existing proposition example

The common example supplies an even-natural-number specification, the proposition
`∀ n, Valid n → n + 0 = n`, and a generator with proved soundness and completeness.
Its `size` bounds inputs by `2 * size`; each sample uses `seed + index`. The
generator satisfies the premise without consulting the proposition's conclusion.

```sh
lake build example-samples
python3 -m pbt.generate_goals \
  --spec-module specifications.Example \
  --property-module pbt.example.Property --declaration Example.property \
  --namespace ExampleGoals --output .lake/generated/ExampleGoal.lean \
  --timeout-seconds 60
python3 -m pbt.verify --module pbt.example.Generator \
  --proof Example.correctGenerator \
  --expected-type 'ExampleGoals.CorrectGen ExampleGoals.Premise' \
  --timeout-seconds 60
python3 -m pbt.run --implementation /usr/bin/python3 \
  --output test_cases/example-run --count 4 --size 8 --seed 12
python3 -m unittest pbt.test_example pbt.test_goal_tools.ToolBoundaryTests -v
```

Supply the executable path of the Python interpreter to test as `--implementation`.
The runner exports Lean samples, renders Python source from an AST, executes each
program, and compares its printed integer with the input. Each case folder contains
`program.py`, `sample.json`, and `observation.json`. Replay a case with the same
interpreter, for example `/usr/bin/python3 test_cases/example-run/case-000000/program.py`.
Choose a fresh output directory for each run; existing output is never overwritten.
Goal generation also requires a fresh destination and compiles the result before
writing it. The checked-in `pbt/example/Goal.lean` is the example contract;
the command above emits a separate copy for inspection.

## Writing properties

Supply a Prop-valued definition or opaque declaration, an inductive proposition,
or a theorem whose type is the proposition. Declaration parameters are
universally quantified in the extracted property. Universe parameters are
preserved in the generated declarations.

For example, a property module can contain:

```lean
import specifications.Example

namespace MyProperties

-- The existing single-input, single-premise form remains supported.
def evenIdentity : Prop :=
  ∀ n : Nat, ExampleSpec.Valid n → n + 0 = n

-- A premise is optional, and there may be several dependent inputs.
def boundedIndex : Prop :=
  ∀ n : Nat, ∀ i : Fin (n + 1), i.val ≤ n

-- Conclusions may contain existential quantifiers and other logical forms.
def successorExists : Prop :=
  ∀ n : Nat, ∃ m : Nat, m = n + 1

-- Definition parameters, implicit binders, and universes are supported.
universe u
def identity {α : Type u} (x : α) : Prop := x = x

-- The conclusion may depend on a proof input.
def proofIdentity : Prop :=
  ∀ n : Nat, ∀ h : n = n, h = h

-- Properties without inputs are also supported.
def closedProperty : Prop := True ∨ False

theorem identityTheorem (n : Nat) : n + 0 = n := rfl

opaque opaqueProperty : Prop := True

inductive inductiveProperty : Prop where
  | witness : inductiveProperty

end MyProperties
```

Select one declaration with `--declaration`, for example
`--declaration MyProperties.successorExists`, and set `--property-module` to its
module. Types, propositions, proof inputs, typeclass binders, and arbitrary
logical conclusions are accepted; inputs need not be monomorphic values in
`Type`.

The generated contract exposes `Property`, `Input`, `Premise`, and `Target`,
together with a constructive equivalence checked by Lean:

```lean
theorem property_iff :
    Property ↔ (∀ input : Input, Premise input → Target input)
```

For the existing form `∀ x : T, P x → Q x`, the direct representation is retained
when `T` is a concrete monomorphic type in `Type`, both binders are explicit,
and `Q x` neither depends on the premise proof nor has further leading binders:
`Input` is `T`, `Premise` is `P`, and `Target` is `Q`.

Otherwise, the leading universal binders are bundled into a dependent input
using nested `PSigma` pairs ending in `Unit`. This includes type and proof
binders, so later fields can depend on earlier fields. `Premise` is `True` and
`Target` is the remaining proposition with the fields substituted for its
inputs. With no leading binders, `Input` is `Unit` and `Target` is the whole
property. For `successorExists`, only `n` is sampled: `∃ m, m = n + 1` stays in
`Target`. An existential witness is not converted into a universally sampled
input.

If a private implementation detail cannot be printed in a generated module,
the contract keeps the original public proposition as `Target` with `Input =
Unit` and `Premise = True`. This still yields a constructive equivalence, but
the generated input no longer exposes the proposition's quantified values for
sampling.

## Constructing and extracting a generator

The generated contract defines `Generator` as a total function from size and seed to
`Input` (`Nat → Nat → Input`). Its support is the set of inputs returned for at
least one size and seed. The proof obligation is a **type with a generator witness**:

```lean
def CorrectGen (P : Input → Prop) :=
  {gen : Generator // ∀ input, Support gen input ↔ P input}
```

Write a term of `CorrectGen Premise`. The forward implication proves that every
generated input satisfies the premise; the reverse implication proves that every
input satisfying it is reachable for some size and seed. Extract the executable
generator with `.val`. Every size/seed pair produces a premise-satisfying input;
an empty premise cannot have a `CorrectGen` witness. For example, a complete
generator for all natural numbers can be constructed in one declaration:

```lean
def allNats : Spec4Pbt.CorrectGen (fun _ : Nat => True) := by
  refine ⟨fun _size seed => seed, ?_⟩
  intro input
  constructor
  · intro _; trivial
  · intro _; exact ⟨0, input, rfl⟩

def sampleNat : Spec4Pbt.Generator Nat := allNats.val
```

`pbt.CorrectGen` also provides axiom-free construction rules. `pure a` has
support `x = a`; `pick g h` has support `P x ∨ Q x`; `bind g next` has support
`∃ a, P a ∧ Q a x`; `map f g` has support `∃ a, P a ∧ f a = x`; and `convert g h`
changes the stated predicate using a pointwise equivalence `h`. Applying these
rules builds the generator and its support proof at the same time. For example:

```lean
def oneOrTwo : Spec4Pbt.CorrectGen (fun n : Nat => n = 1 ∨ n = 2) :=
  Spec4Pbt.CorrectGen.pick
    (Spec4Pbt.CorrectGen.pure (1 : Nat))
    (Spec4Pbt.CorrectGen.pure (2 : Nat))
```

[The even-number example](pbt/example/Generator.lean) starts from a certified
natural-number generator, maps it through `n ↦ 2 * n`, converts the resulting
predicate to `ExampleGoals.Premise`, and defines `Example.generate` as
`Example.correctGenerator.val`. `pbt/example/Emit.lean` samples that extracted
function. [Its arithmetic lemmas](pbt/example/EvenProofs.lean) preserve the
original modulo specification while keeping the witness free of axioms. To check
a witness's exact type and transitive axioms, use `pbt.verify` with the complete
`CorrectGen` type, as shown above.

This is a local adaptation of [Palamedes's proof-carrying generator
approach](https://github.com/hgoldstein95/palamedes-lean). It retains this
project's deterministic size/seed sampler; it does not import Palamedes's `Gen`
syntax tree or sampling interpreter. `Candidate` remains an optional helper for
holding an input together with a premise proof. For bundled inputs, proofs
packed into `Input` still have to be constructed by the user. Exact support
guarantees a valid sample at every size and seed, but not a uniform distribution. Accepting a proposition does not imply that an executable
generator or decision procedure exists, and a two-natural-number sampler cannot
cover uncountable input domains. The original `pbt.run` serialization and executable
checking remain specific to this example; the SpecTec path above uses typed views
and supplied checkers. The generated contract does not
prove `Property` or `Target`. `pick` and `bind` decode seeds by structural
recursion; very large seeds can exhaust the Lean interpreter's recursion limit,
so use a compiled executable for large sampling runs.

The verifier checks the designated declaration's exact type and rejects every
transitive axiom, including Lean's foundational axioms. The tools fail with
diagnostics on timeout. Run native goal-tool integration tests, including
property extraction and the strict axiom audit, with:

```sh
python3 -m unittest pbt.test_goal_tools.GoalToolsIntegrationTests -v
```

The example witness passes the zero-axiom audit. The integration tests also
check generated `property_iff` proofs and reject witnesses containing `sorry`.

`specifications/` holds specification sources and their provenance. `pbt/` holds
the common goal tools and groups property-specific code in folders such as
`pbt/example/`. `implementations/` holds external checkouts and builds;
`test_cases/` holds generated cases. Contents of these two directories are ignored
except for their tracked `.gitkeep` files.

The `main` branch supplies the common structure and a runnable example. Each
specification branch starts from `main`; `P4` carries the P4 specification and
existing generators.
