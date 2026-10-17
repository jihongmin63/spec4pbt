# spec4pbt — P4-spectec-based

This branch contains the SpecTec-to-Lean translator in `translator/src/` and
connects its generated relations to certified observable properties. It reuses
the observation layer, checker certification and actual-implementation runner
from `spectec-based`.

## P4-SpecTec dependency and local translation

`external/p4-spectec` is a submodule of the official
[kaist-plrg/p4-spectec](https://github.com/kaist-plrg/p4-spectec), pinned to
`2730cfd9e74048bb5439da0f8afcef124079a064`. It supplies the frontend and P4
specification. The complete Lean backend and its execution support libraries are
tracked under `translator/src/`, imported from Docker revision
`d150aa6e53e3f572bc4b02299c05d6d6cee9d6c0`. See
[translator provenance](translator/PROVENANCE.md) for its source and license.

A fresh clone needs Git, Python 3.12 or later, opam with a C build toolchain,
and Lean's `elan`/`lake`. The checked-in `lean-toolchain` selects Lean. Initialize
the public dependency and install the OCaml packages:

```sh
scripts/bootstrap-p4-spectec
opam switch create spec4pbt 5.1.1
opam install --switch=spec4pbt --deps-only ./external/p4-spectec/p4spectec.opam
opam install --switch=spec4pbt yojson
scripts/build-translator --switch spec4pbt
lake build
```

An existing compatible switch can be selected with `--switch NAME`; omitting it
uses the active opam switch when building. Subsequent translation uses the
recorded local build. `scripts/bootstrap-p4-spectec --source PATH` optionally
uses a local Git cache containing the official pin.

The build command compiles both the actual translator and the observation
metadata helper. It creates an ignored workspace at
`translator/_build/p4-spectec`, combines the pinned official source with the
tracked backend, and applies the small tracked `algo_defs` compatibility patch
there. The official submodule stays unchanged. All source needed beyond the
public submodule is in this repository; no external Docker checkout or prebuilt
translator is used.

Use the backend's original CLI through `scripts/translate-spec`:

```sh
scripts/translate-spec specifications/p4record/spec.watsup > /tmp/Record.lean
```

The original backend generates `Spec.lean` unchanged. The separate
`p4bridge/metadata.ml` uses the same frontend's `Pass.elab` to extract type names,
record fields and relation input slots. It generates `Transport.lean` with JSON
instances and manifest aliases. The `SpecTec` namespace and embedded execution
library are preserved. `p4bridge` handles observation integration; `translator`
contains the semantic translator.

The previous AE/record generated examples and their runtime are retained as
reference examples. The new P4 modules do not import that runtime. The independent
SpecTecX translator and submodule belong to the separate `spectec-based` branch.

## Declare external observations

Keep the observation scope beside the donor-dialect `.watsup` specification:

```toml
schema_version = 1

[[observations]]
id = "value"
relation = "Eval"
observe = ["%1.VALUE"]
```

Input slots come from the relation's `hint(input ...)`; the sidecar cannot change
them. `%1.VALUE` selects one field of output slot 1. Whole outputs, nested record
fields and multiple projections use the same selectors as `spectec-based`.
Only the selected observation is passed to the final property checker.

Generate a fresh bundle (use a destination that does not exist):

```sh
python3 -m p4bridge.translate \
  --config specifications/p4record/observations.toml \
  --output-dir specifications/MyP4/Generated \
  specifications/p4record/spec.watsup

python3 -m pbt.observations \
  --manifest specifications/MyP4/Generated/manifest.json \
  --config specifications/p4record/observations.toml --observation value \
  --spec-module specifications.MyP4.Generated.Transport \
  --namespace MyP4View --output pbt/MyP4View.lean
```

The bundle contains the unmodified translation, transport, manifest, a copy of
the observation config and provenance hashes. Generation checks the Lean
translation, transport and all selected projections before publishing the bundle.
Existing destinations are never overwritten. `--executable` opts into the donor's
fuel evaluator; the default is ordered logical semantics, which is sufficient
for checking properties against outputs of an actual implementation.

Full P4 uses abstract external types such as architecture state. Supply the
chosen representation and instances with `--transport-model Model.lean` when
using such a specification. These are Lean declarations inserted inside the
transport namespace, not imports or a standalone module. No default external
model is invented. [The bridge guide](p4bridge/README.md) describes the exact
boundary and how to run the original translator on the entire P4 specification.

## Certified properties and actual implementation output

The typed view exposes `Input`, `Observation`, `FullOutput`, `project`, and the
existential observable relation `Specification`. User properties have:

```lean
Premise : Input → Prop
Target : Input → Observation → Prop
check : Input → Observation → Bool
check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o)
correctGenerator : Spec4Pbt.CorrectGen Premise
```

`check_correct` certifies the checker against the user's property; it does not
assume the implementation satisfies that property. The implementation adapter
receives `{"input": ...}` and returns exactly `{"observation": ...}`. Diagnostics
may go to stderr. The runner certifies the exact checker and generator, verifies
profile identity and dependency freshness, then tests actual adapter outputs.

The committed P4-SpecTec record example observes `VALUE`, hides `TRACE`, and
checks `VALUE > input`:

```sh
python3 -m pbt.run_observable \
  --manifest specifications/p4record/Generated/manifest.json \
  --config specifications/p4record/observations.toml \
  --observation-id value --spec-module specifications.p4record.Generated.Transport \
  --view-module pbt.p4record.View --view-namespace P4View \
  --property-module pbt.p4record.Property --premise P4Property.Premise \
  --target P4Property.Target --check P4Property.check --check-correct P4Property.check_correct \
  --generator-module pbt.p4record.Generator --generator P4Property.correctGenerator \
  --adapter-command '["python3", "pbt/p4record/adapter.py", "correct"]' \
  --output test_cases/p4-observable --count 4 --size 5 --seed 0
```

Changing the adapter mode to `hidden-change` changes only TRACE and should pass.
Mode `wrong` returns an invalid observed VALUE and should produce a counterexample.
Choose a fresh output directory for each run. The adapter remains the trusted
boundary between an implementation's native result and the declared observation.

```sh
python3 -m unittest discover -s p4bridge/tests -v
python3 -m unittest discover -s pbt -v
scripts/check-p4-examples
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

The `main` branch supplies the common structure and a runnable example. `P4`
carries the P4 specification and existing generators. `P4-spectec-based` branches
from `main` and keeps its integration work in subsequent commits.
