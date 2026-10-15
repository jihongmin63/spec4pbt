# spec4pbt

Property-based testing from a supplied specification and Lean proposition.

Use the Lean version pinned in `lean-toolchain` and Python 3.12 or later. The
Python tools use only the standard library. Run commands from the repository root.

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
cover uncountable input domains. Serialization and executable checking remain
specific to the even-natural-number example. The generated contract does not
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
