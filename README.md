# spec4pbt

Property-based testing from a supplied specification and Lean proposition.

Use the Lean version pinned in `lean-toolchain` and Python 3.12 or later. The
Python tools use only the standard library. Run commands from the repository root.

The common example supplies an even-natural-number specification, the proposition
`∀ n, Valid n → n + 0 = n`, and a Palamedes `Gen Nat` with exact support proved
against `Valid`. Its sampler draws even inputs smaller than `2 * size` when
`size > 0`. Sampling is randomized; there is no seed decoder.

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
  --output test_cases/example-run --count 4 --size 8
python3 -m unittest pbt.test_example pbt.test_goal_tools -v
```

Supply the executable path of the Python interpreter to test as `--implementation`.
The runner exports Lean samples, renders Python source from an AST, executes each
program, and compares its printed integer with the input. Each case folder contains
`program.py`, `sample.json`, and `observation.json`. Replay a case with the same
interpreter, for example `/usr/bin/python3 test_cases/example-run/case-000000/program.py`.
Choose a fresh output directory for each run; existing output is never overwritten.
Replaying a case reruns its saved Python program with its saved input; it does not
recreate the random Lean draw. Goal generation also requires a fresh destination
and compiles the result before writing it. The checked-in `pbt/example/Goal.lean` is the example contract;
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
logical conclusions are accepted. Palamedes's `Gen` itself is restricted to
`Type` (`Type 0`). If the reflected `Input` lives in a higher universe, goal
generation still emits `Property`, `Input`, `Premise`, `Target`, and `property_iff`,
but omits the generator-specific declarations.

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

## Constructing and sampling a generator

This project pins [Palamedes](https://github.com/hgoldstein95/palamedes-lean) directly
at commit `c2012b84fc4ad8ee03e3528838175b959fcc9cf8` and uses its Lean
4.31.0 toolchain. `pbt.CorrectGen` only imports the original library modules; it
does not define a replacement generator. For `Input : Type`, a generated goal
uses:

```lean
def Support (g : Gen Input) (input : Input) : Prop := Gen.support g input
abbrev CorrectGen (P : Input → Prop) := _root_.CorrectGen P
```

Palamedes's `Gen` is a syntax tree with `ret`, `bind`, `pick`, `indexed`, and
`assume` constructors. Its `support` interpreter gives the exact set of possible
values. `pick` takes the union of supports and `bind` composes them with an
existential witness. `indexed` additionally requires a monotone family of
`Option` supports. `assume` contributes values only when its Boolean condition
holds. `CorrectGen P` pairs a `Gen` with an equality `g.support = P`.

Build a certified tree by hand with the original `Gen.CorrectGen.s_pure`,
`s_pick`, `s_bind`, and `convert` rules. The library also provides
`Gen.CorrectGen.s_arbNat`, whose `Gen.indexed` tree has support `True` for every
natural number. A small finite example is:

```lean
import pbt.CorrectGen

open Gen.CorrectGen

def oneOrTwo : CorrectGen (fun n : Nat => n = 1 ∨ n = 2) :=
  s_pick (s_pure 1) (s_pure 2)

def twoOrFour : CorrectGen
    (fun n : Nat => ∃ k, (k = 1 ∨ k = 2) ∧ n = 2 * k) :=
  s_bind oneOrTwo (fun k => s_pure (2 * k))
```

[The even-number proof](pbt/example/Generator.lean) uses `s_arbNat`, `s_bind`,
`s_pure`, and `convert` to produce `CorrectGen ExampleGoals.Premise`. Its `.val`
extracts a plain `Gen Nat`, and [the emitter](pbt/example/Emit.lean) calls
Palamedes's root-level `sample` with `SampleConfig`. `sizeLimit` controls the
`indexed` interpreter and `sizeRetryLimit` bounds retries. Exact support alone
does not promise that every sample call succeeds: `assume` can fail, and an
`indexed` family can yield `none` at a chosen size. The example uses a positive
size and Palamedes's total natural-number generator.

The generated contract calls a generator **sound** if every supported input
satisfies `Premise`, and **complete** if every premise-satisfying input is in its
support. It does not prove `Property` or `Target`. Sampling is random and does
not make support uniform. The Python serialization and executable property
check remain specific to the even-natural-number example. This migration uses
manual proof combinators and does not import Palamedes's generator search tactic.

`pbt.verify` checks the declaration's exact type and its source module. With
the approved Palamedes proof path, it permits only Lean's `propext` and
`Quot.sound` among transitive axioms; it still rejects `sorryAx`,
`Classical.choice`, user axioms, and axiom declarations in the source module.
The example witness currently reports `[propext, Quot.sound]`. The tools fail
with diagnostics on timeout. Run the full integration suite with:

```sh
python3 -m unittest pbt.test_example pbt.test_goal_tools -v
```

The only local Lean 4.31 compatibility addition is two small
`ite_eq_left`/`ite_eq_right` lemmas in
[pbt/example/EvenProofs.lean](pbt/example/EvenProofs.lean). They replace names
available in the previous Lean 4.34.1 toolchain; Palamedes's generator source
is used unchanged. Its `Type 0` restriction is an original library limit.

`specifications/` holds specification sources and their provenance. `pbt/` holds
the common goal tools and groups property-specific code in folders such as
`pbt/example/`. `implementations/` holds external checkouts and builds;
`test_cases/` holds generated cases. Contents of these two directories are ignored
except for their tracked `.gitkeep` files.

The `main` branch supplies the common structure and a runnable example. Each
specification branch starts from `main`; `P4` carries the P4 specification and
existing generators.
