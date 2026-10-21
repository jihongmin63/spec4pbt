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

The build command compiles the translator, observation metadata helper, property
frontend, and native AL property executor. It creates an ignored workspace at
`translator/_build/p4-spectec`, combines the pinned official source with the
tracked backend, and applies the tracked compatibility and property patches
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
correctGenerator : CorrectGen Premise
```

`check_correct` certifies the checker against the user's property; it does not
assume the implementation satisfies that property. The implementation adapter
receives `{"input": ...}` and returns exactly `{"observation": ...}`. Diagnostics
may go to stderr. The runner certifies the exact checker and generator, verifies
profile identity and dependency freshness, then tests actual adapter outputs.
For replay, it uses `seed + index` with the Palamedes sampler and records each
sampled input.

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
and compiles the result before writing it. The checked-in
`pbt/example/Goal.lean` is the example contract; the command above emits a
separate copy for inspection.

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

The `main` branch supplies the common structure and a runnable example. `P4`
carries the P4 specification and existing generators. `P4-spectec-based` includes
the common Palamedes generator layer and its SpecTec integration work.

## Native SpecTec property clauses

Use ordinary SpecTec clauses, prove their complete premises and property in
Lean, then collect external results and check them with the native AL runner.
Specification observation metadata and implementation adapters are separate,
so one certified bundle can test multiple implementations.

See [the property guide](docs/property-clauses.md) for build/run/recheck/rerun
commands, adapter contracts, proof-backed examples, and the actual P4
`Program_ok` to `Program_inst` translation.
