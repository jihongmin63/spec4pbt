# Native SpecTec property clauses

Properties use ordinary SpecTec EL clauses. The frontend lowers them through the
existing EL→IL→AL path, retains source and AL origins, and analyzes output
provenance. An external request may read a property input or an earlier observed
external output. A condition that combines an internal witness with an observed
value is rejected during AL planning.

The generated `Contract.lean` uses the ordered SpecTec relation semantics.
`Conditions` and `Premise` include **every** source condition, including conditions
rechecked against actual observations. Certification requires these exact Lean
declarations in an imported proof module:

```lean
theorem property_correct : Bundle.Contract.SpecProperty := ...
theorem reference_run_correct :
  Bundle.Contract.SpecProperty →
  ∀ input, Bundle.Contract.Premise input → Bundle.Contract.ReferenceRun input := ...
```

`run` additionally audits a `CorrectGen Bundle.Contract.Premise` generator for
exact support. The proof audit rejects extra hypotheses and `sorry` dependencies.
The final checker executes normalized SpecTec AL over the completed trace; it
does not substitute reference outputs for observed values. Outcomes are `pass`,
`fail`, or `error`. An observed guard that is false is a `fail` even when the goal
itself is a tautology. Protocol, decode, abort, and timeout causes remain errors.

The observation TOML used by `plan` and `build` contains only `schema_version = 1`
and `[[observations]]` entries (`id`, `relation`, `observe`). The bundle's
`metadata-config.json` and `plan.json` show the selected observation fields and
AL occurrence order. Its `manifest.json` records the SpecTec relation input
slots and canonical types. The implementation TOML is supplied separately for
each `run`, `collect`, or `rerun`:

```toml
schema_version = 1
id = "my-copy"
cwd = "."
[[executions]]
relation = "Copy"
adapter = ["python3", "adapter.py"]
artifacts = ["copy-target.py"]
```

`cwd` is relative to the implementation manifest, and relative adapter and
artifact paths are resolved there. Each adapter receives a JSON request on
stdin containing `plan_id`, `case_id`, `occurrence_id`, `relation_id`, canonical
`input`, and the metadata's `observe` selectors. It executes the selected
implementation, extracts those fields, and writes one JSON response with the
same four IDs, `status = "success"` and an `observation` object, or
`status = "relation_failure"`. The [ordered adapter](../specifications/property_clause/ordered_adapter.py)
calls a separate [target](../specifications/property_clause/ordered_target.py) and
extracts its native `value`. `artifacts` lists target binaries and helpers that
cannot be found from the adapter argv. The launcher and script arguments are
fingerprinted automatically. A fingerprint records provenance and detects
change during a run; it does not prove the implementation's behavior.

Build the pinned native translator, then run the small proof-backed examples:

```sh
scripts/build-translator
python3 -m pbt.property_clause_examples.run \
  --property positive \
  --bundle pbt/OrderedPositiveDemo \
  --output test_cases/ordered-positive --count 4 --size 5 --seed 0
```

`positive` proves that `Copy(n, v)` and `v > 0` give `Premise(n) ↔ n > 0`, so
its generator never samples zero. `--mode zero` makes the adapter return zero
for a positive input and produces a failing observed condition. Other examples
are `internal_positive` (shared private witness), `progress` (private condition
and external goal), `chain` (observed output fed into the next request), and
`independent` (two separately collected calls). The `mixed` source clause is
available to `plan` as a rejected provenance example.

To build a custom bundle, put a proof file at a stable Lean module path that
imports the future `<output>.Contract` module, then run:

```sh
python3 -m pbt.property_clause build \
  --spec specifications/property_clause/ordered_spec.watsup \
  --property specifications/property_clause/ordered_properties.watsup \
  --name positive \
  --config specifications/property_clause/ordered_observations.toml \
  --output pbt/CustomBundle \
  --proof-module pbt.CustomProof \
  --property-proof MyProof.property_correct \
  --reference-run-proof MyProof.reference_run_correct
python3 -m pbt.property_clause run \
  --bundle pbt/CustomBundle \
  --implementation specifications/property_clause/ordered_correct_implementation.toml \
  --generator-module pbt.CustomGenerator \
  --generator MyGenerator.generator \
  --output test_cases/custom --count 4
```

`collect` accepts a manual JSON input and assumes its premise is satisfied;
`run` is the certified input path. Both require an implementation manifest and
validate every used external relation before sampling or target execution.
Certificate and trace schema version 3 reject earlier combined-config bundles
and traces; rebuild and rerun those records. Native AL IR remains schema 2.
Each trace stores occurrence IDs, request inputs, raw adapter responses,
observed fields, errors, a certificate fingerprint, and a separate implementation
snapshot with manifest and dependency fingerprints. Recheck uses the saved
snapshot and responses without reading the implementation files. Rerun requires
a new explicit implementation and recomputes later inputs from its new observations:

```sh
python3 -m pbt.property_clause recheck \
  --bundle pbt/OrderedPositiveDemo \
  --trace test_cases/ordered-positive/case-000000/trace.json
python3 -m pbt.property_clause collect \
  --bundle pbt/OrderedPositiveDemo \
  --implementation specifications/property_clause/ordered_correct_implementation.toml \
  --input input.json --output test_cases/manual-copy
python3 -m pbt.property_clause rerun \
  --bundle pbt/OrderedPositiveDemo \
  --implementation specifications/property_clause/ordered_zero_implementation.toml \
  --case test_cases/ordered-positive/case-000000 \
  --output test_cases/ordered-positive-rerun
```

## Type soundness: successful instantiation after typing

The P4 obligation discussed here is: a program accepted by `Program_ok` can be
instantiated by `Program_inst`. Its source clause is:

```text
property instantiation_progress:
  (p : p4program)
  Program_inst: |- p : l s
  -- Program_ok: |- p : ir
```

`p` is generated. The typing result `ir` is an internal existential witness.
The instantiation results `l` and `s` belong to the goal. If the property only
checks that instantiation succeeds, metadata can keep both outputs hidden:

```toml
schema_version = 1
[[observations]]
id = "instantiation"
relation = "Program_inst"
observe = []
```

`Program_ok` remains internal, so the generator must prove typing acceptance.
`Program_inst` is external and needs an implementation binding even though its
observable output list is empty.

EL elaboration infers the three output types. AL lowering produces the ordered
condition occurrence `Program_ok(p; ir)` and goal occurrence
`Program_inst(p; l, s)`, with separate source origins and scopes. Classification
keeps the former in the proof-only runtime subset and collects the latter as
an external request with input `[p]`, no dependencies, and `observe = []`.

The emitted Lean contract has the following structure, with identifier quoting
and transport namespace aliases simplified:

```lean
structure Input where
  p : SpecTec.p4program

def Conditions (input : Input) (ir : SpecTec.p4programIR) : Prop :=
  SpecTec.Program_ok input.p ir

def Premise (input : Input) : Prop :=
  ∃ ir, Conditions input ir

def Goal (input : Input) (ir : SpecTec.p4programIR)
    (l : SpecTec.globalInstLayer) (s : SpecTec.store) : Prop :=
  SpecTec.Program_inst input.p l s

def SpecProperty : Prop :=
  ∀ input ir, Conditions input ir → ∃ l s, Goal input ir l s
```

The unused `ir` argument to `Goal` is part of the emitter's uniform shared
condition-variable interface. The property above is logically equivalent to:

```lean
∀ p, (∃ ir, SpecTec.Program_ok p ir) →
  ∃ l s, SpecTec.Program_inst p l s
```

`CorrectGen Premise` certifies exactly the supported inputs satisfying the
premise. It generates `p`; the proof does not expose `ir` to an external call.
Bundle certification also audits the property proof and the `ReferenceRun`
proof connecting ordered calls and AL checks. Emitting these definitions alone
is not a proof of the P4 property.

For each generated program, collection calls only the external instantiation
adapter. A `success` response has `observation: {}` because the property does
not inspect `l` or `s`; this reports successful instantiation. A relation failure
fails the case. Final checking replays that response in the goal AL block. It
does not run the internal typing relation again or fabricate hidden outputs.

The actual P4 clause is supported by the frontend and planner. Certified
execution against a concrete P4 implementation additionally requires its
adapter, the concrete external-type/native codecs, and property/reference-run
and generator proofs. The small ordered examples exercise the complete
certified build, execution, recheck, and rerun path.

Parse and plan the actual P4 clause with its status-only external metadata:

```sh
python3 -m pbt.property_clause plan \
  --spec external/p4-spectec/spec \
  --property specifications/property_clause/full_p4_progress.watsup \
  --name instantiation_progress \
  --config specifications/property_clause/full_p4_observations.toml
```
