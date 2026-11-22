# Cedar scheduler benchmark adapter

`benchmark.py` runs the official Testing Theorems artifact fork's `quickchick 2.`
tactic on a theorem with the five generation premises of
`Original.prop_no_type_error`. As in the upstream theorem, the two premises
that mention the entity list state it literally; `Example
entity_names_literal : Original.entity_names = ... := eq_refl` in `Bench.v`
ties the literal to `Original.v`. The conclusion is the harmless, proved
proposition `true = true`. The plugin prints the full theorem schedule and
defines a proof-local `theorem : nat -> Checker`; `Extraction "theorem.ml"
theorem` inside the proof captures that exact generated checker before `Qed`.
The conclusion theorem closes by `intros; reflexivity`. No generator is
handwritten, and this does not prove generator soundness or completeness.

For a candidate, the full `check.py` equivalence prefix is checked first on
the unmodified candidates. The same tactic then runs on `forall x :
Original.Input, Candidate.predicate_vNNN x -> true = true` over a derivation
copy written by `derivation.py`: every inductive and constructor declared in
`candidates/vNNN/Candidate.v` gets the suffix `_vNNN`, references to earlier
versions are renamed the same way, and `Original.entity_names` becomes the
literal list built only from constructors. The copy is re-tokenized and must
equal the checked file except for exactly these substitutions; unqualified or
partially qualified references to predecessor names, references to later
versions, and existing names ending in a generated suffix stop the batch.
`derivation-rewrite.json` records every substitution. The extracted OCaml module can rename the generator
evaluator (`run` for P0, `run0` in a candidate-shaped fixture), so the adapter
selects the unique evaluator from the generated `.mli` type. A failed or
ambiguous type match stops the benchmark.

`Support.v` recreates the active generation typeclasses of the pinned upstream
`Cedar.v` and `CedarWellTypedTermGenerator.v`: the nine-string
`genCedarString`, its no-op shrinker, the canonical `EntityName` and
`EntityUID` instances at priority 1, then the theorem-level default-priority
`genSizedEntityNameConst` and `genSizedEntityUIDConst` override (UIDs A, B, C,
D, Hicks, Kesha), the theorem's fixed schema fallback, and derived
`GenSized Environment`. Other syntax types use the same `Derive (Arbitrary)`
forms as upstream. The `Derive Show` instances for Schema, RequestType, and
Environment intentionally emit complete Coq constructors instead of
upstream's Cedar-facing pretty displays; this changes callback transport,
not the generation typeclass policy or the five premises. The upstream
`list ascii` instances serve the external Cedar checker and are irrelevant
to these seven input fields. The fixed `Spec.v` omits those generator/Show
definitions, so this support module is required to invoke the official
scheduler without changing Spec.v.

The driver makes exactly one `run (theorem 2) 2 seed`-equivalent call per outer
attempt, carries the same mutable OCaml seed state through the batch, records
`ok=None` as a discard, and stops on a failed or incomplete checker result.
The tactic's own QuickChick run is separate: its `scheduler.log` can say
`*** Gave up! Passed only 3500 tests` and `Discarded: 20000` even after it
successfully derives and extracts the checker. This internal result is stored
verbatim in `result.json` with its reported test and discard counters. A
`gave_up` internal result still permits the fixed external batch; it never
means the internal test passed. An internal `failed` result or an absent,
unrecognized, or ambiguous summary stops the benchmark with scheduler evidence.
The P0 checker reports five callback payloads: generated type, schema,
request types, environments, and expression. The callback bytes remain
in `raw-attempts.jsonl`. `serialization.py` decodes QuickChick string escapes
and negative `Z` notation into Coq source, splits constructor arguments only
at top level, and reconstructs an `Original.mkInput` with all seven fields.
Per-row Coq adapter lemmas check correspondence to the captured type, schema,
requests, nonempty environment list, and expression. Candidate callbacks use
the explicit `ShowInput` of all seven fields; downstream independent Coq
validation parses and checks the term. Parsing or compilation failure stops
the batch; it does not silently drop a sample.

Two guards run after derivation and stop the batch if either fails; the
result records them as `derivation_guards`:

1. Every binder of the printed theorem schedule is a variable of the theorem
   (`ets acts rs e es ty expr` for P0, `x` for candidates) or a fresh
   scheduler name of the form `v..._`. With `Original.entity_names` as a
   constant, the scheduler printed `(entity_names : _, ty : CedarType) <-G`
   and generated the list itself: in `cedar-poc-20261122T025605Z`, 82% of
   generated P0 schemas used another list and failed `WfSchema`, and the
   tactic's own run gave up after about 3,400 tests and 20,000 discards. With
   the literal list it passes 10,000 tests with about 2,400 discards, matching
   the upstream artifact run (10,000 and 2,386).
2. For a candidate, every renamed relation reachable from the selected
   predicate through constructor premises appears in the extracted
   `theorem.ml`. The plugin identifies relations by unqualified name; when
   every version was called `predicate`, a premise naming the predecessor's
   relation was compiled as a recursive call to the candidate's own
   generator, so the predecessor was never sampled.

`scheduler_entity_names` in `attempts.jsonl` is kept for compatibility and is
always `null`. The independent five-premise validator still decides each
reconstructed input against Original's fixed list; generated callback count is
not a count of valid inputs.

Production invocation (repeat for each fixed seed, with a fresh output path):

```sh
python3 scripts/cedar/benchmark.py properties/cedar_no_type_error \
  --candidate P0 --seed 101 \
  --output-dir properties/cedar_no_type_error/.runs/baseline-seed-101
```

Production requires exactly 10,000 outer attempts and size 2. The accepted
seeds are 101, 202, 303, 404, 505 and held-out 1101, 1202, 1303, 1404,
1505. `--test-mode --attempts N` exists only for real Coq regressions and
preparation. The append-only output directory contains `result.json`,
`attempts.jsonl`, `raw-attempts.jsonl`, scheduler/kernel/adapter logs, and a
source snapshot with the extracted checker and compiled sampler. `result.json`
uses `status: completed` only when derivation, extraction, and the exact outer
attempt batch finish. It records derivation status and the separate internal
QuickChick `passed` or `gave_up` outcome, its actual counters and summary, plus
source and tool hashes, commands, fixed parameters, and external attempt counts.
On failure it uses `status: failed` and preserves the error and available
`scheduler.log`. The internal QuickChick counters are operational provenance,
not an additional research metric or the denominator of the valid-input rate.

The observation theorem's `Print Assumptions` is closed under the global
context. The generated proof-local checker uses the artifact's existing random
seed and sampling axioms, listed by `Print Assumptions theorem`; no new axiom
was introduced in the authored property. `coqchk Bench` checks the stored
observation theorem, while Coq typechecks the proof-local generated checker
when the tactic constructs it. Neither check proves finite sampling complete.

Canonical EntityName and EntityUID instances are declared immediately after
their respective derived defaults, before deriving dependent types, matching
the declaration order in upstream Cedar.v. The theorem-level overrides follow
those derived types, as in the upstream theorem file.
