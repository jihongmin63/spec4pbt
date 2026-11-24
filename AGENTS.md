# Predicate reformulation workspace

The project tests external implementations against properties of a formal
specification, using input generators that QuickChick derives from Coq predicates.
This independent branch contains the pinned Coq/QuickChick environment, an
environment checks, and the tools that check predicate reformulations and derive
generators. Experiments that add specifications, properties, and implementation
adapters build on this branch. Do not merge it wholesale into P4-spectec-based or
pbt-experiments.

Keep all environment configuration in environment/env.sh and
environment/opam-switch.export. Use `bash environment/env.sh coqc` and
`bash environment/env.sh coqtop` to select the local switch. Run
`bash environment/env.sh check` after changing the example or environment.
Keep installations, generated files, archived local data, and verification logs
under ignored _opam-testing-theorems/. The AL-to-Coq workflow regenerates ignored final .v sources in
specification/<spec-name>/. New property-specific translations belong in
properties/<name>/.runs/publication/; existing fixed contexts keep their recorded
paths. Compile only ignored copies. Keep input profiles
immutable; generated bindings, publication registries and validation results
belong under ignored _opam-testing-theorems/. Keep temporary design plans there too. Preserve _opam-popl18/ and previous verification evidence.

Use Coq 8.20.0, OCaml 4.14.2, and the official Testing Theorems artifact fork
pinned by source-context archive hash in environment/env.sh. Do not substitute
stock QuickChick 2.2.0. Frontend tools use a separate OCaml 5.1.1 switch via
`bash environment/env.sh frontend`. OPAMROOT and both switches must remain under
the target worktree's _opam-testing-theorems/. Do not modify global opam state or
shell profiles. Default JOBS is 2.

Generator soundness/completeness proofs are outside this experiment's scope.
The property workflow derives Input generators with the pinned QuickChick tactic;
that derivation is separate from the AL-to-Coq relation proof obligations.
Predicate equivalence proofs remain
mandatory and must be closed without extra axioms or admissions. Finite sampling
is not a proof of generator correctness or completeness. Upstream Cedar tests
contain external extraction bindings and Admitted; execute them only as tests,
never as proofs in an authored property workflow.
Do not modify other worktrees.

For property exploration, keep Original.v and the selected specification fixed.
Each candidates/vNNN directory contains Candidate.v and Equivalence.v; the latter
proves `equivalent` against the immediately preceding predicate (Original for v001).
Never edit scripts/check.py or scripts/run.py to make a candidate pass. Run check.py
for the entire sequence; run.py --candidate vNNN verifies that prefix and derives
that candidate's generator automatically, without requiring generator proofs.
Do not author Generator.v.
Keep property snapshots and evidence in ignored property-local .runs/ directories.
The two scripts are maintained verification infrastructure; changes require the
real Coq regressions in scripts/tests. No search configuration JSON is needed.

Keep user-facing workflow documentation concise in the root README. Do not add
separate design, plan, or verification reports. Property commands and native
bridge sources belong under scripts/property/; translator semantics stay under
translator/. Preserve existing evidence when reorganizing code or publications.
