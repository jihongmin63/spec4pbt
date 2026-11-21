# Predicate reformulation workspace

This independent branch contains the Coq/QuickChick environment and a verification
example. Do not merge it wholesale into P4-spectec-based or pbt-experiments.

Keep environment selection and installation in environment/env.sh and
environment/opam-switch.export; keep compatibility examples in environment/checks/. Use `bash environment/env.sh coqc` and
`bash environment/env.sh coqtop` to select the local switch. Run
`bash environment/env.sh check` after changing the example or environment.
Keep installations, generated files, archived local data, and verification logs
under ignored _opam-testing-theorems/. Preserve previous installations and verification evidence.

Use Coq 8.20.0, OCaml 4.14.2, and the official Testing Theorems artifact fork
pinned by source archive hash in env.sh. Do not substitute stock QuickChick 2.2.0.
On this branch, generator soundness/completeness proofs are outside the experiment
scope, as requested by the user. Predicate equivalence proofs remain mandatory
and must be closed without extra axioms or admissions. Finite sampling is not
a proof of generator correctness or completeness. Upstream Cedar tests contain
external extraction bindings and Admitted; execute them only as tests, never as
proofs in the authored property workflow.
Do not modify other worktrees.

For property exploration, keep Original.v and the selected specification fixed.
Each candidates/vNNN directory contains Candidate.v and Equivalence.v; the latter
proves `equivalent` against the immediately preceding predicate (Original for v001).
Never edit scripts/check.py or scripts/run.py to make a candidate pass. Run check.py
for the entire sequence; run.py --candidate vNNN verifies that prefix and derives
that candidate's generator automatically, without requiring generator proofs. Do not author Generator.v.
Keep property snapshots and evidence in ignored property-local .runs/ directories.
The two scripts are maintained verification infrastructure; changes require the
real Coq regressions in scripts/tests. No search configuration JSON is needed.
