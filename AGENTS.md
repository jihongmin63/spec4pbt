# Predicate reformulation workspace

This independent branch contains the Coq/QuickChick environment and a verification
example. Do not merge it wholesale into P4-spectec-based or pbt-experiments.

Keep all environment configuration in environment/env.sh and
environment/opam-switch.export. Use `bash environment/env.sh coqc` and
`bash environment/env.sh coqtop` to select the local switch. Run
`bash environment/env.sh check` after changing the example or environment.
Keep installations, generated files, archived local data, and verification logs
under ignored _opam-popl18/. Preserve previous verification evidence.

Derive generators and correctness proofs with the pinned upstream QuickChick.
Do not replace failing proof automation with admissions, new axioms, or a test-only
claim of correctness. Report upstream assumptions printed by Coq. Completeness
ranges over all sizes and random seeds, not all values in a finite test run.
Do not modify other worktrees.

For property exploration, keep Original.v and the selected specification fixed.
Each candidates/vNNN directory contains Candidate.v and Equivalence.v; the latter
proves `equivalent` against the immediately preceding predicate (Original for v001).
Never edit scripts/check.py or scripts/run.py to make a candidate pass. Run check.py
for the entire sequence; run.py --candidate vNNN verifies that prefix and derives
that candidate's generator and correctness automatically. Do not author Generator.v.
Keep property snapshots and evidence in ignored property-local .runs/ directories.
The two scripts are maintained verification infrastructure; changes require the
real Coq regressions in scripts/tests. No search configuration JSON is needed.
