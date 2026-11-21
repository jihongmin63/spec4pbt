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
