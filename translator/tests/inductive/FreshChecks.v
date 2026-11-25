From Coq Require Import String Arith.
From ALCoq Require Import Execution Values.
From ALCoq.Builtins Require Import P4.
From P4Spec.Generated Require Import InductiveRelations Relations_0000.
Open Scope string_scope.

Definition state n : State := {| next_fresh := n |}.

Lemma fresh_builtin_direct s o t :
  g_p4_dec_fresh_x5f_typeId_execute s o t <->
  o = Success (String.append "FRESH__" (print_nat (next_fresh s))) /\
  t = state (S (next_fresh s)).
Proof.
  split.
  - intro H. inversion H; subst; auto.
  - destruct s as [counter]. intros [-> ->]. constructor. reflexivity.
Qed.

Theorem failed_clause_consumes_fresh n s :
  g_p4_rel_Paths_execute n (state s)
    (Success (String.append "FRESH__" (print_nat (S s))))
    (state (S (S s))).
Proof.
  eapply direct_case_8.
  - apply direct_case_2; reflexivity.
  - eapply direct_case_13.
    + reflexivity.
    + eapply direct_case_24.
      * apply direct_case_2; reflexivity.
      * apply direct_case_26.
Qed.

Theorem public_paths_uses_direct n : g_p4_rel_Paths n "FRESH__1".
Proof.
  unfold g_p4_rel_Paths.
  exists (state 2).
  exact (failed_clause_consumes_fresh n 0).
Qed.

Print Assumptions fresh_builtin_direct.
Print Assumptions failed_clause_consumes_fresh.
Print Assumptions public_paths_uses_direct.
