From Coq Require Import Arith.
From ALCoq Require Import Execution Values.
From FixtureSpec.Generated Require Import InductiveRelations.

(* The constructor form emitted before computation closure conversion. This
   comparison quantifies over every input, outcome and initial/final state. *)
Inductive before_normalization : nat -> State -> Outcome nat -> State -> Prop :=
| before_success : forall n s,
    equal_value nat_ops n 7 = true ->
    before_normalization n s (Success (S n)) s
| before_unmatch : forall n s,
    equal_value nat_ops n 7 = false ->
    before_normalization n s Unmatch s.

Theorem computation_normalization_equivalent n s o t :
  g_fixture_rel_Pre_execute n s o t <-> before_normalization n s o t.
Proof.
  split; intro H; inversion H; subst.
  - apply before_success. assumption.
  - apply before_unmatch. assumption.
  - eapply direct_case_2; try reflexivity; assumption.
  - eapply direct_case_3; try reflexivity; assumption.
Qed.
Print Assumptions computation_normalization_equivalent.
