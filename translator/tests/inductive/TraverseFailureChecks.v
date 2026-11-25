From Coq Require Import String List Arith.
From ALCoq Require Import Execution Values.
From ALCoq.Builtins Require Import P4.
From P4Spec.Generated Require Import InductiveRelations.
Import ListNotations.
Open Scope string_scope.

Definition state n : State := {| next_fresh := n |}.

Lemma first_step_succeeds :
  g_p4_dec_step_execute 0 (state 0) (Success 0) (state 1).
Proof.
  eapply direct_case_8.
  - apply direct_case_2; reflexivity.
  - apply direct_case_10; reflexivity.
Qed.

Lemma second_step_unmatches :
  g_p4_dec_step_execute 1 (state 1) Unmatch (state 2).
Proof.
  eapply direct_case_8.
  - apply direct_case_2; reflexivity.
  - apply direct_case_12. reflexivity.
Qed.

Lemma remaining_list_unmatches :
  g_p4_dec_each_x5f_step_traverse_1_at_1 [1; 2]
    (state 1) Unmatch (state 2).
Proof.
  eapply direct_case_24.
  - reflexivity.
  - apply second_step_unmatches.
  - apply direct_case_32.
Qed.

Lemma first_failure_stops_iteration :
  g_p4_dec_each_x5f_step_execute [0; 1; 2]
    (state 0) Unmatch (state 2).
Proof.
  apply direct_case_38.
  eapply direct_case_24.
  - reflexivity.
  - apply first_step_succeeds.
  - eapply direct_case_29. apply remaining_list_unmatches.
Qed.

Print Assumptions first_failure_stops_iteration.

Theorem first_step_error_propagates x xs s err t :
  g_p4_dec_step_execute x s (Error err) t ->
  g_p4_dec_each_x5f_step_execute (x :: xs) s (Error err) t.
Proof.
  intro H. apply direct_case_40.
  eapply direct_case_24; [reflexivity | exact H | apply direct_case_34].
Qed.

Theorem successful_step_preserves_tail_error x xs s value middle err t :
  g_p4_dec_step_execute x s (Success value) middle ->
  g_p4_dec_each_x5f_step_traverse_1_at_1 xs middle (Error err) t ->
  g_p4_dec_each_x5f_step_execute (x :: xs) s (Error err) t.
Proof.
  intros H T. apply direct_case_40.
  eapply direct_case_24; [reflexivity | exact H |].
  apply direct_case_31. exact T.
Qed.

Theorem successful_step_preserves_tail_unmatch x xs s value middle t :
  g_p4_dec_step_execute x s (Success value) middle ->
  g_p4_dec_each_x5f_step_traverse_1_at_1 xs middle Unmatch t ->
  g_p4_dec_each_x5f_step_execute (x :: xs) s Unmatch t.
Proof.
  intros H T. apply direct_case_38.
  eapply direct_case_24; [reflexivity | exact H |].
  apply direct_case_29. exact T.
Qed.

Print Assumptions first_step_error_propagates.
Print Assumptions successful_step_preserves_tail_error.
Print Assumptions successful_step_preserves_tail_unmatch.

Definition step_result n s : Outcome nat :=
  if andb
      (equal_value text_ops "FRESH__0"
        (String.append "FRESH__" (print_nat (next_fresh s))))
      (equal_value nat_ops n 0%nat)
  then Success n else Unmatch.


Lemma step_direct n s o t :
  g_p4_dec_step_execute n s o t <->
  o = step_result n s /\ t = state (S (next_fresh s)).
Proof.
  destruct s as [counter]. split.
  - intro H. inversion H; subst; clear H.
    match goal with
    | F : g_p4_dec_fresh_x5f_typeId_execute _ _ _ |- _ =>
        inversion F; subst; clear F
    end.
    match goal with
    | A : g_p4_dec_step_after_call_1_at_1 _ _ _ _ _ _ |- _ =>
        inversion A; subst; clear A
    end;
      unfold g_p4_dec_fresh_x5f_typeId_fresh_text in *;
      unfold step_result; cbn [String.append next_fresh] in *;
      repeat match goal with
      | E : equal_value _ _ _ = _ |- _ => rewrite E
      end;
      cbn [andb]; split; reflexivity.
  - intros [-> ->]. unfold step_result. cbn [next_fresh].
    destruct (equal_value text_ops "FRESH__0"
      (String.append "FRESH__" (print_nat counter))) eqn:Etext;
      destruct (equal_value nat_ops n 0%nat) eqn:Enum;
      cbn [andb].
    all: eapply direct_case_8.
    all: try solve [apply direct_case_2; reflexivity].
    all: first [apply direct_case_10; assumption
               | apply direct_case_11; assumption
               | apply direct_case_12; assumption].
Qed.


Lemma each_direct xs s o t :
  g_p4_dec_each_x5f_step_execute xs s o t <->
  g_p4_dec_each_x5f_step_traverse_1_at_1 xs s o t.
Proof.
  split.
  - intro H. inversion H; subst; assumption.
  - intro H. destruct o as [value | | err].
    + eapply direct_case_37. exact H.
    + eapply direct_case_38. exact H.
    + eapply direct_case_40. exact H.
Qed.


Print Assumptions step_direct.
Print Assumptions each_direct.
