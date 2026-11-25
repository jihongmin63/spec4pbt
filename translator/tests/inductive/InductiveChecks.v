From Coq Require Import Arith String.
From ALCoq Require Import Execution Values.
From FixtureSpec.Generated Require Import InductiveRelations Relations_0000.
Open Scope string_scope.

Lemma identity_direct n s o t :
  g_fixture_rel_Identity_execute n s o t <-> o = Success n /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; auto.
  - intros [-> ->]. constructor.
Qed.

Lemma called_direct n s o t :
  g_fixture_rel_Called_execute n s o t <-> o = Success n /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; clear H.
    match goal with H : g_fixture_rel_Identity_execute _ _ _ _ |- _ =>
      apply identity_direct in H; destruct H as [-> ->] end.
    match goal with H : g_fixture_rel_Called_after_call_1_at_1 _ _ _ _ _ |- _ =>
      inversion H; subst; clear H end; auto; discriminate.
  - intros [-> ->]. eapply direct_case_8.
    + apply direct_case_2.
    + apply direct_case_10.
Qed.

(* Once the first rule succeeds, the later fallback rule is not selected. *)
Theorem first_success_excludes_fallback s t :
  ~ g_fixture_rel_Called_execute 1 s (Success 9) t.
Proof.
  intro H. apply called_direct in H. destruct H as [H _]. discriminate H.
Qed.

Definition division_error : ExecutionError :=
  {| error_kind := HostConversion; error_detail := "partial expression failed" |}.

Lemma error_direct s o t :
  g_fixture_dec_error_execute s o t <-> o = Error division_error /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; cbn in *; try discriminate; auto.
  - intros [-> ->]. apply direct_case_20; reflexivity.
Qed.

Theorem public_identity_uses_direct n : g_fixture_rel_Identity n n.
Proof.
  unfold g_fixture_rel_Identity.
  eexists. apply direct_case_2.
Qed.

Lemma sink_direct s o t :
  g_fixture_dec_sink_execute s o t <-> o = Unmatch /\ t = s.
Proof.
  split; [intro H; inversion H; subst; auto | intros [-> ->]; constructor].
Qed.

Lemma fallback_direct s o t :
  g_fixture_dec_fallback_execute s o t <-> o = Success 9 /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; clear H.
    match goal with H : g_fixture_dec_sink_execute _ _ _ |- _ =>
      apply sink_direct in H; destruct H as [-> ->] end.
    match goal with H : g_fixture_dec_fallback_after_call_1_at_1 _ _ _ _ |- _ =>
      inversion H; subst; clear H end; try discriminate.
    match goal with H : g_fixture_dec_fallback_continue_from_2 _ _ _ |- _ =>
      inversion H; subst; auto end.
  - intros [-> ->]. eapply direct_case_28.
    + constructor.
    + eapply direct_case_33. constructor.
Qed.

Lemma wraperror_direct s o t :
  g_fixture_dec_wraperror_execute s o t <-> o = Error division_error /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; clear H.
    match goal with H : g_fixture_dec_error_execute _ _ _ |- _ =>
      apply error_direct in H; destruct H as [-> ->] end.
    match goal with H : g_fixture_dec_wraperror_after_call_1_at_1 _ _ _ _ |- _ =>
      inversion H; subst; clear H end; auto; discriminate.
  - intros [-> ->]. eapply direct_case_43.
    + apply direct_case_20; reflexivity.
    + apply direct_case_50.
Qed.

Lemma never_direct n s o t :
  g_fixture_rel_Never_execute n s o t <-> o = Unmatch /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; try discriminate; auto.
  - intros [-> ->]. apply direct_case_55. reflexivity.
Qed.

Lemma negated_direct n s o t :
  g_fixture_rel_Negated_execute n s o t <-> o = Success tt /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; clear H.
    match goal with H : g_fixture_rel_Never_execute _ _ _ _ |- _ =>
      apply never_direct in H; destruct H as [-> ->] end.
    match goal with H : g_fixture_rel_Negated_after_call_1_at_1 _ _ _ _ |- _ =>
      inversion H; subst; clear H end; try discriminate; auto.
  - intros [-> ->]. eapply direct_case_61.
    + apply direct_case_55. reflexivity.
    + apply direct_case_64.
Qed.

Lemma arbitrary_direct s o t :
  g_fixture_dec_arbitrary_execute s o t <->
  exists value, o = Success value /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; eauto.
  - intros [value [-> ->]]. constructor.
Qed.

Print Assumptions identity_direct.
Print Assumptions called_direct.
Print Assumptions first_success_excludes_fallback.
Print Assumptions error_direct.
Print Assumptions public_identity_uses_direct.
Print Assumptions sink_direct.
Print Assumptions fallback_direct.
Print Assumptions wraperror_direct.
Print Assumptions never_direct.
Print Assumptions negated_direct.
Print Assumptions arbitrary_direct.
