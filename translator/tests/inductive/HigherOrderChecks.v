From Coq Require Import Arith.
From ALCoq Require Import Execution Values.
From FixtureSpec.Generated Require Import References InductiveRelations.

Lemma identity_direct n s o t :
  g_fixture_dec_identity_execute n s o t <-> o = Success n /\ t = s.
Proof.
  split; [intro H; inversion H; subst; auto | intros [-> ->]; constructor].
Qed.

Lemma apply_source A B (reference : FunctionRef A B) input s o t :
  R_apply A B reference input s o t ->
  match reference in FunctionRef X Y return X -> State -> Outcome Y -> State -> Prop with
  | Ref_g_fixture_dec_identity => g_fixture_dec_identity_execute
  end input s o t.
Proof. intro H. induction H. assumption. Qed.

Lemma apply_reference_direct n s o t :
  R_apply nat nat Ref_g_fixture_dec_identity n s o t <->
  o = Success n /\ t = s.
Proof.
  split.
  - intro H. apply apply_source in H.
    apply identity_direct in H. exact H.
  - intros [-> ->]. eapply direct_case_4.
    apply identity_direct. split; reflexivity.
Qed.

Lemma after_identity (A : Set) (ops : ValueOps@{Set} A)
    before state after final :
  g_fixture_dec_apply_after_call_1_at_1 A ops before state after final ->
  after = before /\ final = state.
Proof. intro H. induction H; auto. Qed.

Lemma apply_step (A : Set) (ops : ValueOps@{Set} A)
    (reference : FunctionRef A A) input s o t :
  g_fixture_dec_apply_execute A ops reference input s o t ->
  exists result middle,
    R_apply A A reference input s result middle /\
    g_fixture_dec_apply_after_call_1_at_1 A ops result middle o t.
Proof. intro H. induction H. eauto. Qed.

Lemma apply_direct n s o t :
  g_fixture_dec_apply_execute nat nat_ops Ref_g_fixture_dec_identity n s o t <->
  o = Success n /\ t = s.
Proof.
  split.
  - intro H. apply apply_step in H.
    destruct H as [result [middle [C K]]].
    apply apply_reference_direct in C. destruct C as [E T].
    apply after_identity in K. destruct K as [E' T'].
    subst. split; reflexivity.
  - intros [-> ->]. eapply direct_case_14.
    + apply apply_reference_direct. split; reflexivity.
    + apply direct_case_16.
Qed.

Lemma call_direct n s o t :
  g_fixture_dec_call_x5f_identity_execute n s o t <->
  o = Success n /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; clear H.
    match goal with H : g_fixture_dec_apply_execute _ _ _ _ _ _ _ |- _ =>
      apply apply_direct in H; destruct H as [E T]
    end.
    subst.
    match goal with H : g_fixture_dec_call_x5f_identity_after_call_1_at_1 _ _ _ _ |- _ =>
      inversion H; subst; clear H
    end; auto; discriminate.
  - intros [-> ->]. eapply direct_case_25.
    + apply apply_direct. split; reflexivity.
    + apply direct_case_27.
Qed.

Lemma polymorphic_direct (A : Set) (ops : ValueOps@{Set} A) (value : A) s o t :
  g_fixture_dec_poly_x5f_identity_execute A ops value s o t <->
  o = Success value /\ t = s.
Proof.
  split; [intro H; induction H; auto | intros [-> ->]; constructor].
Qed.

Print Assumptions apply_reference_direct.
Print Assumptions apply_direct.
Print Assumptions call_direct.
Print Assumptions polymorphic_direct.
Print Assumptions apply_source.
Print Assumptions after_identity.
Print Assumptions apply_step.
