From Coq Require Import Arith.
From ALCoq Require Import Execution Values.
From FixtureSpec.Generated Require Import Calls References Bodies_0000 Program InductiveRelations.
From FixtureSpec Require Import EvalFacts.

Lemma identity_direct n s o t :
  g_fixture_dec_identity_execute n s o t <-> o = Success n /\ t = s.
Proof.
  split; [intro H; inversion H; subst; auto | intros [-> ->]; constructor].
Qed.

Lemma identity_eval n s o t :
  Eval (@Body) (Invoke (C_g_fixture_dec_identity n)) s o t <->
  o = Success n /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_dec_identity Alternatives].
  eapply EvalFacts.or_left_success.
  intros result final. apply EvalFacts.return_value.
Qed.

Lemma apply_forward A B (reference : FunctionRef A B) input s o t :
  R_apply A B reference input s o t ->
  Eval (@Body) (Invoke (ApplyReference reference input)) s o t.
Proof.
  intro H. induction H.
  apply EvalFacts.invoke_body.
  cbn [Body reference_body].
  apply identity_eval.
  apply identity_direct in H. exact H.
Qed.

Lemma apply_reference_direct n s o t :
  R_apply nat nat Ref_g_fixture_dec_identity n s o t <->
  o = Success n /\ t = s.
Proof.
  split.
  - intro H. apply apply_forward in H.
    rewrite EvalFacts.invoke_body in H.
    cbn [Body reference_body] in H.
    apply identity_eval in H. exact H.
  - intros [-> ->]. eapply direct_case_4. apply identity_direct.
    split; reflexivity.
Qed.

Lemma apply_eval n s o t :
  Eval (@Body)
    (Invoke (C_g_fixture_dec_apply nat nat_ops Ref_g_fixture_dec_identity n))
    s o t <-> o = Success n /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_dec_apply Alternatives].
  eapply EvalFacts.or_left_success.
  intros result final.
  rewrite EvalFacts.bind_return, EvalFacts.invoke_body.
  cbn [Body reference_body].
  apply identity_eval.
Qed.

Lemma after_identity (A : Set) (ops : ValueOps@{Set} A)
    before state after final :
  g_fixture_dec_apply_after_call_1_at_1 A ops before state after final ->
  after = before /\ final = state.
Proof. intro H. induction H; auto. Qed.

Lemma apply_execute_forward (A : Set) (ops : ValueOps@{Set} A)
    (reference : FunctionRef A A) value s o t :
  g_fixture_dec_apply_execute A ops reference value s o t ->
  Eval (@Body) (Invoke (C_g_fixture_dec_apply A ops reference value)) s o t.
Proof.
  intro H. induction H.
  apply after_identity in H0. destruct H0 as [-> ->].
  apply apply_forward in H.
  apply EvalFacts.invoke_body.
  cbn [Body B_g_fixture_dec_apply Alternatives].
  destruct call_outcome_10 as [v | | err].
  - apply eval_or_success. eapply eval_bind_success; [constructor | exact H].
  - eapply eval_or_unmatch.
    + eapply eval_bind_success; [constructor | exact H].
    + constructor.
  - apply eval_or_error. eapply eval_bind_success; [constructor | exact H].
Qed.

Lemma apply_direct n s o t :
  g_fixture_dec_apply_execute nat nat_ops Ref_g_fixture_dec_identity n s o t <->
  o = Success n /\ t = s.
Proof.
  split.
  - intro H. apply apply_execute_forward in H. apply apply_eval in H. exact H.
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

Lemma call_eval n s o t :
  Eval (@Body) (Invoke (C_g_fixture_dec_call_x5f_identity n)) s o t <->
  o = Success n /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_dec_call_x5f_identity Alternatives].
  eapply EvalFacts.or_left_success.
  intros result final.
  repeat rewrite EvalFacts.bind_return.
  apply apply_eval.
Qed.

Theorem higher_order_equivalent n s o t :
  Eval (@Body) (Invoke (C_g_fixture_dec_call_x5f_identity n)) s o t <->
  g_fixture_dec_call_x5f_identity_execute n s o t.
Proof. rewrite call_eval, call_direct. reflexivity. Qed.

Lemma polymorphic_direct (A : Set) (ops : ValueOps@{Set} A) (value : A) s o t :
  g_fixture_dec_poly_x5f_identity_execute A ops value s o t <->
  o = Success value /\ t = s.
Proof.
  split; [intro H; induction H; auto | intros [-> ->]; constructor].
Qed.

Lemma polymorphic_eval (A : Set) (ops : ValueOps@{Set} A) (value : A) s o t :
  Eval (@Body) (Invoke (C_g_fixture_dec_poly_x5f_identity A ops value)) s o t <->
  o = Success value /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_dec_poly_x5f_identity Alternatives].
  eapply EvalFacts.or_left_success.
  intros result final. apply EvalFacts.return_value.
Qed.

Theorem polymorphic_equivalent (A : Set) (ops : ValueOps@{Set} A)
    (value : A) s o t :
  Eval (@Body) (Invoke (C_g_fixture_dec_poly_x5f_identity A ops value)) s o t <->
  g_fixture_dec_poly_x5f_identity_execute A ops value s o t.
Proof. rewrite polymorphic_eval, polymorphic_direct. reflexivity. Qed.

Print Assumptions higher_order_equivalent.
Print Assumptions polymorphic_equivalent.
