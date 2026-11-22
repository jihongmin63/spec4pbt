From Coq Require Import Arith String.
From ALCoq Require Import Execution Values.
From FixtureSpec.Generated Require Import Calls Bodies_0000 Program InductiveRelations Relations_0000.
From FixtureSpec Require Import EvalFacts.
Open Scope string_scope.

Lemma identity_direct n s o t :
  g_fixture_rel_Identity_execute n s o t <-> o = Success n /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; auto.
  - intros [-> ->]. constructor.
Qed.

Lemma identity_eval n s o t :
  Eval (@Body) (Invoke (C_g_fixture_rel_Identity n)) s o t <->
  o = Success n /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_rel_Identity Alternatives].
  eapply EvalFacts.or_left_success.
  intros result final.
  rewrite EvalFacts.bind_return, EvalFacts.return_value.
  reflexivity.
Qed.

Theorem identity_equivalent n s o t :
  Eval (@Body) (Invoke (C_g_fixture_rel_Identity n)) s o t <->
  g_fixture_rel_Identity_execute n s o t.
Proof. rewrite identity_eval, identity_direct. reflexivity. Qed.

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

Lemma bind_identity n (k : nat -> Action Call nat) s o t :
  Eval (@Body) (Bind (Invoke (C_g_fixture_rel_Identity n)) k) s o t <->
  Eval (@Body) (k n) s o t.
Proof.
  rewrite EvalFacts.bind_cases.
  split.
  - intros [[v [middle [H R]]] | [[V H] | [e [V H]]]];
      apply identity_eval in H; destruct H as [E T]; try discriminate E.
    inversion E; subst v; subst middle; exact R.
  - intro H. left. exists n, s. split; [apply identity_eval | exact H].
    split; reflexivity.
Qed.

Lemma called_eval n s o t :
  Eval (@Body) (Invoke (C_g_fixture_rel_Called n)) s o t <->
  o = Success n /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_rel_Called Alternatives].
  eapply EvalFacts.or_left_success.
  intros result final.
  rewrite EvalFacts.bind_return, bind_identity.
  repeat rewrite EvalFacts.bind_return.
  rewrite EvalFacts.return_value.
  reflexivity.
Qed.

Theorem called_equivalent n s o t :
  Eval (@Body) (Invoke (C_g_fixture_rel_Called n)) s o t <->
  g_fixture_rel_Called_execute n s o t.
Proof. rewrite called_eval, called_direct. reflexivity. Qed.

Definition division_error : ExecutionError :=
  {| error_kind := HostConversion; error_detail := "partial expression failed" |}.

Lemma error_direct s o t :
  g_fixture_dec_error_execute s o t <-> o = Error division_error /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; cbn in *; try discriminate; auto.
  - intros [-> ->]. apply direct_case_20; reflexivity.
Qed.

Lemma error_eval s o t :
  Eval (@Body) (Invoke C_g_fixture_dec_error) s o t <->
  o = Error division_error /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_dec_error Alternatives].
  eapply EvalFacts.or_left_error.
  intros result final.
  repeat rewrite EvalFacts.bind_return.
  change (Eval (@Body) (Raise division_error) s result final <->
    result = Error division_error /\ final = s).
  apply EvalFacts.raise_value.
Qed.

Theorem error_equivalent s o t :
  Eval (@Body) (Invoke C_g_fixture_dec_error) s o t <->
  g_fixture_dec_error_execute s o t.
Proof. rewrite error_eval, error_direct. reflexivity. Qed.

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

Lemma sink_eval s o t :
  Eval (@Body) (Invoke C_g_fixture_dec_sink) s o t <->
  o = Unmatch /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_dec_sink Alternatives].
  apply EvalFacts.unmatched_value.
Qed.

Theorem sink_equivalent s o t :
  Eval (@Body) (Invoke C_g_fixture_dec_sink) s o t <->
  g_fixture_dec_sink_execute s o t.
Proof. rewrite sink_eval, sink_direct. reflexivity. Qed.

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

Lemma fallback_eval s o t :
  Eval (@Body) (Invoke C_g_fixture_dec_fallback) s o t <->
  o = Success 9 /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_dec_fallback Alternatives].
  rewrite (EvalFacts.or_left_unmatch _ _ _ _ _ _ (sink_eval s)).
  eapply EvalFacts.or_left_success.
  intros result final. apply EvalFacts.return_value.
Qed.

Theorem fallback_equivalent s o t :
  Eval (@Body) (Invoke C_g_fixture_dec_fallback) s o t <->
  g_fixture_dec_fallback_execute s o t.
Proof. rewrite fallback_eval, fallback_direct. reflexivity. Qed.

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

Lemma wraperror_eval s o t :
  Eval (@Body) (Invoke C_g_fixture_dec_wraperror) s o t <->
  o = Error division_error /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_dec_wraperror Alternatives].
  eapply EvalFacts.or_left_error.
  intros result final. apply error_eval.
Qed.

Theorem wraperror_equivalent s o t :
  Eval (@Body) (Invoke C_g_fixture_dec_wraperror) s o t <->
  g_fixture_dec_wraperror_execute s o t.
Proof. rewrite wraperror_eval, wraperror_direct. reflexivity. Qed.

Lemma never_direct n s o t :
  g_fixture_rel_Never_execute n s o t <-> o = Unmatch /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; try discriminate; auto.
  - intros [-> ->]. apply direct_case_55. reflexivity.
Qed.

Lemma never_eval n s o t :
  Eval (@Body) (Invoke (C_g_fixture_rel_Never n)) s o t <->
  o = Unmatch /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_rel_Never Alternatives].
  rewrite (EvalFacts.or_left_unmatch _ _ _ _ _ _).
  - apply EvalFacts.unmatched_value.
  - intros result final. repeat rewrite EvalFacts.bind_return.
    cbn [Guard]. apply EvalFacts.bind_unmatched.
Qed.

Theorem never_equivalent n s o t :
  Eval (@Body) (Invoke (C_g_fixture_rel_Never n)) s o t <->
  g_fixture_rel_Never_execute n s o t.
Proof. rewrite never_eval, never_direct. reflexivity. Qed.

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

Lemma negated_eval n s o t :
  Eval (@Body) (Invoke (C_g_fixture_rel_Negated n)) s o t <->
  o = Success tt /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_rel_Negated Alternatives].
  eapply EvalFacts.or_left_success.
  intros result final. repeat rewrite EvalFacts.bind_return.
  rewrite EvalFacts.bind_cases.
  split.
  - intros [[v [middle [L R]]] | [[V L] | [e [V L]]]].
    + apply (proj1 (EvalFacts.negate_unmatched _ _ _ _ _ (never_eval n s))) in L.
      destruct L as [E T]. inversion E; subst v middle.
      now apply EvalFacts.return_value in R.
    + apply (proj1 (EvalFacts.negate_unmatched _ _ _ _ _ (never_eval n s))) in L.
      destruct L as [E _]. discriminate E.
    + apply (proj1 (EvalFacts.negate_unmatched _ _ _ _ _ (never_eval n s))) in L.
      destruct L as [E _]. discriminate E.
  - intros [-> ->]. left. exists tt, s. split.
    + apply (proj2 (EvalFacts.negate_unmatched _ _ _ _ _ (never_eval n s))).
      split; reflexivity.
    + constructor.
Qed.

Theorem negated_equivalent n s o t :
  Eval (@Body) (Invoke (C_g_fixture_rel_Negated n)) s o t <->
  g_fixture_rel_Negated_execute n s o t.
Proof. rewrite negated_eval, negated_direct. reflexivity. Qed.

Lemma arbitrary_direct s o t :
  g_fixture_dec_arbitrary_execute s o t <->
  exists value, o = Success value /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; eauto.
  - intros [value [-> ->]]. constructor.
Qed.

Lemma arbitrary_eval s o t :
  Eval (@Body) (Invoke C_g_fixture_dec_arbitrary) s o t <->
  exists value, o = Success value /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_dec_arbitrary].
  split.
  - intro H. inversion H; subst; eauto.
  - intros [value [-> ->]]. constructor.
Qed.

Theorem arbitrary_equivalent s o t :
  Eval (@Body) (Invoke C_g_fixture_dec_arbitrary) s o t <->
  g_fixture_dec_arbitrary_execute s o t.
Proof. rewrite arbitrary_eval, arbitrary_direct. reflexivity. Qed.

Print Assumptions identity_equivalent.
Print Assumptions called_equivalent.
Print Assumptions error_equivalent.
Print Assumptions sink_equivalent.
Print Assumptions fallback_equivalent.
Print Assumptions wraperror_equivalent.
Print Assumptions never_equivalent.
Print Assumptions negated_equivalent.
Print Assumptions arbitrary_equivalent.
