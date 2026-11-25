From Coq Require Import Arith ZArith Lia String.
From ALCoq Require Import Execution Values.
From FixtureSpec.Generated Require Import Casts References InductiveRelations Relations_0000.
Open Scope string_scope.

Definition division_error : ExecutionError :=
  {| error_kind := HostConversion; error_detail := "partial expression failed" |}.

Lemma error_direct s o t :
  g_fixture_dec_error_execute s o t <-> o = Error division_error /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; cbn in *; try discriminate; auto.
  - intros [-> ->]. econstructor; reflexivity.
Qed.

Lemma always_direct n s o t :
  g_fixture_rel_Always_execute n s o t <-> o = Success tt /\ t = s.
Proof.
  split; [intro H; inversion H; subst; auto | intros [-> ->]; constructor].
Qed.

(* A negated judgment that succeeds makes its rule unmatch. *)
Theorem negated_success_unmatches n s o t :
  g_fixture_rel_Refuted_execute n s o t <-> o = Unmatch /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; clear H.
    match goal with H : g_fixture_rel_Always_execute _ _ _ _ |- _ =>
      apply always_direct in H; destruct H as [-> ->] end.
    match goal with H : g_fixture_rel_Refuted_after_call_1_at_1 _ _ _ _ |- _ =>
      inversion H; subst; auto end.
  - intros [-> ->]. econstructor.
    + apply always_direct. split; reflexivity.
    + constructor.
Qed.

Lemma faulty_direct n s o t :
  g_fixture_rel_Faulty_execute n s o t <-> o = Error division_error /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; clear H.
    match goal with H : g_fixture_dec_error_execute _ _ _ |- _ =>
      apply error_direct in H; destruct H as [-> ->] end.
    match goal with H : g_fixture_rel_Faulty_after_call_1_at_1 _ _ _ _ _ |- _ =>
      inversion H; subst; auto end.
  - intros [-> ->]. econstructor.
    + apply error_direct. split; reflexivity.
    + constructor.
Qed.

(* An error inside a negated judgment propagates and blocks the later rule. *)
Theorem negated_error_propagates n s o t :
  g_fixture_rel_Shielded_execute n s o t <-> o = Error division_error /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; clear H.
    match goal with H : g_fixture_rel_Faulty_execute _ _ _ _ |- _ =>
      apply faulty_direct in H; destruct H as [-> ->] end.
    match goal with H : g_fixture_rel_Shielded_after_call_1_at_1 _ _ _ _ _ |- _ =>
      inversion H; subst; auto end.
  - intros [-> ->]. econstructor.
    + apply faulty_direct. split; reflexivity.
    + constructor.
Qed.

Definition left_value n := if Nat.even n then 10 else 20.
Definition right_value n := if Nat.even n then 20 else 10.

Lemma left_value_succ n : left_value (S n) = right_value n.
Proof.
  unfold left_value, right_value. rewrite Nat.even_succ, <- Nat.negb_even.
  now destruct (Nat.even n).
Qed.

Lemma right_value_succ n : right_value (S n) = left_value n.
Proof.
  unfold left_value, right_value. rewrite Nat.even_succ, <- Nat.negb_even.
  now destruct (Nat.even n).
Qed.

Lemma predecessor_cast n :
  g_fixture_cast_0 (Z.sub (Z.of_nat (S n)) (Z.of_nat 1)) = Some n.
Proof.
  unfold g_fixture_cast_0.
  replace (Z.sub (Z.of_nat (S n)) (Z.of_nat 1)) with (Z.of_nat n) by lia.
  rewrite (proj2 (Z.leb_le 0 (Z.of_nat n)) (Nat2Z.is_nonneg n)).
  now rewrite Nat2Z.id.
Qed.

(* Discharge clauses whose guards are false for a successor input. *)
Ltac successor_guards :=
  repeat match goal with
  | H : context [g_fixture_cast_0 (Z.sub (Z.of_nat (S ?k)) (Z.of_nat 1))] |- _ =>
      rewrite (predecessor_cast k) in H
  end;
  repeat match goal with
  | H : Some _ = Some _ |- _ => injection H as H; subst
  end;
  try match goal with
  | H : _ = _ |- _ => solve [cbn in H; discriminate H]
  end.

(* Mutually recursive calls alternate between the two functions. *)
Theorem mutual_calls_alternate n :
  (forall s o t, g_fixture_dec_left_execute n s o t <->
     o = Success (left_value n) /\ t = s) /\
  (forall s o t, g_fixture_dec_right_execute n s o t <->
     o = Success (right_value n) /\ t = s).
Proof.
  induction n as [|n [IHleft IHright]]; split; intros s o t; split.
  - intro H. inversion H; subst; cbn in *; try discriminate; auto.
  - intros [-> ->]. econstructor; reflexivity.
  - intro H. inversion H; subst; cbn in *; try discriminate; auto.
  - intros [-> ->]. econstructor; reflexivity.
  - intro H. inversion H; subst; clear H; [cbn in *; discriminate |].
    match goal with H : g_fixture_dec_left_continue_from_2 _ _ _ _ |- _ =>
      inversion H; subst; clear H end; successor_guards.
    match goal with H : g_fixture_dec_right_execute _ _ _ _ |- _ =>
      apply IHright in H; destruct H as [-> ->] end.
    match goal with H : g_fixture_dec_left_after_call_1_at_2 _ _ _ _ |- _ =>
      inversion H; subst; clear H end.
    rewrite left_value_succ. auto.
  - intros [-> ->]. rewrite left_value_succ.
    constructor 2; [reflexivity |].
    econstructor.
    + reflexivity.
    + rewrite predecessor_cast. reflexivity.
    + apply predecessor_cast.
    + apply IHright. split; reflexivity.
    + constructor.
  - intro H. inversion H; subst; clear H; [cbn in *; discriminate |].
    match goal with H : g_fixture_dec_right_continue_from_2 _ _ _ _ |- _ =>
      inversion H; subst; clear H end; successor_guards.
    match goal with H : g_fixture_dec_left_execute _ _ _ _ |- _ =>
      apply IHleft in H; destruct H as [-> ->] end.
    match goal with H : g_fixture_dec_right_after_call_1_at_2 _ _ _ _ |- _ =>
      inversion H; subst; clear H end.
    rewrite right_value_succ. auto.
  - intros [-> ->]. rewrite right_value_succ.
    constructor 2; [reflexivity |].
    econstructor.
    + reflexivity.
    + rewrite predecessor_cast. reflexivity.
    + apply predecessor_cast.
    + apply IHleft. split; reflexivity.
    + constructor.
Qed.

Lemma apply_source A B (reference : FunctionRef A B) input s o t :
  R_apply A B reference input s o t ->
  match reference in FunctionRef X Y return X -> State -> Outcome Y -> State -> Prop with
  | Ref_g_fixture_dec_left => g_fixture_dec_left_execute
  end input s o t.
Proof. intro H. induction H. assumption. Qed.

(* A function reference reaches the mutually recursive group. *)
Theorem callback_reaches_mutual_group n s o t :
  g_fixture_dec_through_x5f_left_execute n s o t <->
  o = Success (left_value n) /\ t = s.
Proof.
  destruct (mutual_calls_alternate n) as [Hleft _].
  split.
  - intro H. inversion H; subst; clear H.
    match goal with H : g_fixture_dec_apply_x5f_nat_execute _ _ _ _ _ |- _ =>
      inversion H; subst; clear H end.
    match goal with H : R_apply _ _ _ _ _ _ _ |- _ =>
      apply apply_source, Hleft in H; destruct H as [-> ->] end.
    match goal with H : g_fixture_dec_apply_x5f_nat_after_call_1_at_1 _ _ _ _ |- _ =>
      inversion H; subst; clear H end.
    match goal with H : g_fixture_dec_through_x5f_left_after_call_1_at_1 _ _ _ _ |- _ =>
      inversion H; subst; clear H end.
    auto.
  - intros [-> ->]. econstructor.
    + econstructor.
      * econstructor. apply Hleft. split; reflexivity.
      * constructor.
    + constructor.
Qed.

Example mutual_recursion : g_fixture_dec_left 2 10.
Proof.
  exists {| next_fresh := 0 |}.
  apply (proj1 (mutual_calls_alternate 2)). split; reflexivity.
Qed.

Example callback_through_mutual_group : g_fixture_dec_through_x5f_left 1 20.
Proof.
  exists {| next_fresh := 0 |}.
  apply callback_reaches_mutual_group. split; reflexivity.
Qed.

Print Assumptions negated_success_unmatches.
Print Assumptions negated_error_propagates.
Print Assumptions mutual_calls_alternate.
Print Assumptions callback_reaches_mutual_group.
Print Assumptions mutual_recursion.
Print Assumptions callback_through_mutual_group.
