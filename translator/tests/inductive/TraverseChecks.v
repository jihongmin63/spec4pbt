From Coq Require Import List Arith.
From ALCoq Require Import Execution Values.
From FixtureSpec.Generated Require Import Calls Bodies_0000 Program InductiveRelations.
From FixtureSpec Require Import EvalFacts.
Import ListNotations.

Definition step (n : nat) := S n.

Lemma step_matches_source n : step n = Nat.add n 1.
Proof. unfold step; rewrite nat_add_one_as_successor; reflexivity. Qed.

Lemma direct_traverse xs s o t :
  g_fixture_dec_each_traverse_1_at_1 xs s o t <->
  o = Success (map step xs) /\ t = s.
Proof.
  split.
  - intro H. induction H; subst; simpl in *.
    + auto.
    + destruct IHg_fixture_dec_each_traverse_1_at_1 as [E T].
      inversion E; subst. unfold step. auto.
    + destruct IHg_fixture_dec_each_traverse_1_at_1 as [E _]. discriminate.
    + destruct IHg_fixture_dec_each_traverse_1_at_1 as [E _]. discriminate.
  - revert s o t. induction xs as [| x xs IH]; intros s o t [-> ->]; simpl.
    + constructor.
    + eapply direct_case_7 with (v_2374656d7032 := x).
      * reflexivity.
      * apply IH. split; reflexivity.
Qed.

Lemma direct_each xs s o t :
  g_fixture_dec_each_execute xs s o t <->
  o = Success (map step xs) /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; clear H;
      match goal with
      | H : g_fixture_dec_each_traverse_1_at_1 _ _ _ _ |- _ =>
          apply direct_traverse in H; destruct H as [E T]
      end; try discriminate; subst; auto.
  - intros [-> ->]. eapply direct_case_13. apply direct_traverse.
    split; reflexivity.
Qed.

Lemma bind_known {A B : Set} (left : Action Call A)
    (right : A -> Action Call B) (value : A) s o t :
  (forall outcome final, Eval (@Body) left s outcome final <->
      outcome = Success value /\ final = s) ->
  Eval (@Body) (Bind left right) s o t <-> Eval (@Body) (right value) s o t.
Proof.
  intro known. rewrite EvalFacts.bind_cases. split.
  - intros [[v [middle [L R]]] | [[E L] | [e [E L]]]];
      apply known in L; destruct L as [V M]; try discriminate.
    inversion V; subst v middle; exact R.
  - intro H. left. exists value, s. split; [apply known; auto | exact H].
Qed.

Lemma step_eval n s o t :
  Eval (@Body)
    (Bind (Return n) (fun a => Bind (Return 1) (fun b => Return (S a))))
    s o t <-> o = Success (step n) /\ t = s.
Proof.
  unfold step. repeat rewrite EvalFacts.bind_return.
  apply EvalFacts.return_value.
Qed.

Lemma eval_traverse_pure (f : nat -> Action Call nat) (g : nat -> nat)
    (Hf : forall x s o t, Eval (@Body) (f x) s o t <->
       o = Success (g x) /\ t = s) :
  forall xs s o t,
    Eval (@Body) (Traverse f xs) s o t <->
    o = Success (map g xs) /\ t = s.
Proof.
  induction xs as [| x xs IH]; intros s o t; cbn [Traverse map].
  - apply EvalFacts.return_value.
  - rewrite (bind_known (f x) _ (g x) s o t (Hf x s)).
    rewrite (bind_known (Traverse f xs) _ (map g xs) s o t (IH s)).
    apply EvalFacts.return_value.
Qed.

Lemma eval_each xs s o t :
  Eval (@Body) (Invoke (C_g_fixture_dec_each xs)) s o t <->
  o = Success (map step xs) /\ t = s.
Proof.
  rewrite EvalFacts.invoke_body.
  cbn [Body B_g_fixture_dec_each Alternatives].
  eapply EvalFacts.or_left_success.
  intros result final.
  change (Eval (@Body)
      (Traverse (fun x : nat =>
        Bind (Return x) (fun a => Bind (Return 1)
          (fun b => Return (S a)))) xs) s result final <->
      result = Success (map step xs) /\ final = s).
  apply eval_traverse_pure.
  intros; apply step_eval.
Qed.

Theorem each_equivalent xs s o t :
  Eval (@Body) (Invoke (C_g_fixture_dec_each xs)) s o t <->
  g_fixture_dec_each_execute xs s o t.
Proof. rewrite eval_each, direct_each. reflexivity. Qed.

Print Assumptions each_equivalent.
