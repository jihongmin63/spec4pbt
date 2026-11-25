From Coq Require Import List Arith.
From ALCoq Require Import Execution Values.
From FixtureSpec.Generated Require Import InductiveRelations.
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

Print Assumptions direct_traverse.
Print Assumptions direct_each.
