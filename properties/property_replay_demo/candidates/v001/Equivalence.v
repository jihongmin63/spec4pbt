Require Import Property.Original Property.candidates.v001.Candidate.

Theorem equivalent : forall x : Original.Input,
  Original.predicate x <-> Candidate.predicate x.
Proof.
  intro x; split; intro H.
  - destruct H as [x0 b c middle final HExternal HB].
    eapply Candidate.precondition; eassumption.
  - destruct H as [x0 b c middle final HExternal HB].
    eapply Original.precondition; eassumption.
Qed.

Theorem original_witness : forall x : nat,
  Original.predicate (Original.mkInput x) <->
  exists (b c : nat) (middle final : ALCoq.Execution.State),
    FixtureSpec.Generated.InductiveRelations_0000.g_fixture_rel_External_execute
      x {| ALCoq.Execution.next_fresh := 0 |}
      (ALCoq.Execution.Success b) middle /\
    FixtureSpec.Generated.InductiveRelations_0000.g_fixture_rel_B_execute
      b middle (ALCoq.Execution.Success c) final.
Proof.
  intro x; split.
  - intro H. inversion H as [x0 b c middle final HExternal HB]; subst.
    exists b, c, middle, final. split; assumption.
  - intros (b & c & middle & final & HExternal & HB).
    eapply Original.precondition; eassumption.
Qed.
