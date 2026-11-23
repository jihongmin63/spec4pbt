Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
From ALCoq Require Import Execution.
From CandidateSpec.Generated Require Import InductiveRelations_0000.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v001.Candidate.predicate x <->
  Property.candidates.v002.Candidate.predicate x.
Proof.
  intro input; split; intro H.
  - destruct H as [x b c middle final HExternal HB].
    refine (Property.candidates.v002.Candidate.precondition
      x x b c middle final final HExternal HB _).
    constructor.
  - destruct H as [x helper_value b c middle final helper_final HExternal HB HHelper].
    eapply Property.candidates.v001.Candidate.precondition; eassumption.
Qed.
