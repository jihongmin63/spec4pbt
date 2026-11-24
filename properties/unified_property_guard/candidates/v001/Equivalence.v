Require Import Property.Original Property.candidates.v001.Candidate.
Theorem equivalent : forall x : Original.Input,
  Original.predicate x <-> Candidate.predicate x.
Proof.
  intro x; split; intro H; destruct H; econstructor; eassumption.
Qed.
