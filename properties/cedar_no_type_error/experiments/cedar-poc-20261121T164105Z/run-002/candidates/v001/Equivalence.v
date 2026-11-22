Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.

Theorem equivalent : forall x : Original.Input,
  Property.Original.predicate x <->
  Property.candidates.v001.Candidate.predicate x.
Proof.
  intro x; split.
  - destruct x as [ets acts rs e es ty expr].
    unfold Original.predicate; simpl.
    intros [Hs [Hr [He [Ht Hexpr]]]].
    inversion He as [s r | s r rs' envs' Htail]; subst.
    + apply Candidate.PredicateSingle; assumption.
    + inversion Htail; subst; eapply Candidate.PredicateCons; eauto.
  - intro Hc.
    destruct Hc; unfold Original.predicate; simpl; repeat split; try assumption.
    + constructor.
    + constructor; assumption.
Qed.
