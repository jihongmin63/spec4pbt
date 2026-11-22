Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.

Theorem equivalent : forall x : Original.Input,
  Property.Original.predicate x <->
  Property.candidates.v001.Candidate.predicate x.
Proof.
  intros [ets acts rs e es ty expr].
  split.
  - unfold Original.predicate; simpl.
    intros [Hs [Hr [He [Ht Hexpr]]]].
    inversion He; subst; constructor; assumption.
  - intro H.
    inversion H; subst.
    unfold Original.predicate; simpl.
    repeat split; assumption.
Qed.
