Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.

Theorem equivalent :
  forall x : Original.Input,
    Property.Original.predicate x <->
    Property.candidates.v001.Candidate.predicate x.
Proof.
  intros [ets acts rs e es ty expr].
  split.
  - intros [Hs [Hr [He [Ht Hexpr]]]].
    constructor; assumption.
  - intro H.
    inversion H; subst.
    repeat split; assumption.
Qed.
