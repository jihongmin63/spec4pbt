Require Import List Specification.cedar.Spec Property.Original
  Property.candidates.v001.Candidate.

Theorem equivalent : forall x : Original.Input,
  Property.Original.predicate x <->
  Property.candidates.v001.Candidate.predicate x.
Proof.
  intros [ets acts rs e es ty expr].
  split.
  - unfold Property.Original.predicate; simpl.
    intros [Hs [Hr [He [Ht Hexpr]]]].
    inversion He; subst.
    + apply Candidate.PredicateSingle; assumption.
    + eapply Candidate.PredicateCons; eassumption.
  - intro H.
    inversion H; subst; unfold Property.Original.predicate; simpl;
      repeat split; try assumption.
    + apply MkEnvsSingle.
    + apply MkEnvsCons; assumption.
Qed.
