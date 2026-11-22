Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.

Theorem equivalent : forall x : Original.Input,
  Property.Original.predicate x <->
  Property.candidates.v001.Candidate.predicate x.
Proof.
  intros [ets acts rs e es ty expr].
  split.
  - intros [Hschema [Hrequests [Henv [Htype Hexpr]]]].
    inversion Henv; subst; simpl in *;
      match goal with H : _ = rs |- _ => rewrite <- H in * end.
    + apply Candidate.PredicateSingle; assumption.
    + apply Candidate.PredicateCons; assumption.
  - intro Hcandidate.
    inversion Hcandidate; subst; unfold Original.predicate; simpl;
      repeat split; try assumption.
    + apply Spec.MkEnvsSingle.
    + apply Spec.MkEnvsCons; assumption.
Qed.
