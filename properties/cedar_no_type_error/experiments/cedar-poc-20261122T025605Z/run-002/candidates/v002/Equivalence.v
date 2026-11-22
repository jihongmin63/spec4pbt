Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v001.Candidate.predicate x <->
  Property.candidates.v002.Candidate.predicate x.
Proof.
  intros x; split.
  - intro H.
    inversion H; subst.
    + eapply Property.candidates.v002.Candidate.PredicateEnvironments;
        eauto using MkEnvsSingle.
    + eapply Property.candidates.v002.Candidate.PredicateEnvironments;
        eauto using MkEnvsCons.
  - intro H.
    inversion H as [ets acts r rs es ty expr Hschema Hrequests
                    Henvironments Hty Hexpr]; subst.
    inversion Henvironments; subst.
    + eapply Property.candidates.v001.Candidate.PredicateSingle; eauto.
    + eapply Property.candidates.v001.Candidate.PredicateCons; eauto.
Qed.
