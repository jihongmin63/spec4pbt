Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v002.Candidate.predicate x <->
  Property.candidates.v003.Candidate.predicate x.
Proof.
  intro x. split.
  - intro H. now apply Property.candidates.v003.Candidate.PredicatePrevious.
  - intro H. destruct H as [ets acts r Hwf Hreq | i Hprev].
    + apply Property.candidates.v002.Candidate.PredicateEnvironments.
      * exact Hwf.
      * exact Hreq.
      * apply MkEnvsSingle.
      * apply WfBoolType.
      * apply TLitFalse. apply TFalse.
    + exact Hprev.
Qed.
