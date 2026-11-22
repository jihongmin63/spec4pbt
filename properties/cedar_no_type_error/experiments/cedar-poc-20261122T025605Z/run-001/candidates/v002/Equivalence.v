Require Import Specification.cedar.Spec Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v001.Candidate.predicate x <->
  Property.candidates.v002.Candidate.predicate x.
Proof.
  intros x; split.
  - intro H.
    exact (Property.candidates.v002.Candidate.PredicatePrevious x H).
  - intro H.
    destruct H as
      [i Hprev
      | ets acts r Hschema Hrequests
      | ets acts r Hschema Hrequests
      | ets acts r rs es Hschema Hrequests Henvs
      | ets acts r rs es Hschema Hrequests Henvs].
    + exact Hprev.
    + apply Property.candidates.v001.Candidate.PredicateSingle;
        [exact Hschema | exact Hrequests | constructor |].
      apply TLitOther.
      * discriminate.
      * constructor.
    + apply Property.candidates.v001.Candidate.PredicateSingle;
        [exact Hschema | exact Hrequests | constructor |].
      apply TLitFalse. constructor.
    + apply Property.candidates.v001.Candidate.PredicateCons;
        [exact Hschema | exact Hrequests | exact Henvs | constructor |].
      apply TLitOther.
      * discriminate.
      * constructor.
    + apply Property.candidates.v001.Candidate.PredicateCons;
        [exact Hschema | exact Hrequests | exact Henvs | constructor |].
      apply TLitFalse. constructor.
Qed.
