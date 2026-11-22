Require Import List String Specification.cedar.Spec Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Import ListNotations.

Lemma lift_v001 : forall x : Original.Input,
  Property.candidates.v001.Candidate.predicate x ->
  Property.candidates.v004.Candidate.predicate x.
Proof.
  intros x H.
  apply Property.candidates.v004.Candidate.PredicatePrevious.
  apply Property.candidates.v003.Candidate.PredicatePrevious.
  apply Property.candidates.v002.Candidate.PredicatePrevious.
  exact H.
Qed.

Lemma int_typing : forall env n,
  HasType (somepaths []) env (lit (int n), somepaths []) intType.
Proof.
  intros env n.
  apply TLitOther.
  - discriminate.
  - constructor.
Qed.

Lemma string_typing : forall env s,
  HasType (somepaths []) env (lit (stringLit s), somepaths []) stringType.
Proof.
  intros env s.
  apply TLitOther.
  - discriminate.
  - constructor.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v004.Candidate.predicate x <->
  Property.candidates.v005.Candidate.predicate x.
Proof.
  intro x; split.
  - intro H. apply Property.candidates.v005.Candidate.PredicatePrevious. exact H.
  - intro H.
    destruct H as
      [i H
      | ets acts r n Hwf Hacts
      | ets acts r rs es n Hwf Hacts Henv
      | ets acts r s Hwf Hacts
      | ets acts r rs es s Hwf Hacts Henv].
    + exact H.
    + apply lift_v001.
      eapply Property.candidates.v001.Candidate.PredicateSingle.
      * exact Hwf.
      * exact Hacts.
      * constructor.
      * apply int_typing.
    + apply lift_v001.
      eapply Property.candidates.v001.Candidate.PredicateCons.
      * exact Hwf.
      * exact Hacts.
      * exact Henv.
      * constructor.
      * apply int_typing.
    + apply lift_v001.
      eapply Property.candidates.v001.Candidate.PredicateSingle.
      * exact Hwf.
      * exact Hacts.
      * constructor.
      * apply string_typing.
    + apply lift_v001.
      eapply Property.candidates.v001.Candidate.PredicateCons.
      * exact Hwf.
      * exact Hacts.
      * exact Henv.
      * constructor.
      * apply string_typing.
Qed.
