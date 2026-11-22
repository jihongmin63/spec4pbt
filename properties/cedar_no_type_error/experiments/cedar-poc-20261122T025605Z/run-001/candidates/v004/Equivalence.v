Require Import List String Specification.cedar.Spec Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Import ListNotations.

Module P1 := Property.candidates.v001.Candidate.
Module P2 := Property.candidates.v002.Candidate.
Module P3 := Property.candidates.v003.Candidate.
Module P4 := Property.candidates.v004.Candidate.

Lemma previous_single : forall ets acts r ty expr,
  WfSchema Original.entity_names (MkSchema ets acts) ->
  ActionSchemaToRequestTypes acts [] [r] ->
  WfCedarType Original.entity_names ty ->
  HasType (somepaths []) (MkEnvironment (MkSchema ets acts) r) expr ty ->
  P3.predicate (Original.mkInput ets acts [r]
    (MkEnvironment (MkSchema ets acts) r) [] ty expr).
Proof.
  intros ets acts r ty expr Hschema Hrequests Hwf Htype.
  apply P3.PredicatePrevious.
  apply P2.PredicatePrevious.
  apply P1.PredicateSingle; assumption.
Qed.

Lemma previous_cons : forall ets acts r rs es ty expr,
  WfSchema Original.entity_names (MkSchema ets acts) ->
  ActionSchemaToRequestTypes acts [] (r :: rs) ->
  SchemaToEnvironments (MkSchema ets acts) rs es ->
  WfCedarType Original.entity_names ty ->
  HasType (somepaths []) (MkEnvironment (MkSchema ets acts) r) expr ty ->
  P3.predicate (Original.mkInput ets acts (r :: rs)
    (MkEnvironment (MkSchema ets acts) r) es ty expr).
Proof.
  intros ets acts r rs es ty expr Hschema Hrequests Henvs Hwf Htype.
  apply P3.PredicatePrevious.
  apply P2.PredicatePrevious.
  apply P1.PredicateCons; assumption.
Qed.

Lemma equal_int_type : forall env n,
  HasType (somepaths []) env
    (binaryApp equals (lit (int n)) (lit (int n)), somepaths [])
    (boolType tt_).
Proof.
  intros env n. eapply TEqLitTrue. constructor.
Qed.

Lemma equal_string_type : forall env s,
  HasType (somepaths []) env
    (binaryApp equals (lit (stringLit s)) (lit (stringLit s)), somepaths [])
    (boolType tt_).
Proof.
  intros env s. eapply TEqLitTrue. constructor.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v003.Candidate.predicate x <->
  Property.candidates.v004.Candidate.predicate x.
Proof.
  intro x. split.
  - intro H. apply P4.PredicatePrevious. exact H.
  - intro H. destruct H as
      [i Hprevious
      | ets acts r n Hschema Hrequests
      | ets acts r rs es n Hschema Hrequests Henvs
      | ets acts r s Hschema Hrequests
      | ets acts r rs es s Hschema Hrequests Henvs].
    + exact Hprevious.
    + apply previous_single; try assumption.
      * constructor.
      * apply equal_int_type.
    + apply previous_cons; try assumption.
      * constructor.
      * apply equal_int_type.
    + apply previous_single; try assumption.
      * constructor.
      * apply equal_string_type.
    + apply previous_cons; try assumption.
      * constructor.
      * apply equal_string_type.
Qed.
