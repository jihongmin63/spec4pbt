Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Require Import Property.candidates.v006.Candidate.
Require Import Property.candidates.v007.Candidate.
Require Import Property.candidates.v008.Candidate.
Import ListNotations.

Lemma tiny_schema_wf : forall ets acts r,
  Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
  WfSchema Original.entity_names (MkSchema ets acts).
Proof.
  intros ets acts r H.
  inversion H; subst.
  eapply WfS.
  - unfold Original.entity_names.
    apply WfETSCons.
    + apply DNFound; reflexivity.
    + apply NIECons; [discriminate | constructor].
    + constructor; constructor.
    + apply WfETSSingle.
      * apply DNRest; [discriminate | apply DNFound; reflexivity].
      * constructor; constructor.
  - repeat constructor; try discriminate; try reflexivity.
  - reflexivity.
Qed.

Lemma tiny_schema_requests : forall ets acts r,
  Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
  ActionSchemaToRequestTypes acts [] [r].
Proof.
  intros ets acts r H.
  inversion H; subst.
  repeat constructor.
Qed.

Lemma tiny_int_has_type : forall a V e,
  Property.candidates.v005.Candidate.TinyIntExpr e ->
  HasType a V (e, somepaths []) intType.
Proof.
  intros a V e H; induction H.
  - apply TLitOther; [discriminate | constructor].
  - eapply TNeg; eassumption.
  - eapply TAdd; eassumption.
  - eapply TSub; eassumption.
  - eapply TMul; eassumption.
Qed.

Lemma int_record_prior : forall ets acts r field value,
  Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
  Property.candidates.v005.Candidate.TinyIntExpr value ->
  Property.candidates.v007.Candidate.predicate
    (Original.mkInput ets acts [r]
      (MkEnvironment (MkSchema ets acts) r) []
      (recordTypeCons field false intType recordTypeNil)
      (recExprCons field value recExprNil, somepaths [])).
Proof.
  intros ets acts r field value Hschema Hvalue.
  apply Property.candidates.v007.Candidate.PredicatePrevious.
  apply Property.candidates.v006.Candidate.PredicatePrevious.
  apply Property.candidates.v005.Candidate.PredicatePrevious.
  apply Property.candidates.v004.Candidate.PredicatePrevious.
  apply Property.candidates.v003.Candidate.PredicatePrevious.
  eapply Property.candidates.v002.Candidate.PredicateEnvironments.
  - eapply tiny_schema_wf; eassumption.
  - eapply tiny_schema_requests; eassumption.
  - constructor.
  - apply WfRecordTypeConsNil; constructor.
  - eapply TRecCons with (x := somepaths []) (rx := somepaths []).
    + apply tiny_int_has_type; assumption.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v007.Candidate.predicate x <->
  Property.candidates.v008.Candidate.predicate x.
Proof.
  intro x; split.
  - intro H; apply Property.candidates.v008.Candidate.PredicatePrevious; exact H.
  - intro H; destruct H as [ets acts r field value Hschema Hvalue | i Hprevious].
    + eapply int_record_prior; eassumption.
    + exact Hprevious.
Qed.
