Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Import ListNotations.
Open Scope string_scope.

Lemma tiny_schema_wf : forall ets acts r,
  Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
  WfSchema Original.entity_names (MkSchema ets acts).
Proof.
  intros ets acts r H.
  inversion H; subst.
  unfold Original.entity_names.
  eapply WfS with
    (acts := [(MkEntityUID (MkName "Action" []) id,
               MkActionSchemaEntry
                 [MkName "EntityType1" []]
                 [MkName "EntityType1" []] [])]).
  - eapply WfETSCons.
    + apply DNFound; reflexivity.
    + repeat (constructor; try discriminate).
    + repeat constructor.
    + eapply WfETSSingle.
      * eapply DNRest.
        -- discriminate.
        -- apply DNFound; reflexivity.
      * repeat constructor.
  - repeat (constructor; try discriminate; try reflexivity).
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

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v004.Candidate.predicate x <->
  Property.candidates.v005.Candidate.predicate x.
Proof.
  intro x; split.
  - intro H.
    apply Property.candidates.v005.Candidate.PredicatePrevious.
    exact H.
  - intro H.
    destruct H as [ets acts r e Hschema Hexpr | i Hprevious].
    + apply Property.candidates.v004.Candidate.PredicatePrevious.
      apply Property.candidates.v003.Candidate.PredicatePrevious.
      eapply Property.candidates.v002.Candidate.PredicateEnvironments
        with (r := r) (rs := []) (es := []).
      * apply tiny_schema_wf with (r := r); exact Hschema.
      * eapply tiny_schema_requests; exact Hschema.
      * constructor.
      * constructor.
      * apply tiny_int_has_type; exact Hexpr.
    + exact Hprevious.
Qed.
