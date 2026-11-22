Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Import ListNotations.
Open Scope string_scope.

Module V1 := Property.candidates.v001.Candidate.
Module V2 := Property.candidates.v002.Candidate.
Module V3 := Property.candidates.v003.Candidate.

Definition first_entity := MkName "EntityType1" [].
Definition second_entity := MkName "EntityType2" [].
Definition simple_action (id : string) := MkEntityUID (MkName "Action" []) id.
Definition simple_ets : list (EntityName * EntitySchemaEntry) :=
  [(first_entity, MkEntitySchemaEntry [] []);
   (second_entity, MkEntitySchemaEntry [] [])].
Definition simple_acts (id : string) : list (EntityUID * ActionSchemaEntry) :=
  [(simple_action id,
    MkActionSchemaEntry [first_entity] [second_entity] [])].
Definition simple_request (id : string) : RequestType :=
  MkRequest first_entity (simple_action id) second_entity [].
Definition simple_schema (id : string) : Schema :=
  MkSchema simple_ets (simple_acts id).
Definition simple_environment (id : string) : Environment :=
  MkEnvironment (simple_schema id) (simple_request id).
Definition simple_input (id : string) (ty : CedarType)
    (expr : CedarExpr * PathSet) : Original.Input :=
  Original.mkInput simple_ets (simple_acts id) [simple_request id]
    (simple_environment id) [] ty expr.

Lemma first_defined : DefinedName Original.entity_names first_entity.
Proof.
  unfold Original.entity_names, first_entity.
  apply DNFound. reflexivity.
Qed.

Lemma second_defined : DefinedName Original.entity_names second_entity.
Proof.
  unfold Original.entity_names, first_entity, second_entity.
  apply DNRest.
  - discriminate.
  - apply DNFound. reflexivity.
Qed.

Lemma simple_schema_wf : forall id,
    WfSchema Original.entity_names (simple_schema id).
Proof.
  intro id.
  unfold simple_schema, simple_ets, simple_acts.
  eapply WfS.
  - apply WfETSCons.
    + apply first_defined.
    + apply NIECons.
      * unfold first_entity, second_entity. discriminate.
      * apply NIENil.
    + apply WfETSingle; constructor.
    + apply WfETSSingle.
      * apply second_defined.
      * apply WfETSingle; constructor.
  - apply WfACTSSingle. apply WfACTSingle.
    + apply first_defined.
    + apply second_defined.
    + apply WfAttrsNil.
  - reflexivity.
Qed.

Lemma simple_type_wf : forall ty expr,
    V3.SimpleTyped ty expr -> WfCedarType Original.entity_names ty.
Proof.
  intros ty expr H. destruct H.
  - apply WfBoolType.
  - apply WfStringType.
  - apply WfIntType.
  - apply WfRecordTypeNil.
  - apply WfEntityType. apply first_defined.
  - apply WfEntityType. apply second_defined.
Qed.

Lemma simple_has_type : forall id ty expr,
    V3.SimpleTyped ty expr ->
    HasType (somepaths []) (simple_environment id) expr ty.
Proof.
  intros id ty expr H. destruct H.
  - apply TLitOther.
    + discriminate.
    + apply TTrue.
  - apply TLitOther.
    + discriminate.
    + apply TString.
  - apply TLitOther.
    + discriminate.
    + apply TInt.
  - apply TRecNil.
  - unfold simple_environment, simple_request.
    apply TVar. apply TPrincipal.
  - unfold simple_environment, simple_request.
    apply TVar. apply TResource.
Qed.

Lemma simple_in_v1 : forall id ty expr,
    V3.SimpleTyped ty expr -> V1.predicate (simple_input id ty expr).
Proof.
  intros id ty expr H.
  unfold simple_input, simple_environment, simple_schema.
  eapply V1.Build.
  - apply simple_schema_wf.
  - apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
  - apply MkEnvsSingle.
  - apply simple_type_wf with (expr := expr). exact H.
  - apply simple_has_type. exact H.
Qed.

Theorem equivalent : forall x : Original.Input,
    V2.predicate x <-> V3.predicate x.
Proof.
  intro x. split.
  - intro H. apply V3.General. exact H.
  - intro H. destruct H as [id ty expr Htyped | i Hold].
    + apply V2.General.
      change (V1.predicate (simple_input id ty expr)).
      apply simple_in_v1. exact Htyped.
    + exact Hold.
Qed.
