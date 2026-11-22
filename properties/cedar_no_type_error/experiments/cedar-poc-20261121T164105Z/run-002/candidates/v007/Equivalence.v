Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Require Import Property.candidates.v006.Candidate.
Require Import Property.candidates.v007.Candidate.
Import ListNotations.
Open Scope string_scope.

Module V001 := Property.candidates.v001.Candidate.
Module V002 := Property.candidates.v002.Candidate.
Module V003 := Property.candidates.v003.Candidate.
Module V004 := Property.candidates.v004.Candidate.
Module V005 := Property.candidates.v005.Candidate.
Module V006 := Property.candidates.v006.Candidate.
Module V007 := Property.candidates.v007.Candidate.

Lemma boolean_and_has_type : forall env expr ty,
  V007.BooleanAndTyped expr ty ->
  HasType (somepaths []) env expr ty.
Proof.
  intros env expr ty H. destruct H.
  - apply TAnd. apply TCondTrue.
    + apply TLitOther. discriminate. constructor.
    + constructor.
  - apply TAnd. apply TCondTrue.
    + apply TLitFalse. constructor.
    + constructor.
  - apply TAnd. apply TCondFalse.
    + constructor.
    + apply TLitFalse. constructor.
  - apply TAnd. apply TCondFalse.
    + constructor.
    + apply TLitFalse. constructor.
Qed.

Lemma fixed_schema_wf : forall p r action_id,
  DefinedName Original.entity_names p ->
  DefinedName Original.entity_names r ->
  WfSchema Original.entity_names
    (MkSchema
      [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
       (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
      [(MkEntityUID (MkName "Action" []) action_id,
        MkActionSchemaEntry [p] [r] [])]).
Proof.
  intros p r action_id Hp Hr.
  eapply WfS.
  - unfold Original.entity_names.
    eapply WfETSCons.
    + apply DNFound. reflexivity.
    + apply NIECons. discriminate. constructor.
    + repeat constructor.
    + apply WfETSSingle.
      * apply DNRest. discriminate. apply DNFound. reflexivity.
      * repeat constructor.
  - apply WfACTSSingle. apply WfACTSingle; [exact Hp | exact Hr | constructor].
  - reflexivity.
Qed.

Theorem equivalent : forall x : Original.Input,
  V006.predicate x <-> V007.predicate x.
Proof.
  intro x. split.
  - intro H. apply V007.PredicatePredecessor. exact H.
  - intro H. destruct H as [p r action_id expr ty Hp Hr Htyped | input Hprev].
    + destruct Htyped;
        apply V006.PredicatePredecessor;
        apply V005.PredicatePredecessor;
        apply V004.PredicatePredecessor;
        apply V003.PredicatePredecessor;
        apply V002.PredicateGeneral;
        eapply V001.PredicateSingle.
      all: try (apply fixed_schema_wf; assumption).
      all: try (apply ASTESingle; apply ASTRTSingle; apply ATRTSingle).
      all: try apply WfBoolType.
      all: apply boolean_and_has_type; constructor.
    + exact Hprev.
Qed.
