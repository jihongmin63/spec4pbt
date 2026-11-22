Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Require Import Property.candidates.v006.Candidate.
Import ListNotations.
Open Scope string_scope.

Module C1 := Property.candidates.v001.Candidate.
Module C2 := Property.candidates.v002.Candidate.
Module C3 := Property.candidates.v003.Candidate.
Module C4 := Property.candidates.v004.Candidate.
Module C5 := Property.candidates.v005.Candidate.
Module C6 := Property.candidates.v006.Candidate.

Definition record_ets : list (EntityName * EntitySchemaEntry) :=
  [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
   (MkName "EntityType2" [], MkEntitySchemaEntry [] [])].

Lemma record_ets_wf :
  WfETS Original.entity_names Original.entity_names record_ets.
Proof.
  unfold Original.entity_names, record_ets.
  apply WfETSCons.
  - apply DNFound. reflexivity.
  - apply NIECons; [discriminate | constructor].
  - apply WfETSingle; constructor.
  - apply WfETSSingle.
    + apply DNRest; [discriminate | apply DNFound; reflexivity].
    + apply WfETSingle; constructor.
Qed.

Lemma record_ets_defined :
  DefinedEntities record_ets Original.entity_names.
Proof.
  unfold record_ets, Original.entity_names.
  repeat constructor.
Qed.

Lemma integer_expr_typed : forall env e,
  C4.IntegerExpr e ->
  HasType (somepaths []) env (e, somepaths []) intType.
Proof.
  intros env e H; induction H.
  - eapply TLitOther; [discriminate | constructor].
  - eapply TNeg; eauto.
  - eapply TAdd; eauto.
  - eapply TSub; eauto.
  - eapply TMul; eauto.
Qed.

Lemma record_expr_typed : forall env field e,
  C4.IntegerExpr e ->
  HasType (somepaths []) env
    (recExprCons field e recExprNil, somepaths [])
    (recordTypeCons field false intType recordTypeNil).
Proof.
  intros env field e He.
  eapply TRecCons with (x := somepaths []) (rx := somepaths []).
  - apply integer_expr_typed. exact He.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma record_field_typed : forall acts req expr ty,
  C6.RecordFieldTyped expr ty ->
  HasType (somepaths [])
    (MkEnvironment (MkSchema record_ets acts) req) expr ty.
Proof.
  intros acts req expr ty H; destruct H as [field e He | field e He].
  - eapply TGetAttrRecReq with
      (ns := Original.entity_names)
      (TE := recordTypeCons field false intType recordTypeNil)
      (T := intType).
    + reflexivity.
    + apply record_ets_defined.
    + apply BindNow. constructor.
    + apply record_expr_typed. exact He.
  - eapply THasAttrRecReq with
      (ns := Original.entity_names)
      (TE := recordTypeCons field false intType recordTypeNil)
      (T := intType).
    + reflexivity.
    + apply record_ets_defined.
    + apply BindNow. constructor.
    + apply record_expr_typed. exact He.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v005.Candidate.predicate x <->
  Property.candidates.v006.Candidate.predicate x.
Proof.
  intro x; split.
  - intro H. apply C6.PredicatePredecessor. exact H.
  - intro H. destruct H as [p r action_id expr ty Hp Hr Hfield | input Hprev].
    + apply C5.PredicatePredecessor.
      apply C4.PredicatePredecessor.
      apply C3.PredicatePredecessor.
      apply C2.PredicateGeneral.
      apply C1.PredicateSingle.
      * apply WfS with
          (acts := [(MkEntityUID (MkName "Action" []) action_id,
                     MkActionSchemaEntry [p] [r] [])]).
        -- apply record_ets_wf.
        -- apply WfACTSSingle. apply WfACTSingle; try assumption.
           constructor.
        -- reflexivity.
      * apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
      * destruct Hfield; constructor.
      * apply record_field_typed. exact Hfield.
    + exact Hprev.
Qed.
