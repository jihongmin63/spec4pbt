Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Import ListNotations.
Open Scope string_scope.

Module C1 := Property.candidates.v001.Candidate.
Module C2 := Property.candidates.v002.Candidate.
Module C3 := Property.candidates.v003.Candidate.
Module C4 := Property.candidates.v004.Candidate.
Module C5 := Property.candidates.v005.Candidate.

Definition n1 := MkName "EntityType1" [].
Definition n2 := MkName "EntityType2" [].
Definition base_ets : list (EntityName * EntitySchemaEntry) :=
  [(n1, MkEntitySchemaEntry [] []); (n2, MkEntitySchemaEntry [] [])].
Definition base_acts (id : string) : list (EntityUID * ActionSchemaEntry) :=
  [(MkEntityUID (MkName "Action" []) id,
    MkActionSchemaEntry [n1] [n1] [])].
Definition base_req (id : string) : RequestType :=
  MkRequest n1 (MkEntityUID (MkName "Action" []) id) n1 [].
Definition base_env (id : string) : Environment :=
  MkEnvironment (MkSchema base_ets (base_acts id)) (base_req id).
Definition base_input (id : string) (ty : CedarType)
    (expr : CedarExpr * PathSet) : Original.Input :=
  Original.mkInput base_ets (base_acts id) [base_req id]
                   (base_env id) [] ty expr.

Lemma name1_defined : DefinedName Original.entity_names n1.
Proof. unfold Original.entity_names, n1; constructor; reflexivity. Qed.
Lemma name2_defined : DefinedName Original.entity_names n2.
Proof.
  unfold Original.entity_names, n1, n2.
  apply DNRest; [discriminate | constructor; reflexivity].
Qed.

Lemma base_entities : DefinedEntities base_ets Original.entity_names.
Proof.
  unfold base_ets, Original.entity_names, n1, n2.
  repeat constructor.
Qed.

Lemma base_schema : forall id,
  WfSchema Original.entity_names (MkSchema base_ets (base_acts id)).
Proof.
  intro id. unfold Original.entity_names, base_ets, base_acts, n1, n2.
  eapply WfS.
  - apply WfETSCons.
    + constructor; reflexivity.
    + constructor; [discriminate | constructor].
    + constructor; [constructor | constructor].
    + apply WfETSSingle.
      * apply DNRest; [discriminate | constructor; reflexivity].
      * constructor; [constructor | constructor].
  - apply WfACTSSingle. constructor.
    + constructor; reflexivity.
    + constructor; reflexivity.
    + constructor.
  - reflexivity.
Qed.

Lemma base_requests : forall id,
  ActionSchemaToRequestTypes (base_acts id) [] [base_req id].
Proof.
  intro id. unfold base_acts, base_req.
  apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
Qed.

Lemma base_environments : forall id,
  SchemaToEnvironments (MkSchema base_ets (base_acts id))
    [base_req id] [base_env id].
Proof. intro id. unfold base_env. constructor. Qed.

Lemma int_tree_syntax : forall e, C3.IntTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto using WfExprSyntax.
Qed.

Lemma string_tree_syntax : forall e, C4.C4StringTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto using WfExprSyntax.
Qed.

Lemma int_set_wf_set : forall e, C4.C4IntSet e -> WfSetSyntax e.
Proof.
  intros e H; induction H; constructor;
    eauto using int_tree_syntax, WFSSNil.
Qed.

Lemma int_set_syntax : forall e, C4.C4IntSet e -> WfExprSyntax e.
Proof.
  intros e H; induction H; constructor;
    eauto using int_tree_syntax, int_set_wf_set, WFSSNil.
Qed.

Lemma bool_tree_syntax : forall e, C4.C4BoolTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto using WfExprSyntax,
    int_tree_syntax, string_tree_syntax, int_set_syntax.
Qed.

Lemma int_tree_typed : forall id e,
  C3.IntTree e -> forall a,
  HasType a (base_env id) (e, somepaths []) intType.
Proof.
  intros id e H; induction H; intro a.
  - apply TLitOther; [discriminate | constructor].
  - eapply TNeg. apply IHIntTree.
  - eapply TAdd; eauto.
  - eapply TSub; eauto.
  - eapply TMul; eauto.
  - eapply TCondTrue; [apply IHIntTree1 | eauto using int_tree_syntax].
  - eapply TCondFalse; [eauto using int_tree_syntax | apply IHIntTree2].
Qed.

Lemma string_tree_typed : forall id e,
  C4.C4StringTree e -> forall a,
  HasType a (base_env id) (e, somepaths []) stringType.
Proof.
  intros id e H; induction H; intro a.
  - apply TLitOther; [discriminate | constructor].
  - eapply TCondTrue; [apply IHC4StringTree1 |
      eauto using string_tree_syntax].
  - eapply TCondFalse; [eauto using string_tree_syntax |
      apply IHC4StringTree2].
Qed.

Lemma int_set_typed : forall id e,
  C4.C4IntSet e -> forall a,
  HasType a (base_env id) (e, somepaths []) (setType intType).
Proof.
  intros id e H; induction H; intro a.
  - eapply TSetSingle. eauto using int_tree_typed.
  - eapply TSetMany.
    + eauto using int_tree_typed.
    + apply IHC4IntSet.
    + eauto using int_set_wf_set.
Qed.

Lemma bool_tree_typed : forall id e,
  C4.C4BoolTree e -> forall a,
  HasType a (base_env id) (e, somepaths []) (boolType anyBool).
Proof.
  intros id e H; induction H; intro a.
  - eapply TLessThan; eauto using int_tree_typed.
  - eapply TLessEqualThan; eauto using int_tree_typed.
  - eapply TLike. eauto using string_tree_typed.
  - eapply TNotAny. apply IHC4BoolTree.
  - eapply TCondTrue; [apply IHC4BoolTree1 |
      eauto using bool_tree_syntax].
  - eapply TCondFalse; [eauto using bool_tree_syntax |
      apply IHC4BoolTree2].
  - eapply TContains with (ns := Original.entity_names)
      (ets := base_ets) (acts := base_acts id) (R := base_req id)
      (T1 := intType) (T2 := intType) (T := intType);
      eauto using base_entities, WfCedarType, SubType,
        int_set_typed, int_tree_typed.
  - eapply TContainsAll with (ns := Original.entity_names)
      (ets := base_ets) (acts := base_acts id) (R := base_req id)
      (T1 := intType) (T2 := intType) (T := intType);
      eauto using base_entities, WfCedarType, SubType,
        int_set_typed.
  - eapply TContainsAny with (ns := Original.entity_names)
      (ets := base_ets) (acts := base_acts id) (R := base_req id)
      (T1 := intType) (T2 := intType) (T := intType);
      eauto using base_entities, WfCedarType, SubType,
        int_set_typed.
Qed.

Lemma single_record_typed : forall id field e a,
  C3.IntTree e ->
  HasType a (base_env id)
    (recExprCons field e recExprNil, somepaths [])
    (recordTypeCons field false intType recordTypeNil).
Proof.
  intros. eapply TRecCons.
  - eauto using int_tree_typed.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma c5_case_typed : forall id ty expr,
  C5.C5Case ty expr ->
  WfCedarType Original.entity_names ty /\
  HasType (somepaths []) (base_env id) expr ty.
Proof.
  intros id ty expr H; destruct H; split;
    try (eauto using WfCedarType, name1_defined).
  - eapply TAnd. eapply TCondBool with
      (T2 := boolType anyBool) (T3 := boolType ff_)
      (x1 := somepaths []) (x2 := somepaths []) (x3 := allpaths).
    + constructor.
    + eauto using bool_tree_typed.
    + simpl. eauto using bool_tree_typed.
    + apply TLitFalse. constructor.
    + reflexivity.
  - eapply TCondBool with
      (T2 := intType) (T3 := intType)
      (x1 := somepaths []) (x2 := somepaths []) (x3 := somepaths []).
    + constructor.
    + eauto using bool_tree_typed.
    + simpl. eauto using int_tree_typed.
    + eauto using int_tree_typed.
    + reflexivity.
  - eapply TCondBool with
      (T2 := stringType) (T3 := stringType)
      (x1 := somepaths []) (x2 := somepaths []) (x3 := somepaths []).
    + constructor.
    + eauto using bool_tree_typed.
    + simpl. eauto using string_tree_typed.
    + eauto using string_tree_typed.
    + reflexivity.
  - eapply TCondBool with
      (T2 := setType intType) (T3 := setType intType)
      (x1 := somepaths []) (x2 := somepaths []) (x3 := somepaths []).
    + constructor.
    + eauto using bool_tree_typed.
    + simpl. eauto using int_set_typed.
    + eauto using int_set_typed.
    + reflexivity.
  - eapply TGetAttrRecReq with
      (ns := Original.entity_names)
      (TE := recordTypeCons field false intType recordTypeNil)
      (ets := base_ets) (acts := base_acts id) (R := base_req id).
    + reflexivity.
    + apply base_entities.
    + apply BindNow. constructor.
    + eauto using single_record_typed.
  - eapply THasAttrRecReq with
      (ns := Original.entity_names)
      (TE := recordTypeCons field false intType recordTypeNil)
      (ets := base_ets) (acts := base_acts id) (R := base_req id).
    + reflexivity.
    + apply base_entities.
    + apply BindNow. constructor.
    + eauto using single_record_typed.
  - apply TLitOther.
    + discriminate.
    + unfold base_env, base_ets. apply TEntity. constructor.
  - eapply TIsTrue with (ns := Original.entity_names)
      (ets := base_ets) (acts := base_acts id) (R := base_req id).
    + reflexivity.
    + apply base_entities.
    + apply WfEntityType. apply name1_defined.
    + apply TVar. unfold base_env, base_req. constructor.
Qed.

Lemma c5_in_c4 : forall id ty expr,
  C5.C5Case ty expr -> C4.predicate (base_input id ty expr).
Proof.
  intros id ty expr Hcase.
  destruct (c5_case_typed id ty expr Hcase) as [Hwf Htype].
  apply C4.C4Inherited. apply C3.C3Inherited.
  apply C2.Inherited. apply C1.General.
  - apply base_schema.
  - apply base_requests.
  - apply base_environments.
  - exact Hwf.
  - exact Htype.
Qed.

Theorem equivalent : forall x : Original.Input,
  C4.predicate x <-> C5.predicate x.
Proof.
  intro x; split.
  - apply C5.C5Inherited.
  - intro H; destruct H as [i H | id ty expr Hcase].
    + exact H.
    + apply c5_in_c4. exact Hcase.
Qed.
