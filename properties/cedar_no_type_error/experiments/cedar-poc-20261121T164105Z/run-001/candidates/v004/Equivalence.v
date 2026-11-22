Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Import ListNotations.
Open Scope string_scope.

Module C1 := Property.candidates.v001.Candidate.
Module C2 := Property.candidates.v002.Candidate.
Module C3 := Property.candidates.v003.Candidate.
Module C4 := Property.candidates.v004.Candidate.

Definition base_ets : list (EntityName * EntitySchemaEntry) :=
  [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
   (MkName "EntityType2" [], MkEntitySchemaEntry [] [])].

Definition base_acts (id : string) : list (EntityUID * ActionSchemaEntry) :=
  [(MkEntityUID (MkName "Action" []) id,
    MkActionSchemaEntry [MkName "EntityType1" []]
                        [MkName "EntityType1" []] [])].

Definition base_req (id : string) : RequestType :=
  MkRequest (MkName "EntityType1" [])
            (MkEntityUID (MkName "Action" []) id)
            (MkName "EntityType1" []) [].

Definition base_env (id : string) : Environment :=
  MkEnvironment (MkSchema base_ets (base_acts id)) (base_req id).

Definition base_input (id : string) (ty : CedarType)
    (ex : CedarExpr * PathSet) : Original.Input :=
  Original.mkInput base_ets (base_acts id) [base_req id]
                   (base_env id) [] ty ex.

Lemma base_defined : DefinedEntities base_ets Original.entity_names.
Proof.
  unfold base_ets, Original.entity_names.
  repeat constructor.
Qed.

Lemma base_schema : forall id,
  WfSchema Original.entity_names (MkSchema base_ets (base_acts id)).
Proof.
  intro id. unfold Original.entity_names, base_ets, base_acts.
  eapply WfS.
  - eapply WfETSCons.
    + apply DNFound. reflexivity.
    + apply NIECons.
      * discriminate.
      * apply NIENil.
    + apply WfETSingle; constructor.
    + eapply WfETSSingle.
      * eapply DNRest.
        -- discriminate.
        -- apply DNFound. reflexivity.
      * apply WfETSingle; constructor.
  - apply WfACTSSingle. apply WfACTSingle.
    + apply DNFound. reflexivity.
    + apply DNFound. reflexivity.
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
Proof.
  intro id. unfold base_env. apply MkEnvsSingle.
Qed.

Lemma int_tree_wf : forall e, C3.IntTree e -> WfExprSyntax e.
Proof.
  intros e H. induction H; constructor; auto using WFSPrim.
Qed.

Lemma int_tree_typed : forall id e, C3.IntTree e ->
  HasType (somepaths []) (base_env id) (e, somepaths []) intType.
Proof.
  intros id e H.
  induction H as
    [n | e H IH | e1 e2 H1 IH1 H2 IH2
     | e1 e2 H1 IH1 H2 IH2 | e1 e2 H1 IH1 H2 IH2
     | e1 e2 H1 IH1 H2 IH2 | e1 e2 H1 IH1 H2 IH2].
  - apply TLitOther. discriminate. constructor.
  - eapply TNeg. exact IH.
  - eapply TAdd; eassumption.
  - eapply TSub; eassumption.
  - eapply TMul; eassumption.
  - eapply TCondTrue.
    + exact IH1.
    + apply int_tree_wf. exact H2.
  - eapply TCondFalse.
    + apply int_tree_wf. exact H1.
    + exact IH2.
Qed.

Lemma string_tree_wf : forall e, C4.C4StringTree e -> WfExprSyntax e.
Proof.
  intros e H. induction H; constructor; auto using WFSPrim.
Qed.

Lemma string_tree_typed : forall id e, C4.C4StringTree e ->
  HasType (somepaths []) (base_env id) (e, somepaths []) stringType.
Proof.
  intros id e H.
  induction H as [s | e1 e2 H1 IH1 H2 IH2 | e1 e2 H1 IH1 H2 IH2].
  - apply TLitOther. discriminate. constructor.
  - eapply TCondTrue.
    + exact IH1.
    + apply string_tree_wf. exact H2.
  - eapply TCondFalse.
    + apply string_tree_wf. exact H1.
    + exact IH2.
Qed.

Lemma set_tree_wf : forall e, C4.C4IntSet e -> WfSetSyntax e.
Proof.
  intros e H. induction H.
  - constructor. apply int_tree_wf. assumption. constructor.
  - constructor. apply int_tree_wf. assumption. assumption.
Qed.

Lemma set_tree_typed : forall id e, C4.C4IntSet e ->
  HasType (somepaths []) (base_env id) (e, somepaths []) (setType intType).
Proof.
  intros id e H. induction H as [e He | e rest He Hr IHr].
  - eapply TSetSingle. apply int_tree_typed. exact He.
  - eapply TSetMany.
    + apply int_tree_typed. exact He.
    + exact IHr.
    + apply set_tree_wf. exact Hr.
Qed.

Lemma set_tree_expr_wf : forall e, C4.C4IntSet e -> WfExprSyntax e.
Proof.
  intros e H. inversion H; subst; constructor;
    eauto using int_tree_wf, set_tree_wf, WFSSNil.
Qed.

Lemma bool_tree_wf : forall e, C4.C4BoolTree e -> WfExprSyntax e.
Proof.
  intros e H. induction H; constructor;
    eauto using int_tree_wf, string_tree_wf, set_tree_expr_wf, WFSPrim.
Qed.

Lemma bool_tree_typed : forall id e, C4.C4BoolTree e ->
  HasType (somepaths []) (base_env id) (e, somepaths []) (boolType anyBool).
Proof.
  intros id e H. induction H.
  - eapply TLessThan; eauto using int_tree_typed.
  - eapply TLessEqualThan; eauto using int_tree_typed.
  - eapply TLike. eauto using string_tree_typed.
  - eapply TNotAny. exact IHC4BoolTree.
  - eapply TCondTrue.
    + exact IHC4BoolTree1.
    + apply bool_tree_wf. exact H0.
  - eapply TCondFalse.
    + apply bool_tree_wf. exact H.
    + exact IHC4BoolTree2.
  - eapply TContains with
      (ets := base_ets) (acts := base_acts id) (R := base_req id)
      (ns := Original.entity_names) (T := intType)
      (T1 := intType) (T2 := intType).
    + reflexivity.
    + apply base_defined.
    + constructor.
    + constructor.
    + constructor.
    + apply set_tree_typed. assumption.
    + apply int_tree_typed. assumption.
  - eapply TContainsAll with
      (ets := base_ets) (acts := base_acts id) (R := base_req id)
      (ns := Original.entity_names) (T := intType)
      (T1 := intType) (T2 := intType).
    + reflexivity.
    + apply base_defined.
    + constructor.
    + constructor.
    + constructor.
    + apply set_tree_typed. assumption.
    + apply set_tree_typed. assumption.
  - eapply TContainsAny with
      (ets := base_ets) (acts := base_acts id) (R := base_req id)
      (ns := Original.entity_names) (T := intType)
      (T1 := intType) (T2 := intType).
    + reflexivity.
    + apply base_defined.
    + constructor.
    + constructor.
    + constructor.
    + apply set_tree_typed. assumption.
    + apply set_tree_typed. assumption.
Qed.

Lemma double_field_typed : forall id e1 e2,
  C3.IntTree e1 -> C3.IntTree e2 ->
  HasType (somepaths []) (base_env id)
    (recExprCons "left" e1 (recExprCons "right" e2 recExprNil), somepaths [])
    (recordTypeCons "left" false intType
      (recordTypeCons "right" false intType recordTypeNil)).
Proof.
  intros id e1 e2 H1 H2.
  eapply TRecCons.
  - apply int_tree_typed. exact H1.
  - constructor.
  - eapply TRecCons.
    + apply int_tree_typed. exact H2.
    + constructor.
    + apply TRecNil.
    + constructor.
    + constructor.
  - constructor.
    + apply int_tree_wf. exact H2.
    + constructor.
    + constructor.
  - constructor.
    + discriminate.
    + constructor.
Qed.

Lemma case_typed : forall id ty ex, C4.C4Case ty ex ->
  WfCedarType Original.entity_names ty /\
  HasType (somepaths []) (base_env id) ex ty.
Proof.
  intros id ty ex H. destruct H.
  - split. constructor. apply string_tree_typed. assumption.
  - split. constructor. constructor. apply set_tree_typed. assumption.
  - split. constructor. apply bool_tree_typed. assumption.
  - split.
    + repeat constructor.
    + apply double_field_typed; assumption.
Qed.

Lemma structured_in_predecessor : forall id ty ex,
  C4.C4Case ty ex -> C3.predicate (base_input id ty ex).
Proof.
  intros id ty ex Hcase. unfold base_input.
  apply C3.C3Inherited. apply C2.Inherited.
  apply C1.General.
  - apply base_schema.
  - apply base_requests.
  - apply base_environments.
  - exact (proj1 (case_typed id ty ex Hcase)).
  - exact (proj2 (case_typed id ty ex Hcase)).
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v003.Candidate.predicate x <->
  Property.candidates.v004.Candidate.predicate x.
Proof.
  intro x. split.
  - apply C4.C4Inherited.
  - intro H. destruct H as [i Hi | id ty ex Hcase].
    + exact Hi.
    + apply structured_in_predecessor. exact Hcase.
Qed.
