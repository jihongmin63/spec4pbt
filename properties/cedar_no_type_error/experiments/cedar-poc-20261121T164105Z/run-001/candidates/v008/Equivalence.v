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
Require Import Property.candidates.v008.Candidate.
Import ListNotations.
Open Scope string_scope.

Module C1 := Property.candidates.v001.Candidate.
Module C2 := Property.candidates.v002.Candidate.
Module C3 := Property.candidates.v003.Candidate.
Module C4 := Property.candidates.v004.Candidate.
Module C5 := Property.candidates.v005.Candidate.
Module C6 := Property.candidates.v006.Candidate.
Module C7 := Property.candidates.v007.Candidate.
Module C8 := Property.candidates.v008.Candidate.

Definition names := Original.entity_names.
Definition entities : list (EntityName * EntitySchemaEntry) :=
  [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
   (MkName "EntityType2" [], MkEntitySchemaEntry [] [])].
Definition actions (s : string) : list (EntityUID * ActionSchemaEntry) :=
  [(MkEntityUID (MkName "Action" []) s,
    MkActionSchemaEntry [MkName "EntityType1" []]
                        [MkName "EntityType1" []] [])].
Definition request (s : string) : RequestType :=
  MkRequest (MkName "EntityType1" [])
            (MkEntityUID (MkName "Action" []) s)
            (MkName "EntityType1" []) [].
Definition env (s : string) : Environment :=
  MkEnvironment (MkSchema entities (actions s)) (request s).
Definition input (s : string) (ty : CedarType) (ex : CedarExpr * PathSet)
  : Original.Input :=
  Original.mkInput entities (actions s) [request s] (env s) [] ty ex.
Definition empty : PathSet := somepaths [].

Lemma defined_entities : DefinedEntities entities
  [MkName "EntityType1" []; MkName "EntityType2" []].
Proof. unfold entities; repeat constructor. Qed.

Lemma c3_int_wf : forall e, C3.IntTree e -> WfExprSyntax e.
Proof. intros e H; induction H; eauto using WfExprSyntax. Qed.

Lemma c4_string_wf : forall e, C4.C4StringTree e -> WfExprSyntax e.
Proof. intros e H; induction H; eauto using WfExprSyntax. Qed.

Lemma c4_set_wf : forall e, C4.C4IntSet e -> WfSetSyntax e.
Proof.
  intros e H; induction H; eauto using WfSetSyntax, c3_int_wf.
Qed.

Lemma wf_set_expr : forall e, WfSetSyntax e -> WfExprSyntax e.
Proof. intros e H; induction H; eauto using WfExprSyntax. Qed.

Lemma c4_bool_wf : forall e, C4.C4BoolTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto 10 using WfExprSyntax, WfSetSyntax,
    c3_int_wf, c4_string_wf, c4_set_wf, wf_set_expr.
Qed.

Lemma c3_int_type : forall s e, C3.IntTree e ->
  HasType empty (env s) (e, empty) intType.
Proof.
  intros s e H; induction H.
  - apply TLitOther; [discriminate | constructor].
  - eapply TNeg; eauto.
  - eapply TAdd; eauto.
  - eapply TSub; eauto.
  - eapply TMul; eauto.
  - eapply TCondTrue; eauto using c3_int_wf.
  - eapply TCondFalse; eauto using c3_int_wf.
Qed.

Lemma c4_string_type : forall s e, C4.C4StringTree e ->
  HasType empty (env s) (e, empty) stringType.
Proof.
  intros s e H; induction H.
  - apply TLitOther; [discriminate | constructor].
  - eapply TCondTrue; eauto using c4_string_wf.
  - eapply TCondFalse; eauto using c4_string_wf.
Qed.

Lemma c4_set_type : forall s e, C4.C4IntSet e ->
  HasType empty (env s) (e, empty) (setType intType).
Proof.
  intros s e H; induction H.
  - eapply TSetSingle; eauto using c3_int_type.
  - eapply TSetMany; eauto using c3_int_type, c4_set_wf.
Qed.

Lemma bool_if : forall s c t f,
  HasType empty (env s) (c, empty) (boolType anyBool) ->
  HasType empty (env s) (t, empty) (boolType anyBool) ->
  HasType empty (env s) (f, empty) (boolType anyBool) ->
  HasType empty (env s) (ite c t f, empty) (boolType anyBool).
Proof.
  intros. eapply TCondBool with (x1:=empty) (x2:=empty) (x3:=empty)
    (T2:=boolType anyBool) (T3:=boolType anyBool); simpl;
    eauto using BranchJoin.
Qed.

Lemma bool_and : forall s a b,
  HasType empty (env s) (a, empty) (boolType anyBool) ->
  HasType empty (env s) (b, empty) (boolType anyBool) ->
  HasType empty (env s) (andExpr a b, empty) (boolType anyBool).
Proof.
  intros. eapply TAnd.
  eapply TCondBool with (x1:=empty) (x2:=empty) (x3:=allpaths)
    (T2:=boolType anyBool) (T3:=boolType ff_); simpl;
    eauto using BranchJoin, HasType, HasTypePrim.
Qed.

Lemma int_if : forall s c t f,
  HasType empty (env s) (c, empty) (boolType anyBool) ->
  HasType empty (env s) (t, empty) intType ->
  HasType empty (env s) (f, empty) intType ->
  HasType empty (env s) (ite c t f, empty) intType.
Proof.
  intros. eapply TCondBool with (x1:=empty) (x2:=empty) (x3:=empty)
    (T2:=intType) (T3:=intType); simpl; eauto using BranchJoin.
Qed.

Lemma string_if : forall s c t f,
  HasType empty (env s) (c, empty) (boolType anyBool) ->
  HasType empty (env s) (t, empty) stringType ->
  HasType empty (env s) (f, empty) stringType ->
  HasType empty (env s) (ite c t f, empty) stringType.
Proof.
  intros. eapply TCondBool with (x1:=empty) (x2:=empty) (x3:=empty)
    (T2:=stringType) (T3:=stringType); simpl; eauto using BranchJoin.
Qed.

Lemma string_set_if : forall s c t f,
  HasType empty (env s) (c, empty) (boolType anyBool) ->
  HasType empty (env s) (t, empty) (setType stringType) ->
  HasType empty (env s) (f, empty) (setType stringType) ->
  HasType empty (env s) (ite c t f, empty) (setType stringType).
Proof.
  intros. eapply TCondBool with (x1:=empty) (x2:=empty) (x3:=empty)
    (T2:=setType stringType) (T3:=setType stringType);
    simpl; eauto using BranchJoin.
Qed.

Lemma c4_bool_type : forall s e, C4.C4BoolTree e ->
  HasType empty (env s) (e, empty) (boolType anyBool).
Proof.
  intros s e H; induction H.
  - eapply TLessThan; eauto using c3_int_type.
  - eapply TLessEqualThan; eauto using c3_int_type.
  - eapply TLike; eauto using c4_string_type.
  - eapply TNotAny; eauto.
  - eapply TCondTrue; eauto using c4_bool_wf.
  - eapply TCondFalse; eauto using c4_bool_wf.
  - eapply TContains with (T:=intType) (T1:=intType)
      (T2:=intType) (ns:=names) (ets:=entities)
      (acts:=actions s) (R:=request s); simpl;
      eauto using defined_entities, WfCedarType, SubType,
        c4_set_type, c3_int_type.
  - eapply TContainsAll with (T:=intType) (T1:=intType)
      (T2:=intType) (ns:=names) (ets:=entities)
      (acts:=actions s) (R:=request s); simpl;
      eauto using defined_entities, WfCedarType, SubType, c4_set_type.
  - eapply TContainsAny with (T:=intType) (T1:=intType)
      (T2:=intType) (ns:=names) (ets:=entities)
      (acts:=actions s) (R:=request s); simpl;
      eauto using defined_entities, WfCedarType, SubType, c4_set_type.
Qed.

Lemma c6_bool_type : forall s e, C6.C6BoolTree e ->
  HasType empty (env s) (e, empty) (boolType anyBool).
Proof.
  intros s e H; induction H.
  - eauto using c4_bool_type.
  - eapply TNotAny; eauto.
  - eauto using bool_and.
  - eauto using bool_if.
Qed.

Lemma c7_int_type : forall s e, C7.C7IntTree e ->
  HasType empty (env s) (e, empty) intType.
Proof.
  intros s e H; induction H.
  - eauto using c3_int_type.
  - eapply TNeg; eauto.
  - eapply TAdd; eauto.
  - eapply TSub; eauto.
  - eapply TMul; eauto.
  - eauto using int_if, c6_bool_type.
Qed.

Lemma c6_bool_wf : forall e, C6.C6BoolTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto using WfExprSyntax, c4_bool_wf.
Qed.

Lemma c7_int_wf : forall e, C7.C7IntTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto using WfExprSyntax, c3_int_wf,
    c6_bool_wf.
Qed.

Lemma c7_set_wf : forall e, C7.C7IntSet e -> WfSetSyntax e.
Proof.
  intros e H; induction H; eauto using WfSetSyntax, c7_int_wf.
Qed.

Lemma c7_set_type : forall s e, C7.C7IntSet e ->
  HasType empty (env s) (e, empty) (setType intType).
Proof.
  intros s e H; induction H.
  - eapply TSetSingle; eauto using c7_int_type.
  - eapply TSetMany; eauto using c7_int_type, c7_set_wf.
Qed.

Lemma c7_bool_wf : forall e, C7.C7BoolTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto 10 using WfExprSyntax, c6_bool_wf,
    c7_int_wf, c7_set_wf, wf_set_expr.
Qed.

Lemma c7_bool_type : forall s e, C7.C7BoolTree e ->
  HasType empty (env s) (e, empty) (boolType anyBool).
Proof.
  intros s e H; induction H.
  - eauto using c6_bool_type.
  - eapply TLessThan; eauto using c7_int_type.
  - eapply TLessEqualThan; eauto using c7_int_type.
  - eapply TContains with (T:=intType) (T1:=intType)
      (T2:=intType) (ns:=names) (ets:=entities)
      (acts:=actions s) (R:=request s); simpl;
      eauto using defined_entities, WfCedarType, SubType,
        c7_set_type, c7_int_type.
  - eapply TContainsAll with (T:=intType) (T1:=intType)
      (T2:=intType) (ns:=names) (ets:=entities)
      (acts:=actions s) (R:=request s); simpl;
      eauto using defined_entities, WfCedarType, SubType, c7_set_type.
  - eapply TContainsAny with (T:=intType) (T1:=intType)
      (T2:=intType) (ns:=names) (ets:=entities)
      (acts:=actions s) (R:=request s); simpl;
      eauto using defined_entities, WfCedarType, SubType, c7_set_type.
  - eapply TNotAny; eauto.
  - eauto using bool_and.
  - eauto using bool_if.
Qed.

Lemma c8_string_wf : forall e, C8.C8StringTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto using WfExprSyntax, c4_string_wf,
    c7_bool_wf.
Qed.

Lemma c8_string_type : forall s e, C8.C8StringTree e ->
  HasType empty (env s) (e, empty) stringType.
Proof.
  intros s e H; induction H.
  - eauto using c4_string_type.
  - eauto using string_if, c7_bool_type.
Qed.

Lemma c8_set_wf : forall e, C8.C8StringSet e -> WfSetSyntax e.
Proof.
  intros e H; induction H; eauto using WfSetSyntax, c8_string_wf.
Qed.

Lemma c8_set_type : forall s e, C8.C8StringSet e ->
  HasType empty (env s) (e, empty) (setType stringType).
Proof.
  intros s e H; induction H.
  - eapply TSetSingle; eauto using c8_string_type.
  - eapply TSetMany; eauto using c8_string_type, c8_set_wf.
Qed.

Lemma true_type : forall s,
  HasType empty (env s) (lit (boolean true), empty) (boolType tt_).
Proof. intro; apply TLitOther; [discriminate | constructor]. Qed.

Lemma false_type : forall s,
  HasType empty (env s) (lit (boolean false), allpaths) (boolType ff_).
Proof. intro; apply TLitFalse; constructor. Qed.

Lemma bool_if_tf : forall s c,
  HasType empty (env s) (c, empty) (boolType anyBool) ->
  HasType empty (env s)
    (ite c (lit (boolean true)) (lit (boolean false)), empty)
    (boolType anyBool).
Proof.
  intros. eapply TCondBool with (x1:=empty) (x2:=empty)
    (x3:=allpaths) (T2:=boolType tt_) (T3:=boolType ff_);
    simpl; eauto using BranchJoin, true_type, false_type.
Qed.

Lemma bool_if_ft : forall s c,
  HasType empty (env s) (c, empty) (boolType anyBool) ->
  HasType empty (env s)
    (ite c (lit (boolean false)) (lit (boolean true)), empty)
    (boolType anyBool).
Proof.
  intros. eapply TCondBool with (x1:=empty) (x2:=allpaths)
    (x3:=empty) (T2:=boolType ff_) (T3:=boolType tt_);
    simpl; eauto using BranchJoin, true_type, false_type.
Qed.

Lemma c8_bool_type : forall s e, C8.C8BoolTree e ->
  HasType empty (env s) (e, empty) (boolType anyBool).
Proof.
  intros s e H; induction H.
  - eauto using c7_bool_type.
  - eapply TLike; eauto using c8_string_type.
  - eapply TContains with (T:=stringType) (T1:=stringType)
      (T2:=stringType) (ns:=names) (ets:=entities)
      (acts:=actions s) (R:=request s); simpl;
      eauto using defined_entities, WfCedarType, SubType,
        c8_set_type, c8_string_type.
  - eapply TContainsAll with (T:=stringType) (T1:=stringType)
      (T2:=stringType) (ns:=names) (ets:=entities)
      (acts:=actions s) (R:=request s); simpl;
      eauto using defined_entities, WfCedarType, SubType, c8_set_type.
  - eapply TContainsAny with (T:=stringType) (T1:=stringType)
      (T2:=stringType) (ns:=names) (ets:=entities)
      (acts:=actions s) (R:=request s); simpl;
      eauto using defined_entities, WfCedarType, SubType, c8_set_type.
  - eapply TNotAny; eauto.
  - eauto using bool_and.
  - eauto using bool_if.
  - eauto using bool_if_tf.
  - eauto using bool_if_ft.
Qed.

Lemma record_single_type : forall s field e T,
  HasType empty (env s) (e, empty) T ->
  HasType empty (env s) (recExprCons field e recExprNil, empty)
    (recordTypeCons field false T recordTypeNil).
Proof.
  intros. eapply TRecCons with (x:=empty) (rx:=empty);
    eauto using RecordType, HasType, WfRecSyntax, NotInRecExpr.
Qed.

Lemma record_get_type : forall s field e T,
  HasType empty (env s) (e, empty) T ->
  HasType empty (env s)
    (getAttr (recExprCons field e recExprNil) field, empty) T.
Proof.
  intros. eapply TGetAttrRecReq with
    (x:=empty) (TE:=recordTypeCons field false T recordTypeNil)
    (ns:=names) (ets:=entities) (acts:=actions s) (R:=request s);
    simpl; eauto using defined_entities, BindAttrType, WfRecordType,
      record_single_type.
Qed.

Lemma c8_case_type : forall s ty ex, C8.C8Case ty ex ->
  HasType empty (env s) ex ty.
Proof.
  intros s ty ex H; induction H;
    eauto using c8_string_type, c8_set_type, c8_bool_type,
      string_set_if, record_single_type, record_get_type.
Qed.

Lemma c8_case_wf_type : forall ty ex, C8.C8Case ty ex ->
  WfCedarType names ty.
Proof.
  intros ty ex H; induction H; unfold names, Original.entity_names;
    eauto using WfCedarType.
Qed.

Lemma canonical_schema : forall s,
  WfSchema names (MkSchema entities (actions s)).
Proof.
  intro s. unfold names, Original.entity_names, entities, actions.
  eapply WfS.
  - repeat constructor; congruence.
  - repeat constructor; congruence.
  - reflexivity.
Qed.

Lemma canonical_requests : forall s,
  ActionSchemaToRequestTypes (actions s) [] [request s].
Proof.
  intro s. unfold actions, request.
  repeat constructor.
Qed.

Lemma canonical_environment : forall s,
  SchemaToEnvironments (MkSchema entities (actions s))
    [request s] [env s].
Proof.
  intro s. unfold env. constructor.
Qed.

Theorem equivalent : forall x : Original.Input,
  C7.predicate x <-> C8.predicate x.
Proof.
  intro x; split.
  - intro H. exact (C8.C8Inherited x H).
  - intro H. destruct H as [i H7 | s ty ex Hcase].
    + exact H7.
    + apply C7.C7Inherited.
      apply C6.C6Inherited.
      apply C5.C5Inherited.
      apply C4.C4Inherited.
      apply C3.C3Inherited.
      apply C2.Inherited.
      eapply C1.General.
      * apply canonical_schema.
      * apply canonical_requests.
      * apply canonical_environment.
      * eauto using c8_case_wf_type.
      * eauto using c8_case_type.
Qed.

