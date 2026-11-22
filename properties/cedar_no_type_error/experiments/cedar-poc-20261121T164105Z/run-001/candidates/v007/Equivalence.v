Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v006.Candidate.
Require Import Property.candidates.v007.Candidate.
Import ListNotations.
Open Scope string_scope.

Module P1 := Property.candidates.v001.Candidate.
Module P3 := Property.candidates.v003.Candidate.
Module P4 := Property.candidates.v004.Candidate.
Module P6 := Property.candidates.v006.Candidate.
Module P7 := Property.candidates.v007.Candidate.

Definition fixed_ets : list (EntityName * EntitySchemaEntry) :=
  [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
   (MkName "EntityType2" [], MkEntitySchemaEntry [] [])].
Definition fixed_acts (id : string) : list (EntityUID * ActionSchemaEntry) :=
  [(MkEntityUID (MkName "Action" []) id,
    MkActionSchemaEntry [MkName "EntityType1" []]
                        [MkName "EntityType1" []] [])].
Definition fixed_request (id : string) : RequestType :=
  MkRequest (MkName "EntityType1" [])
            (MkEntityUID (MkName "Action" []) id)
            (MkName "EntityType1" []) [].
Definition fixed_env (id : string) : Environment :=
  MkEnvironment (MkSchema fixed_ets (fixed_acts id)) (fixed_request id).
Definition fixed_input (id : string) (t : CedarType)
    (p : CedarExpr * PathSet) : Original.Input :=
  Original.mkInput fixed_ets (fixed_acts id) [fixed_request id]
                   (fixed_env id) [] t p.

Lemma fixed_defined : DefinedEntities fixed_ets Original.entity_names.
Proof. repeat constructor. Qed.

Lemma fixed_schema : forall id,
    WfSchema Original.entity_names (MkSchema fixed_ets (fixed_acts id)).
Proof.
  intro id. unfold fixed_ets, fixed_acts, Original.entity_names.
  eapply WfS with (acts := [(MkEntityUID (MkName "Action" []) id,
    MkActionSchemaEntry [MkName "EntityType1" []]
                        [MkName "EntityType1" []] [])]).
  - eapply WfETSCons.
    + apply DNFound. reflexivity.
    + constructor. discriminate. constructor.
    + constructor; constructor.
    + eapply WfETSSingle; [apply DNRest; [discriminate|apply DNFound; reflexivity]
                            |constructor; constructor].
  - constructor. constructor; try (apply DNFound; reflexivity);
      constructor.
  - reflexivity.
Qed.

Lemma fixed_request_types : forall id,
    ActionSchemaToRequestTypes (fixed_acts id) [] [fixed_request id].
Proof. intro id. unfold fixed_acts, fixed_request. repeat constructor. Qed.

Lemma fixed_environments : forall id,
    SchemaToEnvironments (MkSchema fixed_ets (fixed_acts id))
      [fixed_request id] [fixed_env id].
Proof. intro id. unfold fixed_env. constructor. Qed.

Lemma int3_wf : forall e, P3.IntTree e -> WfExprSyntax e.
Proof. intros e H; induction H; eauto using WfExprSyntax. Qed.

Lemma int3_type : forall id e, P3.IntTree e ->
    HasType (somepaths []) (fixed_env id) (e, somepaths []) intType.
Proof.
  intros id e H; induction H.
  - apply TLitOther; [discriminate|constructor].
  - eapply TNeg; eauto.
  - eapply TAdd; eauto.
  - eapply TSub; eauto.
  - eapply TMul; eauto.
  - eapply TCondTrue; [eauto|eauto using int3_wf].
  - eapply TCondFalse; [eauto using int3_wf|eauto].
Qed.

Lemma string4_wf : forall e, P4.C4StringTree e -> WfExprSyntax e.
Proof. intros e H; induction H; eauto using WfExprSyntax. Qed.

Lemma string4_type : forall id e, P4.C4StringTree e ->
    HasType (somepaths []) (fixed_env id) (e, somepaths []) stringType.
Proof.
  intros id e H; induction H.
  - apply TLitOther; [discriminate|constructor].
  - eapply TCondTrue; [eauto|eauto using string4_wf].
  - eapply TCondFalse; [eauto using string4_wf|eauto].
Qed.

Lemma set4_wf : forall e, P4.C4IntSet e -> WfSetSyntax e.
Proof.
  intros e H; induction H; constructor; eauto using int3_wf, WfSetSyntax.
Qed.

Lemma set4_type : forall id e, P4.C4IntSet e ->
    HasType (somepaths []) (fixed_env id) (e, somepaths []) (setType intType).
Proof.
  intros id e H; induction H.
  - eapply TSetSingle. eauto using int3_type.
  - eapply TSetMany; eauto using int3_type, set4_wf.
Qed.

Lemma set4_expr_wf : forall e, P4.C4IntSet e -> WfExprSyntax e.
Proof.
  intros e H; induction H.
  - apply WFSSetCons; [eauto using int3_wf|constructor].
  - apply WFSSetCons; eauto using int3_wf, set4_wf.
Qed.

Lemma bool4_wf : forall e, P4.C4BoolTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto using WfExprSyntax, string4_wf,
    int3_wf, set4_expr_wf.
Qed.

Lemma bool4_type : forall id e, P4.C4BoolTree e ->
    HasType (somepaths []) (fixed_env id) (e, somepaths []) (boolType anyBool).
Proof.
  intros id e H; induction H.
  - eapply TLessThan; eauto using int3_type.
  - eapply TLessEqualThan; eauto using int3_type.
  - eapply TLike. eauto using string4_type.
  - eapply TNotAny. eauto.
  - eapply TCondTrue; [eauto|eauto using bool4_wf].
  - eapply TCondFalse; [eauto using bool4_wf|eauto].
  - unfold fixed_env. eapply TContains with (ns := Original.entity_names) (T := intType);
      eauto using fixed_defined, WfIntType, SubType, set4_type, int3_type.
  - unfold fixed_env. eapply TContainsAll with (ns := Original.entity_names) (T := intType);
      eauto using fixed_defined, WfIntType, SubType, set4_type.
  - unfold fixed_env. eapply TContainsAny with (ns := Original.entity_names) (T := intType);
      eauto using fixed_defined, WfIntType, SubType, set4_type.
Qed.

Lemma typed_if : forall id c e1 e2 t,
    HasType (somepaths []) (fixed_env id) (c, somepaths []) (boolType anyBool) ->
    HasType (somepaths []) (fixed_env id) (e1, somepaths []) t ->
    HasType (somepaths []) (fixed_env id) (e2, somepaths []) t ->
    HasType (somepaths []) (fixed_env id)
      (ite c e1 e2, somepaths []) t.
Proof.
  intros id c e1 e2 t Hc H1 H2.
  eapply TCondBool with (T2 := t) (T3 := t)
    (x1 := somepaths []) (x2 := somepaths []) (x3 := somepaths []);
    simpl; eauto using BranchJoin.
Qed.

Lemma typed_and : forall id e1 e2,
    HasType (somepaths []) (fixed_env id) (e1, somepaths []) (boolType anyBool) ->
    HasType (somepaths []) (fixed_env id) (e2, somepaths []) (boolType anyBool) ->
    HasType (somepaths []) (fixed_env id)
      (andExpr e1 e2, somepaths []) (boolType anyBool).
Proof.
  intros id e1 e2 H1 H2. eapply TAnd.
  eapply TCondBool with (T2 := boolType anyBool) (T3 := boolType ff_)
    (x1 := somepaths []) (x2 := somepaths []) (x3 := allpaths);
    simpl; eauto using BranchJoin, HasType, HasTypePrim.
Qed.

Lemma bool6_type : forall id e, P6.C6BoolTree e ->
    HasType (somepaths []) (fixed_env id) (e, somepaths []) (boolType anyBool).
Proof.
  intros id e H; induction H.
  - eauto using bool4_type.
  - eapply TNotAny; eauto.
  - eauto using typed_and.
  - eauto using typed_if.
Qed.

Lemma bool6_wf : forall e, P6.C6BoolTree e -> WfExprSyntax e.
Proof. intros e H; induction H; eauto using WfExprSyntax, bool4_wf. Qed.

Lemma int7_wf : forall e, P7.C7IntTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto using WfExprSyntax, int3_wf, bool6_wf.
Qed.

Lemma int7_type : forall id e, P7.C7IntTree e ->
    HasType (somepaths []) (fixed_env id) (e, somepaths []) intType.
Proof.
  intros id e H; induction H.
  - eauto using int3_type.
  - eapply TNeg; eauto.
  - eapply TAdd; eauto.
  - eapply TSub; eauto.
  - eapply TMul; eauto.
  - eapply typed_if; eauto using bool6_type.
Qed.

Lemma set7_wf : forall e, P7.C7IntSet e -> WfSetSyntax e.
Proof.
  intros e H; induction H; constructor; eauto using int7_wf, WfSetSyntax.
Qed.

Lemma set7_type : forall id e, P7.C7IntSet e ->
    HasType (somepaths []) (fixed_env id) (e, somepaths []) (setType intType).
Proof.
  intros id e H; induction H.
  - eapply TSetSingle. eauto using int7_type.
  - eapply TSetMany; eauto using int7_type, set7_wf.
Qed.

Lemma bool7_type : forall id e, P7.C7BoolTree e ->
    HasType (somepaths []) (fixed_env id) (e, somepaths []) (boolType anyBool).
Proof.
  intros id e H; induction H.
  - eauto using bool6_type.
  - eapply TLessThan; eauto using int7_type.
  - eapply TLessEqualThan; eauto using int7_type.
  - unfold fixed_env. eapply TContains with (ns := Original.entity_names) (T := intType);
      eauto using fixed_defined, WfIntType, SubType, set7_type, int7_type.
  - unfold fixed_env. eapply TContainsAll with (ns := Original.entity_names) (T := intType);
      eauto using fixed_defined, WfIntType, SubType, set7_type.
  - unfold fixed_env. eapply TContainsAny with (ns := Original.entity_names) (T := intType);
      eauto using fixed_defined, WfIntType, SubType, set7_type.
  - eapply TNotAny; eauto.
  - eauto using typed_and.
  - eauto using typed_if.
Qed.

Lemma case7_wf : forall id t p, P7.C7Case t p ->
    WfCedarType Original.entity_names t /\
    HasType (somepaths []) (fixed_env id) p t.
Proof.
  intros id t p H; induction H; split.
  - constructor.
  - eauto using int7_type.
  - constructor. constructor.
  - eauto using set7_type.
  - constructor.
  - eauto using bool7_type.
  - constructor.
  - eauto using typed_if, bool7_type, int7_type.
  - constructor. constructor.
  - eauto using typed_if, bool7_type, set7_type.
  - constructor.
  - eauto using typed_if, bool7_type, string4_type.
  - constructor. constructor.
  - eapply TRecCons with (x := somepaths []) (rx := somepaths []);
      eauto using int7_type, RecordType, WfRecSyntax, NotInRecExpr, HasType.
  - constructor.
  - eapply TGetAttrRecReq with
        (TE := recordTypeCons field false intType recordTypeNil)
        (ns := Original.entity_names) (ets := fixed_ets)
        (acts := fixed_acts id) (R := fixed_request id)
        (x := somepaths []);
      eauto using fixed_defined, int7_type, HasType, RecordType,
        WfRecSyntax, NotInRecExpr, WfRecordType, WfCedarType, BindAttrType.
Qed.

Lemma structured7_in_6 : forall id t p,
    P7.C7Case t p -> P6.predicate (fixed_input id t p).
Proof.
  intros id t p H. destruct (case7_wf id t p H) as [Ht Hp].
  apply P6.C6Inherited. apply Property.candidates.v005.Candidate.C5Inherited.
  apply P4.C4Inherited. apply P3.C3Inherited.
  apply Property.candidates.v002.Candidate.Inherited.
  apply P1.General; eauto using fixed_schema, fixed_request_types,
    fixed_environments.
Qed.

Theorem equivalent : forall x : Original.Input,
  P6.predicate x <-> P7.predicate x.
Proof.
  intro x. split.
  - apply P7.C7Inherited.
  - intro H. inversion H; subst.
    + assumption.
    + change (P6.predicate (fixed_input action_id ty expr)).
      eauto using structured7_in_6.
Qed.
