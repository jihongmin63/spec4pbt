Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Require Import Property.candidates.v006.Candidate.
Import ListNotations.
Open Scope string_scope.

Definition base_names : list EntityName :=
  [MkName "EntityType1" []; MkName "EntityType2" []].
Definition base_ets : list (EntityName * EntitySchemaEntry) :=
  [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
   (MkName "EntityType2" [], MkEntitySchemaEntry [] [])].
Definition base_acts (s : string) : list (EntityUID * ActionSchemaEntry) :=
  [(MkEntityUID (MkName "Action" []) s,
    MkActionSchemaEntry [MkName "EntityType1" []]
                        [MkName "EntityType1" []] [])].
Definition base_req (s : string) : RequestType :=
  MkRequest (MkName "EntityType1" [])
            (MkEntityUID (MkName "Action" []) s)
            (MkName "EntityType1" []) [].
Definition base_env (s : string) : Environment :=
  MkEnvironment (MkSchema base_ets (base_acts s)) (base_req s).

Lemma int_syntax : forall e, Property.candidates.v003.Candidate.IntTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto 3 using WfExprSyntax.
Qed.

Lemma int_typed : forall e, Property.candidates.v003.Candidate.IntTree e ->
  forall V a, HasType a V (e, somepaths []) intType.
Proof.
  intros e H; induction H; intros V a.
  - eapply TLitOther; [discriminate | constructor].
  - eapply TNeg; eauto.
  - eapply TAdd; eauto.
  - eapply TSub; eauto.
  - eapply TMul; eauto.
  - eapply TCondTrue; [eauto | eauto using int_syntax].
  - eapply TCondFalse; [eauto using int_syntax | eauto].
Qed.

Lemma string_syntax : forall e, Property.candidates.v004.Candidate.C4StringTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto 3 using WfExprSyntax.
Qed.

Lemma string_typed : forall e, Property.candidates.v004.Candidate.C4StringTree e ->
  forall V a, HasType a V (e, somepaths []) stringType.
Proof.
  intros e H; induction H; intros V a.
  - eapply TLitOther; [discriminate | constructor].
  - eapply TCondTrue; [eauto | eauto using string_syntax].
  - eapply TCondFalse; [eauto using string_syntax | eauto].
Qed.

Lemma set_syntax : forall e, Property.candidates.v004.Candidate.C4IntSet e -> WfSetSyntax e.
Proof.
  intros e H; induction H; constructor; eauto using int_syntax, WfSetSyntax.
Qed.

Lemma set_expr_syntax : forall e,
  Property.candidates.v004.Candidate.C4IntSet e -> WfExprSyntax e.
Proof.
  intros e H; destruct H; apply WFSSetCons;
    eauto using int_syntax, set_syntax, WfSetSyntax.
Qed.

Lemma set_typed : forall e, Property.candidates.v004.Candidate.C4IntSet e ->
  forall V a, HasType a V (e, somepaths []) (setType intType).
Proof.
  intros e H; induction H; intros V a.
  - eapply TSetSingle; eauto using int_typed.
  - eapply TSetMany; eauto using int_typed, set_syntax.
Qed.

Lemma base_entities : DefinedEntities base_ets base_names.
Proof. repeat constructor. Qed.

Lemma bool_syntax : forall e, Property.candidates.v004.Candidate.C4BoolTree e -> WfExprSyntax e.
Proof.
  intros e H; induction H; eauto 4 using WfExprSyntax, int_syntax,
    string_syntax, set_expr_syntax.
Qed.

Lemma bool_typed : forall e, Property.candidates.v004.Candidate.C4BoolTree e ->
  forall s a, HasType a (base_env s) (e, somepaths []) (boolType anyBool).
Proof.
  intros e H; induction H; intros s a.
  - eapply TLessThan; eauto using int_typed.
  - eapply TLessEqualThan; eauto using int_typed.
  - eapply TLike; eauto using string_typed.
  - eapply TNotAny; eauto.
  - eapply TCondTrue; [eauto | eauto using bool_syntax].
  - eapply TCondFalse; [eauto using bool_syntax | eauto].
  - eapply TContains with (T:=intType) (T1:=intType) (T2:=intType)
      (ns:=base_names) (ets:=base_ets) (acts:=base_acts s) (R:=base_req s);
      eauto using set_typed, int_typed, base_entities, WfCedarType, SubType.
  - eapply TContainsAll with (T:=intType) (T1:=intType) (T2:=intType)
      (ns:=base_names) (ets:=base_ets) (acts:=base_acts s) (R:=base_req s);
      eauto using set_typed, base_entities, WfCedarType, SubType.
  - eapply TContainsAny with (T:=intType) (T1:=intType) (T2:=intType)
      (ns:=base_names) (ets:=base_ets) (acts:=base_acts s) (R:=base_req s);
      eauto using set_typed, base_entities, WfCedarType, SubType.
Qed.

Lemma c6_bool_typed : forall e, Property.candidates.v006.Candidate.C6BoolTree e ->
  forall s a, HasType a (base_env s) (e, somepaths []) (boolType anyBool).
Proof.
  intros e H; induction H; intros s a.
  - eauto using bool_typed.
  - eapply TNotAny; eauto.
  - eapply TAnd.
    eapply TCondBool with (x1:=somepaths []) (x2:=somepaths [])
                           (x3:=allpaths) (T2:=boolType anyBool)
                           (T3:=boolType ff_).
    + apply BJBool.
    + eauto.
    + eauto.
    + apply TLitFalse. constructor.
    + reflexivity.
  - eapply TCondBool with (x1:=somepaths []) (x2:=somepaths [])
                           (x3:=somepaths []) (T2:=boolType anyBool)
                           (T3:=boolType anyBool).
    + apply BJExact.
    + eauto.
    + eauto.
    + eauto.
    + reflexivity.
Qed.

Lemma c6_case_typed : forall ty expr,
  Property.candidates.v006.Candidate.C6Case ty expr ->
  forall s a, HasType a (base_env s) expr ty.
Proof.
  intros ty expr H; induction H; intros s a.
  - eauto using c6_bool_typed.
  - eapply TCondBool with (x1:=somepaths []) (x2:=somepaths [])
                           (x3:=somepaths []) (T2:=intType) (T3:=intType).
    + apply BJExact.
    + eauto using c6_bool_typed.
    + eauto using int_typed.
    + eauto using int_typed.
    + reflexivity.
  - eapply TCondBool with (x1:=somepaths []) (x2:=somepaths [])
                           (x3:=somepaths []) (T2:=stringType) (T3:=stringType).
    + apply BJExact.
    + eauto using c6_bool_typed.
    + eauto using string_typed.
    + eauto using string_typed.
    + reflexivity.
Qed.

Lemma base_schema : forall s,
  WfSchema base_names (MkSchema base_ets (base_acts s)).
Proof.
  intro s. unfold base_names, base_ets, base_acts.
  eapply WfS with (acts:=
    [(MkEntityUID (MkName "Action" []) s,
      MkActionSchemaEntry [MkName "EntityType1" []]
                          [MkName "EntityType1" []] [])]); simpl.
  - eapply WfETSCons.
    + apply DNFound. reflexivity.
    + apply NIECons. discriminate. constructor.
    + constructor; constructor.
    + eapply WfETSSingle.
      * apply DNRest. discriminate. apply DNFound. reflexivity.
      * constructor; constructor.
  - constructor. constructor.
    + apply DNFound. reflexivity.
    + apply DNFound. reflexivity.
    + constructor.
  - reflexivity.
Qed.

Lemma base_requests : forall s,
  ActionSchemaToRequestTypes (base_acts s) [] [base_req s].
Proof.
  intro s. unfold base_acts, base_req.
  eapply ASTESingle. eapply ASTRTSingle. constructor.
Qed.

Lemma base_environments : forall s,
  SchemaToEnvironments (MkSchema base_ets (base_acts s))
                       [base_req s] [base_env s].
Proof. intro s. unfold base_env. constructor. Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v005.Candidate.predicate x <->
  Property.candidates.v006.Candidate.predicate x.
Proof.
  intro x; split.
  - intro H. now apply Property.candidates.v006.Candidate.C6Inherited.
  - intro H. inversion H; subst.
    + assumption.
    + apply Property.candidates.v005.Candidate.C5Inherited.
      apply Property.candidates.v004.Candidate.C4Inherited.
      apply Property.candidates.v003.Candidate.C3Inherited.
      apply Property.candidates.v002.Candidate.Inherited.
      apply Property.candidates.v001.Candidate.General.
      * apply base_schema.
      * apply base_requests.
      * apply base_environments.
      * destruct H0; constructor.
      * apply c6_case_typed; assumption.
Qed.
