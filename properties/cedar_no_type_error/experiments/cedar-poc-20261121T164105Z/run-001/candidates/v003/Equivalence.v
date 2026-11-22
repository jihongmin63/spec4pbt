Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Import ListNotations.
Open Scope string_scope.

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
    (expr : CedarExpr * PathSet) : Original.Input :=
  Original.mkInput base_ets (base_acts id) [base_req id]
                   (base_env id) [] ty expr.

Lemma base_schema_ok : forall id,
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
    + apply WfAttrsNil.
  - reflexivity.
Qed.

Lemma base_request_ok : forall id,
  ActionSchemaToRequestTypes (base_acts id) [] [base_req id].
Proof.
  intro id. unfold base_acts, base_req.
  eapply ASTESingle. eapply ASTRTSingle. apply ATRTSingle.
Qed.

Lemma base_environments_ok : forall id,
  SchemaToEnvironments (MkSchema base_ets (base_acts id))
                       [base_req id] [base_env id].
Proof.
  intro id. unfold base_env. apply MkEnvsSingle.
Qed.

Lemma int_tree_wf : forall e,
  Property.candidates.v003.Candidate.IntTree e -> WfExprSyntax e.
Proof.
  intros e H. induction H;
    eauto using WFSPrim, WFSUnary, WFSBinary, WFSIte.
Qed.

Lemma int_tree_typed : forall a V e,
  Property.candidates.v003.Candidate.IntTree e ->
  HasType a V (e, somepaths []) intType.
Proof.
  intros a V e H. induction H.
  - apply TLitOther; [discriminate | apply TInt].
  - eapply TNeg. exact IHIntTree.
  - eapply TAdd; eassumption.
  - eapply TSub; eassumption.
  - eapply TMul; eassumption.
  - eapply TCondTrue; [exact IHIntTree1 | apply int_tree_wf; assumption].
  - eapply TCondFalse; [apply int_tree_wf; assumption | exact IHIntTree2].
Qed.

Lemma base_entities_defined : DefinedEntities base_ets Original.entity_names.
Proof.
  unfold base_ets, Original.entity_names. repeat constructor.
Qed.

Lemma composite_typed : forall id ty expr,
  Property.candidates.v003.Candidate.CompositeCase ty expr ->
  HasType (somepaths []) (base_env id) expr ty.
Proof.
  intros id ty expr H. inversion H; subst; clear H.
  - apply int_tree_typed. assumption.
  - eapply TLessThan; apply int_tree_typed; eassumption.
  - eapply TLessEqualThan; apply int_tree_typed; eassumption.
  - eapply TEqAny with (T := intType)
                        (ets := base_ets) (acts := base_acts id)
                        (R := base_req id) (ns := Original.entity_names).
    + reflexivity.
    + apply base_entities_defined.
    + apply WfIntType.
    + apply ST.
    + apply ST.
    + apply int_tree_typed. assumption.
    + apply int_tree_typed. assumption.
  - eapply TSetSingle. apply int_tree_typed. assumption.
  - eapply TRecCons.
    + apply int_tree_typed. assumption.
    + apply RTNil.
    + apply TRecNil.
    + apply WFRNil.
    + apply NIRNil.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v002.Candidate.predicate x <->
  Property.candidates.v003.Candidate.predicate x.
Proof.
  intro x. split.
  - intro H. apply Property.candidates.v003.Candidate.C3Inherited. exact H.
  - intro H. inversion H; subst.
    + assumption.
    + change (Property.candidates.v002.Candidate.predicate
                (base_input action_id ty expr)).
      apply Property.candidates.v002.Candidate.Inherited.
      apply Property.candidates.v001.Candidate.General.
      * apply base_schema_ok.
      * apply base_request_ok.
      * apply base_environments_ok.
      * inversion H0; subst; simpl;
          eauto using WfIntType, WfSetType, WfBoolType,
                      WfRecordTypeConsNil, WfRecordTypeNil.
      * apply composite_typed. assumption.
Qed.
