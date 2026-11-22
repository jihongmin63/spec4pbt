Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Import ListNotations.
Open Scope string_scope.

Definition simple_ets : list (EntityName * EntitySchemaEntry) :=
  [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
   (MkName "EntityType2" [], MkEntitySchemaEntry [] [])].

Definition simple_acts (s : string) : list (EntityUID * ActionSchemaEntry) :=
  [(MkEntityUID (MkName "Action" []) s,
    MkActionSchemaEntry [MkName "EntityType1" []]
                        [MkName "EntityType1" []] [])].

Definition simple_request (s : string) : RequestType :=
  MkRequest (MkName "EntityType1" [])
            (MkEntityUID (MkName "Action" []) s)
            (MkName "EntityType1" []) [].

Definition simple_environment (s : string) : Environment :=
  MkEnvironment (MkSchema simple_ets (simple_acts s)) (simple_request s).

Definition simple_input (s : string) (ty : CedarType)
    (expr : CedarExpr * PathSet) : Original.Input :=
  Original.mkInput simple_ets (simple_acts s) [simple_request s]
                   (simple_environment s) [] ty expr.

Lemma simple_schema_wf : forall s,
  WfSchema Original.entity_names (MkSchema simple_ets (simple_acts s)).
Proof.
  intro s. unfold Original.entity_names, simple_ets, simple_acts.
  eapply WfS.
  - apply WfETSCons.
    + apply DNFound. reflexivity.
    + apply NIECons; [discriminate | apply NIENil].
    + apply WfETSingle; constructor.
    + apply WfETSSingle.
      * apply DNRest; [discriminate | apply DNFound; reflexivity].
      * apply WfETSingle; constructor.
  - apply WfACTSSingle. apply WfACTSingle.
    + apply DNFound. reflexivity.
    + apply DNFound. reflexivity.
    + apply WfAttrsNil.
  - reflexivity.
Qed.

Lemma simple_action_requests : forall s,
  ActionSchemaToRequestTypes (simple_acts s) [] [simple_request s].
Proof.
  intro s. unfold simple_acts, simple_request.
  apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
Qed.

Lemma simple_environments : forall s,
  SchemaToEnvironments (MkSchema simple_ets (simple_acts s))
    [simple_request s] [simple_environment s].
Proof. intro s. unfold simple_environment. constructor. Qed.

Lemma simple_type_wf : forall ty expr,
  Property.candidates.v002.Candidate.SimpleCase ty expr ->
  WfCedarType Original.entity_names ty.
Proof.
  intros ty expr H. destruct H; unfold Original.entity_names;
    eauto using WfBoolType, WfIntType, WfStringType, WfEntityType,
      WfSetType, WfRecordTypeNil, WfRecordTypeConsNil, DNFound.
Qed.

Lemma simple_typed : forall s ty expr,
  Property.candidates.v002.Candidate.SimpleCase ty expr ->
  HasType (somepaths []) (simple_environment s) expr ty.
Proof.
  intros s ty expr H. destruct H; simpl.
  - apply TLitOther; [discriminate | constructor].
  - apply TLitOther; [discriminate | constructor].
  - apply TVar. apply TPrincipal.
  - apply TVar. apply TResource.
  - apply TVar. apply TContext. apply RNil.
  - eapply TNotTrue. apply TLitOther; [discriminate | constructor].
  - eapply TNotFalse. apply TLitFalse. constructor.
  - eapply TNeg. apply TLitOther; [discriminate | constructor].
  - eapply TLike. apply TLitOther; [discriminate | constructor].
  - eapply TAdd.
    + apply TLitOther; [discriminate | constructor].
    + apply TLitOther; [discriminate | constructor].
  - eapply TSub.
    + apply TLitOther; [discriminate | constructor].
    + apply TLitOther; [discriminate | constructor].
  - eapply TMul.
    + apply TLitOther; [discriminate | constructor].
    + apply TLitOther; [discriminate | constructor].
  - eapply TLessThan.
    + apply TLitOther; [discriminate | constructor].
    + apply TLitOther; [discriminate | constructor].
  - eapply TLessEqualThan.
    + apply TLitOther; [discriminate | constructor].
    + apply TLitOther; [discriminate | constructor].
  - eapply TEqLitTrue. constructor.
  - eapply TSetSingle. apply TLitOther; [discriminate | constructor].
  - eapply TRecCons.
    + apply TLitOther; [discriminate | constructor].
    + apply RTNil.
    + apply TRecNil.
    + apply WFRNil.
    + apply NIRNil.
  - eapply TCondTrue.
    + apply TLitOther; [discriminate | constructor].
    + constructor.
  - eapply TCondFalse.
    + constructor.
    + apply TLitOther; [discriminate | constructor].
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v001.Candidate.predicate x <->
  Property.candidates.v002.Candidate.predicate x.
Proof.
  intro x. split.
  - intro H. apply Property.candidates.v002.Candidate.Inherited. exact H.
  - intro H. destruct H as [i H | s ty expr H].
    + exact H.
    + change (Property.candidates.v001.Candidate.predicate
                (simple_input s ty expr)).
      apply Property.candidates.v001.Candidate.General.
      * apply simple_schema_wf.
      * apply simple_action_requests.
      * apply simple_environments.
      * eapply simple_type_wf. exact H.
      * eapply simple_typed. exact H.
Qed.
