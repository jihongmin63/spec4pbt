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

Definition name1 := MkName "EntityType1" [].
Definition name2 := MkName "EntityType2" [].
Definition ground_ets : list (EntityName * EntitySchemaEntry) :=
  [(name1, MkEntitySchemaEntry [] []);
   (name2, MkEntitySchemaEntry [] [])].
Definition ground_act (id : string) : EntityUID * ActionSchemaEntry :=
  (MkEntityUID (MkName "Action" []) id,
   MkActionSchemaEntry [name1] [name2] []).
Definition ground_req (id : string) : RequestType :=
  MkRequest name1 (MkEntityUID (MkName "Action" []) id) name2 [].
Definition ground_env (id : string) : Environment :=
  MkEnvironment (MkSchema ground_ets [ground_act id]) (ground_req id).
Definition ground_input (id : string) (ty : CedarType)
    (expr : CedarExpr * PathSet) : Original.Input :=
  Original.mkInput ground_ets [ground_act id] [ground_req id]
    (ground_env id) [] ty expr.

Lemma name1_defined : DefinedName Original.entity_names name1.
Proof. apply DNFound. reflexivity. Qed.

Lemma name2_defined : DefinedName Original.entity_names name2.
Proof.
  apply DNRest.
  - discriminate.
  - apply DNFound. reflexivity.
Qed.

Lemma ground_schema : forall id,
  WfSchema Original.entity_names (MkSchema ground_ets [ground_act id]).
Proof.
  intro id.
  apply (WfS _ _ [ground_act id] [ground_act id]).
  - unfold ground_ets, Original.entity_names.
    apply WfETSCons.
    + exact name1_defined.
    + apply NIECons; [discriminate | constructor].
    + constructor; constructor.
    + apply WfETSSingle.
      * exact name2_defined.
      * constructor; constructor.
  - apply WfACTSSingle.
    unfold ground_act.
    apply WfACTSingle.
    + exact name1_defined.
    + exact name2_defined.
    + constructor.
  - reflexivity.
Qed.

Lemma ground_requests : forall id,
  ActionSchemaToRequestTypes [ground_act id] [] [ground_req id].
Proof. intro id; unfold ground_act, ground_req; repeat constructor. Qed.

Lemma ground_environments : forall id,
  SchemaToEnvironments (MkSchema ground_ets [ground_act id])
    [ground_req id] [ground_env id].
Proof. intro id; unfold ground_env; constructor. Qed.

Lemma ground_int_typed : forall V e, C4.GroundInt e ->
  HasType (somepaths []) V (e, somepaths []) intType.
Proof.
  intros V e H; induction H.
  - apply TLitOther; [discriminate | constructor].
  - eapply TNeg; eassumption.
  - eapply TAdd; eassumption.
  - eapply TSub; eassumption.
  - eapply TMul; eassumption.
Qed.

Lemma ground_type_wf : forall ty expr,
  C4.GroundTyped ty expr -> WfCedarType Original.entity_names ty.
Proof. intros ty expr H; destruct H; repeat constructor. Qed.

Lemma ground_expr_typed : forall V ty expr,
  C4.GroundTyped ty expr -> HasType (somepaths []) V expr ty.
Proof.
  intros V ty expr H; destruct H.
  - apply ground_int_typed; assumption.
  - eapply TLessThan; apply ground_int_typed; assumption.
  - eapply TLessEqualThan; apply ground_int_typed; assumption.
  - eapply TSetSingle; apply ground_int_typed; assumption.
  - eapply TRecCons.
    + apply ground_int_typed; assumption.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
  - eapply TEqLitTrue. constructor.
  - apply TLitFalse. constructor.
  - eapply TNotTrue. apply TLitOther; [discriminate | constructor].
  - eapply TNotFalse. apply TLitFalse. constructor.
Qed.

Lemma ground_in_v003 : forall id ty expr,
  C4.GroundTyped ty expr -> C3.predicate (ground_input id ty expr).
Proof.
  intros id ty expr H.
  apply C3.General. apply C2.General.
  unfold ground_input.
  eapply C1.Build.
  - apply ground_schema.
  - apply ground_requests.
  - apply ground_environments.
  - eapply ground_type_wf; eassumption.
  - eapply ground_expr_typed; eassumption.
Qed.

Theorem equivalent : forall x : Original.Input,
  C3.predicate x <-> C4.predicate x.
Proof.
  intro x; split.
  - intro H. apply C4.General. exact H.
  - intro H. inversion H; subst.
    + apply ground_in_v003. assumption.
    + assumption.
Qed.
