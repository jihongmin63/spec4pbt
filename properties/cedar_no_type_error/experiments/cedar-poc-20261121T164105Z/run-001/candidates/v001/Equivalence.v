Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Import ListNotations.
Open Scope string_scope.

Definition example_ets : list (EntityName * EntitySchemaEntry) :=
  [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
   (MkName "EntityType2" [], MkEntitySchemaEntry [] [])].

Definition example_acts (s : string) : list (EntityUID * ActionSchemaEntry) :=
  [(MkEntityUID (MkName "Action" []) s,
    MkActionSchemaEntry [MkName "EntityType1" []]
                        [MkName "EntityType1" []] [])].

Definition example_req (s : string) : RequestType :=
  MkRequest (MkName "EntityType1" [])
            (MkEntityUID (MkName "Action" []) s)
            (MkName "EntityType1" []) [].

Definition example_env (s : string) : Environment :=
  MkEnvironment (MkSchema example_ets (example_acts s)) (example_req s).

Lemma example_schema : forall s,
  WfSchema Original.entity_names (MkSchema example_ets (example_acts s)).
Proof.
  intro s.
  unfold Original.entity_names, example_ets, example_acts.
  eapply WfS with (acts :=
    [(MkEntityUID (MkName "Action" []) s,
      MkActionSchemaEntry [MkName "EntityType1" []]
                          [MkName "EntityType1" []] [])]).
  - eapply WfETSCons.
    + apply DNFound. reflexivity.
    + apply NIECons. discriminate. apply NIENil.
    + apply WfETSingle; constructor.
    + apply WfETSSingle.
      * apply DNRest. discriminate. apply DNFound. reflexivity.
      * apply WfETSingle; constructor.
  - apply WfACTSSingle. apply WfACTSingle.
    + apply DNFound. reflexivity.
    + apply DNFound. reflexivity.
    + apply WfAttrsNil.
  - reflexivity.
Qed.

Lemma example_base : forall s ty expr,
  WfCedarType Original.entity_names ty ->
  HasType (somepaths []) (example_env s) expr ty ->
  Original.predicate
    (Original.mkInput example_ets (example_acts s) [example_req s]
      (example_env s) [] ty expr).
Proof.
  intros s ty expr Hty Hexpr.
  unfold Original.predicate; simpl.
  repeat split.
  - apply example_schema.
  - apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
  - apply MkEnvsSingle.
  - exact Hty.
  - exact Hexpr.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.Original.predicate x <->
  Property.candidates.v001.Candidate.predicate x.
Proof.
  intro x. split.
  - destruct x as [ets acts rs e es ty expr].
    unfold Original.predicate; simpl.
    intros [Hs [Hr [He [Ht Hexpr]]]].
    apply Candidate.General; assumption.
  - intro H. destruct H as
      [ets acts rs e es ty expr Hs Hr He Ht Hexpr | s | s | s].
    + unfold Original.predicate; simpl.
      repeat split; assumption.
    + apply example_base.
      * apply WfRecordTypeNil.
      * apply TRecNil.
    + apply example_base.
      * apply WfBoolType.
      * apply TLitOther.
        -- discriminate.
        -- apply TTrue.
    + apply example_base.
      * apply WfBoolType.
      * apply TLitFalse. apply TFalse.
Qed.
