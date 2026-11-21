Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Import ListNotations.

Lemma seed_wf_schema : forall ets acts req,
  Candidate.SeedSchema ets acts req ->
  WfSchema Original.entity_names (MkSchema ets acts).
Proof.
  intros ets acts req Hseed.
  inversion Hseed; subst; clear Hseed.
  unfold Original.entity_names.
  eapply WfS with
    (acts := [(MkEntityUID (MkName "Action" []) id,
               MkActionSchemaEntry [MkName "EntityType1" []]
                                   [MkName "EntityType2" []] [])]).
  - eapply WfETSCons.
    + apply DNFound. reflexivity.
    + apply NIECons.
      * discriminate.
      * apply NIENil.
    + apply WfETSingle; constructor.
    + eapply WfETSSingle.
      * apply DNRest.
        -- discriminate.
        -- apply DNFound. reflexivity.
      * apply WfETSingle; constructor.
  - apply WfACTSSingle.
    apply WfACTSingle.
    + apply DNFound. reflexivity.
    + apply DNRest.
      * discriminate.
      * apply DNFound. reflexivity.
    + apply WfAttrsNil.
  - reflexivity.
Qed.

Lemma seed_requests : forall ets acts req,
  Candidate.SeedSchema ets acts req ->
  ActionSchemaToRequestTypes acts [] [req].
Proof.
  intros ets acts req Hseed.
  inversion Hseed; subst; clear Hseed.
  apply ASTESingle.
  apply ASTRTSingle.
  apply ATRTSingle.
Qed.

Lemma seed_environments : forall ets acts req,
  Candidate.SeedSchema ets acts req ->
  SchemaToEnvironments (MkSchema ets acts) [req]
    [MkEnvironment (MkSchema ets acts) req].
Proof.
  intros. apply MkEnvsSingle.
Qed.

Lemma seed_entity_type_1 :
  WfCedarType Original.entity_names
    (entityType (MkName "EntityType1" [])).
Proof.
  apply WfEntityType.
  unfold Original.entity_names.
  apply DNFound. reflexivity.
Qed.

Lemma seed_entity_type_2 :
  WfCedarType Original.entity_names
    (entityType (MkName "EntityType2" [])).
Proof.
  apply WfEntityType.
  unfold Original.entity_names.
  apply DNRest.
  - discriminate.
  - apply DNFound. reflexivity.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.Original.predicate x <->
  Property.candidates.v001.Candidate.predicate x.
Proof.
  intro x; split.
  - destruct x as [ets acts rs e es ty expr].
    unfold Original.predicate; simpl.
    intros [Hschema [Hrequests [Henv [Htype Hexpr]]]].
    apply Candidate.CGeneral; assumption.
  - intro Hcandidate.
    destruct Hcandidate as
      [ets acts req Hseed
      |ets acts req Hseed
      |ets acts req n Hseed
      |ets acts req s Hseed
      |ets acts req Hseed
      |ets acts req Hseed
      |ets acts req Hseed
      |ets acts rs e es ty expr Hschema Hrequests Henv Htype Hexpr];
      unfold Original.predicate; simpl.
    + repeat split.
      * apply seed_wf_schema with (req := req); assumption.
      * eapply seed_requests; eassumption.
      * apply seed_environments; assumption.
      * apply WfBoolType.
      * apply TLitFalse. apply TFalse.
    + repeat split.
      * apply seed_wf_schema with (req := req); assumption.
      * eapply seed_requests; eassumption.
      * apply seed_environments; assumption.
      * apply WfBoolType.
      * apply TLitOther.
        -- discriminate.
        -- apply TTrue.
    + repeat split.
      * apply seed_wf_schema with (req := req); assumption.
      * eapply seed_requests; eassumption.
      * apply seed_environments; assumption.
      * apply WfIntType.
      * apply TLitOther.
        -- discriminate.
        -- apply TInt.
    + repeat split.
      * apply seed_wf_schema with (req := req); assumption.
      * eapply seed_requests; eassumption.
      * apply seed_environments; assumption.
      * apply WfStringType.
      * apply TLitOther.
        -- discriminate.
        -- apply TString.
    + repeat split.
      * apply seed_wf_schema with (req := req); assumption.
      * eapply seed_requests; eassumption.
      * apply seed_environments; assumption.
      * apply seed_entity_type_1.
      * apply TVar. inversion Hseed; subst. apply TPrincipal.
    + repeat split.
      * apply seed_wf_schema with (req := req); assumption.
      * eapply seed_requests; eassumption.
      * apply seed_environments; assumption.
      * apply seed_entity_type_2.
      * apply TVar. inversion Hseed; subst. apply TResource.
    + repeat split.
      * apply seed_wf_schema with (req := req); assumption.
      * eapply seed_requests; eassumption.
      * apply seed_environments; assumption.
      * apply WfRecordTypeNil.
      * apply TVar. inversion Hseed; subst. apply TContext. apply RNil.
    + repeat split; assumption.
Qed.
