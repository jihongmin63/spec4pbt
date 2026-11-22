Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v008.Candidate.
Require Import Property.candidates.v009.Candidate.
Import ListNotations.
Open Scope string_scope.

Lemma tiny_schema_preconditions : forall ets acts r,
  Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
  WfSchema Original.entity_names (MkSchema ets acts) /\
  ActionSchemaToRequestTypes acts [] [r].
Proof.
  intros ets acts r H.
  inversion H; subst; clear H.
  split.
  - unfold Original.entity_names.
    eapply WfS with
      (acts := [(MkEntityUID (MkName "Action" []) id,
                 MkActionSchemaEntry
                   [MkName "EntityType1" []]
                   [MkName "EntityType1" []] [])]).
    + eapply WfETSCons.
      * apply DNFound. reflexivity.
      * apply NIECons; [discriminate | constructor].
      * constructor; constructor.
      * eapply WfETSSingle.
        -- apply DNRest; [discriminate | apply DNFound; reflexivity].
        -- constructor; constructor.
    + apply WfACTSSingle. constructor.
      * apply DNFound. reflexivity.
      * apply DNFound. reflexivity.
      * constructor.
    + reflexivity.
  - apply ASTESingle. apply ASTRTSingle. constructor.
Qed.

Lemma principal_in_previous : forall ets acts r,
  Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
  Property.candidates.v008.Candidate.predicate
    (Original.mkInput ets acts [r]
      (MkEnvironment (MkSchema ets acts) r) []
      (entityType (MkName "EntityType1" []))
      (var principal, somepaths [])).
Proof.
  intros ets acts r H.
  destruct (tiny_schema_preconditions ets acts r H) as [Hs Hr].
  inversion H; subst.
  apply Property.candidates.v008.Candidate.PredicatePrevious.
  apply Property.candidates.v007.Candidate.PredicatePrevious.
  apply Property.candidates.v006.Candidate.PredicatePrevious.
  apply Property.candidates.v005.Candidate.PredicatePrevious.
  apply Property.candidates.v004.Candidate.PredicatePrevious.
  apply Property.candidates.v003.Candidate.PredicatePrevious.
  apply Property.candidates.v002.Candidate.PredicateEnvironments.
  - exact Hs.
  - exact Hr.
  - constructor.
  - apply WfEntityType. apply DNFound. reflexivity.
  - apply TVar. constructor.
Qed.

Lemma resource_in_previous : forall ets acts r,
  Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
  Property.candidates.v008.Candidate.predicate
    (Original.mkInput ets acts [r]
      (MkEnvironment (MkSchema ets acts) r) []
      (entityType (MkName "EntityType1" []))
      (var resource, somepaths [])).
Proof.
  intros ets acts r H.
  destruct (tiny_schema_preconditions ets acts r H) as [Hs Hr].
  inversion H; subst.
  apply Property.candidates.v008.Candidate.PredicatePrevious.
  apply Property.candidates.v007.Candidate.PredicatePrevious.
  apply Property.candidates.v006.Candidate.PredicatePrevious.
  apply Property.candidates.v005.Candidate.PredicatePrevious.
  apply Property.candidates.v004.Candidate.PredicatePrevious.
  apply Property.candidates.v003.Candidate.PredicatePrevious.
  apply Property.candidates.v002.Candidate.PredicateEnvironments.
  - exact Hs.
  - exact Hr.
  - constructor.
  - apply WfEntityType. apply DNFound. reflexivity.
  - apply TVar. constructor.
Qed.

Lemma context_in_previous : forall ets acts r,
  Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
  Property.candidates.v008.Candidate.predicate
    (Original.mkInput ets acts [r]
      (MkEnvironment (MkSchema ets acts) r) []
      recordTypeNil (var context, somepaths [])).
Proof.
  intros ets acts r H.
  destruct (tiny_schema_preconditions ets acts r H) as [Hs Hr].
  inversion H; subst.
  apply Property.candidates.v008.Candidate.PredicatePrevious.
  apply Property.candidates.v007.Candidate.PredicatePrevious.
  apply Property.candidates.v006.Candidate.PredicatePrevious.
  apply Property.candidates.v005.Candidate.PredicatePrevious.
  apply Property.candidates.v004.Candidate.PredicatePrevious.
  apply Property.candidates.v003.Candidate.PredicatePrevious.
  apply Property.candidates.v002.Candidate.PredicateEnvironments.
  - exact Hs.
  - exact Hr.
  - constructor.
  - constructor.
  - apply TVar. apply TContext. constructor.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v008.Candidate.predicate x <->
  Property.candidates.v009.Candidate.predicate x.
Proof.
  intro x; split.
  - intro H. apply Property.candidates.v009.Candidate.PredicatePrevious. exact H.
  - intro H. inversion H; subst.
    + apply principal_in_previous. assumption.
    + apply resource_in_previous. assumption.
    + apply context_in_previous. assumption.
    + assumption.
Qed.
