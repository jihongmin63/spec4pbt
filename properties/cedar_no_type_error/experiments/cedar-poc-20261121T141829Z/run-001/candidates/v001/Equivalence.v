Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Import ListNotations.
Open Scope string_scope.

Lemma wf_ets_shape : forall ets,
  WfETS Original.entity_names Original.entity_names ets ->
  exists et1 et2,
    ets = [(MkName "EntityType1" [], et1);
           (MkName "EntityType2" [], et2)].
Proof.
  intros ets H.
  unfold Original.entity_names in H.
  inversion H; subst.
  inversion H7; subst.
  - eexists; eexists; reflexivity.
  - inversion H11.
Qed.

Lemma wf_acts_shape : forall ns acts,
  WfACTS ns acts ->
  exists action_id principal_name resource_name attrs acts_tail,
    acts =
      (MkEntityUID (MkName "Action" []) action_id,
       MkActionSchemaEntry [principal_name] [resource_name] attrs)
      :: acts_tail.
Proof.
  intros ns acts H.
  inversion H; subst;
    match goal with
    | Hact : WfACT _ _ |- _ => inversion Hact; subst
    end;
    repeat eexists; reflexivity.
Qed.

Lemma env_shape : forall s rs e es,
  SchemaToEnvironments s rs (e :: es) ->
  exists request requests_tail,
    rs = request :: requests_tail /\ e = MkEnvironment s request.
Proof.
  intros s rs e es H.
  inversion H; subst; eauto.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.Original.predicate x <->
  Property.candidates.v001.Candidate.predicate x.
Proof.
  intros [ets acts rs e es ty expr].
  split.
  - unfold Original.predicate; simpl.
    intros [Hs [Hr [He [Ht Hexpr]]]].
    inversion Hs; subst.
    match goal with
    | Hets : WfETS _ _ _ |- _ =>
        destruct (wf_ets_shape _ Hets) as [et1 [et2 HetsEq]]
    end.
    subst ets.
    match goal with
    | Hacts : WfACTS _ _ |- _ =>
        destruct (wf_acts_shape _ _ Hacts)
          as [action_id [principal_name [resource_name
              [attrs [acts_tail HactsEq]]]]]
    end.
    subst acts0.
    cbn [dedupActsById dedupActsByIdAcc actionIdOf existsb] in *.
    destruct (env_shape _ _ _ _ He) as
      [request [requests_tail [Hrs Heq]]].
    subst rs e.
    apply Candidate.CandidateInput; assumption.
  - intro H.
    inversion H; subst.
    unfold Original.predicate; simpl.
    repeat split; assumption.
Qed.
