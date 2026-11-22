Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Import ListNotations.
Open Scope string_scope.

Lemma literal_case :
  forall ets p r action_id attrs ty expr,
    WfETS Original.entity_names Original.entity_names ets ->
    WfACT Original.entity_names
      (MkEntityUID (MkName "Action" []) action_id,
       MkActionSchemaEntry [p] [r] attrs) ->
    WfCedarType Original.entity_names ty ->
    HasType (somepaths [])
      (MkEnvironment
        (MkSchema ets
          [(MkEntityUID (MkName "Action" []) action_id,
            MkActionSchemaEntry [p] [r] attrs)])
        (MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs))
      expr ty ->
    Property.candidates.v001.Candidate.predicate
      (Original.mkInput ets
        [(MkEntityUID (MkName "Action" []) action_id,
          MkActionSchemaEntry [p] [r] attrs)]
        [MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs]
        (MkEnvironment
          (MkSchema ets
            [(MkEntityUID (MkName "Action" []) action_id,
              MkActionSchemaEntry [p] [r] attrs)])
          (MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs))
        [] ty expr).
Proof.
  intros ets p r action_id attrs ty expr Hets Hact Hty Hexpr.
  apply Property.candidates.v001.Candidate.PredicateSingle.
  - eapply WfS.
    + exact Hets.
    + apply WfACTSSingle. exact Hact.
    + reflexivity.
  - apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
  - exact Hty.
  - exact Hexpr.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v001.Candidate.predicate x <->
  Property.candidates.v002.Candidate.predicate x.
Proof.
  intro x. split.
  - intro H. apply Property.candidates.v002.Candidate.PredicateGeneral. exact H.
  - intro H. induction H.
    + eapply literal_case; eauto using WfBoolType.
      apply TLitOther.
      * discriminate.
      * apply TTrue.
    + eapply literal_case; eauto using WfBoolType.
      apply TLitFalse. apply TFalse.
    + eapply literal_case; eauto using WfIntType.
      apply TLitOther.
      * discriminate.
      * apply TInt.
    + eapply literal_case; eauto using WfStringType.
      apply TLitOther.
      * discriminate.
      * apply TString.
    + exact H.
Qed.
