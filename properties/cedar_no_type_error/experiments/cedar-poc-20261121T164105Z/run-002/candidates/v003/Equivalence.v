Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Import ListNotations.

Lemma simple_typed_has_type :
  forall env expr ty,
    Property.candidates.v003.Candidate.SimpleTyped env expr ty ->
    HasType (somepaths []) env expr ty.
Proof.
  intros env expr ty H.
  destruct H.
  - apply TRecNil.
  - apply TVar. apply TPrincipal.
  - apply TVar. apply TResource.
  - apply TVar. apply TContext. assumption.
  - eapply TNotTrue. apply TLitOther; [discriminate | apply TTrue].
  - eapply TNotFalse. apply TLitFalse. apply TFalse.
  - eapply TNeg. apply TLitOther; [discriminate | apply TInt].
  - eapply TAdd; (apply TLitOther; [discriminate | apply TInt]).
  - eapply TLessThan; (apply TLitOther; [discriminate | apply TInt]).
  - eapply TEqLitTrue. apply TInt.
  - eapply TSetSingle. apply TLitOther; [discriminate | apply TInt].
  - eapply TCondTrue.
    + apply TLitOther; [discriminate | apply TInt].
    + apply WFSPrim.
Qed.

Lemma simple_implies_predecessor :
  forall ets p r action_id attrs expr ty,
    WfETS Original.entity_names Original.entity_names ets ->
    WfACT Original.entity_names
      (MkEntityUID (MkName "Action" []) action_id,
       MkActionSchemaEntry [p] [r] attrs) ->
    WfCedarType Original.entity_names ty ->
    Property.candidates.v003.Candidate.SimpleTyped
      (MkEnvironment
        (MkSchema ets
          [(MkEntityUID (MkName "Action" []) action_id,
            MkActionSchemaEntry [p] [r] attrs)])
        (MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs))
      expr ty ->
    Property.candidates.v002.Candidate.predicate
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
  intros ets p r action_id attrs expr ty Hets Hact Hty Hsimple.
  apply Property.candidates.v002.Candidate.PredicateGeneral.
  apply Property.candidates.v001.Candidate.PredicateSingle.
  - eapply WfS.
    + exact Hets.
    + apply WfACTSSingle. exact Hact.
    + reflexivity.
  - apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
  - exact Hty.
  - apply simple_typed_has_type. exact Hsimple.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v002.Candidate.predicate x <->
  Property.candidates.v003.Candidate.predicate x.
Proof.
  intro x. split.
  - apply Property.candidates.v003.Candidate.PredicatePredecessor.
  - intro H. destruct H.
    + eapply simple_implies_predecessor; eassumption.
    + assumption.
Qed.
