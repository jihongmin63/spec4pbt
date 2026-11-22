Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Import ListNotations.

Lemma boolean_prim_typed : forall env b,
  exists ty, HasTypePrim env (boolean b) ty.
Proof.
  intros env b; destruct b.
  - exists (boolType tt_). apply TTrue.
  - exists (boolType ff_). apply TFalse.
Qed.

Lemma literal_comparison_typed :
  forall env expr result,
    Property.candidates.v005.Candidate.LiteralComparison env expr result ->
    HasType (somepaths []) env expr (boolType result).
Proof.
  intros env expr result H.
  destruct H.
  - eapply TEqLitTrue; eassumption.
  - eapply TEqLitFalse; [apply TTrue | apply TFalse | discriminate].
  - eapply TEqLitFalse; [apply TFalse | apply TTrue | discriminate].
  - destruct (boolean_prim_typed env b) as [ty Hty].
    eapply TEqLitFalse; [exact Hty | apply TInt | discriminate].
  - destruct (boolean_prim_typed env b) as [ty Hty].
    eapply TEqLitFalse; [apply TInt | exact Hty | discriminate].
  - destruct (boolean_prim_typed env b) as [ty Hty].
    eapply TEqLitFalse; [exact Hty | apply TString | discriminate].
  - destruct (boolean_prim_typed env b) as [ty Hty].
    eapply TEqLitFalse; [apply TString | exact Hty | discriminate].
  - eapply TEqLitFalse; [apply TInt | apply TString | discriminate].
  - eapply TEqLitFalse; [apply TString | apply TInt | discriminate].
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v004.Candidate.predicate x <->
  Property.candidates.v005.Candidate.predicate x.
Proof.
  intro x; split.
  - intro H.
    apply Property.candidates.v005.Candidate.PredicatePredecessor.
    exact H.
  - intro H.
    destruct H as [ets p r action_id attrs expr result Hets Hact Hcmp
                  | input Hprev].
    + apply Property.candidates.v004.Candidate.PredicatePredecessor.
      apply Property.candidates.v003.Candidate.PredicatePredecessor.
      apply Property.candidates.v002.Candidate.PredicateGeneral.
      apply Property.candidates.v001.Candidate.PredicateSingle.
      * eapply WfS with
          (acts := [(MkEntityUID (MkName "Action" []) action_id,
                     MkActionSchemaEntry [p] [r] attrs)]).
        -- exact Hets.
        -- apply WfACTSSingle. exact Hact.
        -- reflexivity.
      * apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
      * apply WfBoolType.
      * apply literal_comparison_typed. exact Hcmp.
    + exact Hprev.
Qed.
