Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Import ListNotations.

Module C1 := Property.candidates.v001.Candidate.
Module C2 := Property.candidates.v002.Candidate.
Module C3 := Property.candidates.v003.Candidate.
Module C4 := Property.candidates.v004.Candidate.

Lemma integer_wf : forall e, C4.IntegerExpr e -> WfExprSyntax e.
Proof.
  intros e H; induction H; constructor; auto.
Qed.

Lemma integer_has_type : forall a V e,
  C4.IntegerExpr e -> HasType a V (e, somepaths []) intType.
Proof.
  intros a V e H; induction H.
  - apply TLitOther; [discriminate | constructor].
  - eapply TNeg; eassumption.
  - eapply TAdd; eassumption.
  - eapply TSub; eassumption.
  - eapply TMul; eassumption.
Qed.

Lemma more_has_type : forall V expr ty,
  C4.MoreTyped expr ty -> HasType (somepaths []) V expr ty.
Proof.
  intros V expr ty H; induction H.
  - apply integer_has_type; assumption.
  - eapply TLessThan; apply integer_has_type; eassumption.
  - eapply TLessEqualThan; apply integer_has_type; eassumption.
  - eapply TNotAny. eapply TLessThan;
      apply integer_has_type; eassumption.
  - eapply TSetSingle. apply integer_has_type; assumption.
  - eapply TCondTrue.
    + apply integer_has_type; assumption.
    + apply integer_wf; assumption.
  - eapply TCondFalse.
    + apply integer_wf; assumption.
    + apply integer_has_type; assumption.
  - eapply TRecCons.
    + apply integer_has_type; assumption.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
  - eapply TLike. apply TLitOther; [discriminate | constructor].
Qed.

Theorem equivalent : forall x : Original.Input,
  C3.predicate x <-> C4.predicate x.
Proof.
  intro x; split; intro H.
  - apply C4.PredicatePredecessor; assumption.
  - destruct H as [ets p r action_id attrs expr ty Hets Hact Hwf Hmore
                  | input Hpred].
    + apply C3.PredicatePredecessor.
      apply C2.PredicateGeneral.
      eapply C1.PredicateSingle.
      * eapply WfS.
        -- exact Hets.
        -- constructor; exact Hact.
        -- reflexivity.
      * apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
      * exact Hwf.
      * apply more_has_type; exact Hmore.
    + exact Hpred.
Qed.
