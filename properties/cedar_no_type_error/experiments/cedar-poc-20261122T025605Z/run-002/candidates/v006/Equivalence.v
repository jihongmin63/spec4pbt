Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Require Import Property.candidates.v006.Candidate.
Import ListNotations.

Lemma tiny_int_has_type : forall a V e,
  Property.candidates.v005.Candidate.TinyIntExpr e ->
  HasType a V (e, somepaths []) intType.
Proof.
  intros a V e H.
  induction H.
  - apply TLitOther. discriminate. constructor.
  - eapply TNeg; eauto.
  - eapply TAdd; eauto.
  - eapply TSub; eauto.
  - eapply TMul; eauto.
Qed.

Lemma tiny_bool_has_type : forall a V e,
  Property.candidates.v006.Candidate.TinyBoolExpr e ->
  HasType a V (e, somepaths []) (boolType anyBool).
Proof.
  intros a V e H.
  induction H.
  - eapply TLessThan; apply tiny_int_has_type; eassumption.
  - eapply TLessEqualThan; apply tiny_int_has_type; eassumption.
  - eapply TNotAny; eauto.
Qed.

Lemma tiny_schema_wf : forall ets acts r,
  Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
  WfSchema Original.entity_names (MkSchema ets acts).
Proof.
  intros ets acts r H.
  inversion H; subst.
  eapply WfS.
  - eapply WfETSCons.
    + apply DNFound. reflexivity.
    + constructor; [discriminate | constructor].
    + constructor; constructor.
    + eapply WfETSSingle.
      * eapply DNRest. discriminate. apply DNFound. reflexivity.
      * constructor; constructor.
  - apply WfACTSSingle. apply WfACTSingle.
    + apply DNFound. reflexivity.
    + apply DNFound. reflexivity.
    + constructor.
  - reflexivity.
Qed.

Lemma tiny_schema_requests : forall ets acts r,
  Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
  ActionSchemaToRequestTypes acts [] [r].
Proof.
  intros ets acts r H.
  inversion H; subst.
  apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
Qed.

Lemma tiny_bool_previous : forall ets acts r e,
  Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
  Property.candidates.v006.Candidate.TinyBoolExpr e ->
  Property.candidates.v005.Candidate.predicate
    (Original.mkInput ets acts [r]
      (MkEnvironment (MkSchema ets acts) r) []
      (boolType anyBool) (e, somepaths [])).
Proof.
  intros ets acts r e Hschema Hexpr.
  apply Property.candidates.v005.Candidate.PredicatePrevious.
  apply Property.candidates.v004.Candidate.PredicatePrevious.
  apply Property.candidates.v003.Candidate.PredicatePrevious.
  eapply Property.candidates.v002.Candidate.PredicateEnvironments.
  - apply tiny_schema_wf with (r := r). exact Hschema.
  - apply tiny_schema_requests with (ets := ets). exact Hschema.
  - apply MkEnvsSingle.
  - apply WfBoolType.
  - apply tiny_bool_has_type. exact Hexpr.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v005.Candidate.predicate x <->
  Property.candidates.v006.Candidate.predicate x.
Proof.
  intro x. split; intro H.
  - apply Property.candidates.v006.Candidate.PredicatePrevious. exact H.
  - destruct H as [ets acts r e Hschema Hexpr | i Hprev].
    + eapply tiny_bool_previous; eassumption.
    + exact Hprev.
Qed.
