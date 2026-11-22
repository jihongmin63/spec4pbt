Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Require Import Property.candidates.v006.Candidate.
Require Import Property.candidates.v007.Candidate.
Import ListNotations.
Open Scope string_scope.

Module C2 := Property.candidates.v002.Candidate.
Module C3 := Property.candidates.v003.Candidate.
Module C4 := Property.candidates.v004.Candidate.
Module C5 := Property.candidates.v005.Candidate.
Module C6 := Property.candidates.v006.Candidate.
Module C7 := Property.candidates.v007.Candidate.

Lemma tiny_schema_wf : forall ets acts r,
  C4.TinySchema (MkSchema ets acts) r ->
  WfSchema Original.entity_names (MkSchema ets acts).
Proof.
  intros ets acts r H. inversion H; subst; clear H.
  unfold Original.entity_names.
  eapply WfS.
  - eapply WfETSCons.
    + apply DNFound. reflexivity.
    + apply NIECons; [congruence | apply NIENil].
    + constructor; constructor; constructor.
    + eapply WfETSSingle.
      * apply DNRest; [congruence | apply DNFound; reflexivity].
      * constructor; constructor; constructor.
  - apply WfACTSSingle. apply WfACTSingle.
    + apply DNFound. reflexivity.
    + apply DNFound. reflexivity.
    + constructor.
  - reflexivity.
Qed.

Lemma tiny_schema_requests : forall ets acts r,
  C4.TinySchema (MkSchema ets acts) r ->
  ActionSchemaToRequestTypes acts [] [r].
Proof.
  intros ets acts r H. inversion H; subst; clear H.
  apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
Qed.

Lemma tiny_int_has_type : forall e,
  C5.TinyIntExpr e ->
  forall env, HasType (somepaths []) env (e, somepaths []) intType.
Proof.
  intros e H. induction H; intro env.
  - eapply TLitOther; [discriminate | constructor].
  - eapply TNeg; eauto.
  - eapply TAdd; eauto.
  - eapply TSub; eauto.
  - eapply TMul; eauto.
Qed.

Lemma tiny_int_set_has_type : forall e,
  C7.TinyIntSetExpr e ->
  forall env, HasType (somepaths []) env (e, somepaths []) (setType intType).
Proof.
  intros e H. induction H; intro env.
  - eapply TSetSingle. apply tiny_int_has_type. assumption.
  - eapply TSetMany; eauto using tiny_int_has_type.
Qed.

Lemma tiny_int_set_previous : forall ets acts r e,
  C4.TinySchema (MkSchema ets acts) r ->
  C7.TinyIntSetExpr e ->
  C6.predicate (Original.mkInput ets acts [r]
    (MkEnvironment (MkSchema ets acts) r) []
    (setType intType) (e, somepaths [])).
Proof.
  intros ets acts r e Hschema Hset.
  apply C6.PredicatePrevious.
  apply C5.PredicatePrevious.
  apply C4.PredicatePrevious.
  apply C3.PredicatePrevious.
  eapply C2.PredicateEnvironments.
  - apply tiny_schema_wf with (r := r). exact Hschema.
  - exact (tiny_schema_requests ets acts r Hschema).
  - apply MkEnvsSingle.
  - apply WfSetType. apply WfIntType.
  - apply tiny_int_set_has_type. exact Hset.
Qed.

Theorem equivalent : forall x : Original.Input,
  C6.predicate x <-> C7.predicate x.
Proof.
  intro x. split.
  - apply C7.PredicatePrevious.
  - intro H. inversion H; subst.
    + eapply tiny_int_set_previous; eassumption.
    + assumption.
Qed.
