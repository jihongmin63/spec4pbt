Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Import ListNotations.
Open Scope string_scope.

Module C2 := Property.candidates.v002.Candidate.
Module C3 := Property.candidates.v003.Candidate.
Module C4 := Property.candidates.v004.Candidate.

Lemma tiny_premises : forall ets acts r,
  C4.TinySchema (MkSchema ets acts) r ->
  WfSchema Original.entity_names (MkSchema ets acts) /\
  ActionSchemaToRequestTypes acts [] [r] /\
  SchemaToEnvironments (MkSchema ets acts) [r]
    [MkEnvironment (MkSchema ets acts) r].
Proof.
  intros ets acts r Htiny.
  inversion Htiny as [id]; subst; clear Htiny.
  repeat split.
  - unfold Original.entity_names.
    eapply WfS with
      (acts := [(MkEntityUID (MkName "Action" []) id,
                 MkActionSchemaEntry [MkName "EntityType1" []]
                   [MkName "EntityType1" []] [])]).
    + eapply WfETSCons.
      * apply DNFound. reflexivity.
      * apply NIECons; [discriminate | apply NIENil].
      * apply WfETSingle; [apply DNSNil | apply WfAttrsNil].
      * apply WfETSSingle.
        -- apply DNRest; [discriminate | apply DNFound; reflexivity].
        -- apply WfETSingle; [apply DNSNil | apply WfAttrsNil].
    + apply WfACTSSingle. apply WfACTSingle.
      * apply DNFound. reflexivity.
      * apply DNFound. reflexivity.
      * apply WfAttrsNil.
    + reflexivity.
  - apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
  - apply MkEnvsSingle.
Qed.

Lemma tiny_previous : forall ets acts r ty expr,
  C4.TinySchema (MkSchema ets acts) r ->
  WfCedarType Original.entity_names ty ->
  HasType (somepaths []) (MkEnvironment (MkSchema ets acts) r) expr ty ->
  C3.predicate (Original.mkInput ets acts [r]
    (MkEnvironment (MkSchema ets acts) r) [] ty expr).
Proof.
  intros ets acts r ty expr Htiny Hty Hexpr.
  destruct (tiny_premises ets acts r Htiny) as [Hs [Hr He]].
  apply C3.PredicatePrevious.
  eapply C2.PredicateEnvironments; eassumption.
Qed.

Theorem equivalent : forall x : Original.Input,
  C3.predicate x <-> C4.predicate x.
Proof.
  intros x. split.
  - intro H. apply C4.PredicatePrevious. exact H.
  - intro H. induction H.
    + eapply tiny_previous; [eassumption | constructor |].
      apply TLitFalse. constructor.
    + eapply tiny_previous; [eassumption | constructor |].
      apply TLitOther; [discriminate | constructor].
    + eapply tiny_previous; [eassumption | constructor |].
      apply TLitOther; [discriminate | constructor].
    + eapply tiny_previous; [eassumption | constructor |].
      apply TLitOther; [discriminate | constructor].
    + eapply tiny_previous; [eassumption | constructor |].
      apply TRecNil.
    + exact H.
Qed.
