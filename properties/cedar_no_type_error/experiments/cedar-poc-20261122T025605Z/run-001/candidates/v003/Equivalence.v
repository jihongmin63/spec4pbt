Require Import List String Specification.cedar.Spec Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Require Import Property.candidates.v003.Candidate.
Import ListNotations.
Open Scope string_scope.

Definition canonical_ets : list (EntityName * EntitySchemaEntry) :=
  [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
   (MkName "EntityType2" [], MkEntitySchemaEntry [] [])].

Definition canonical_acts (aid : string) : list (EntityUID * ActionSchemaEntry) :=
  [(MkEntityUID (MkName "Action" []) aid,
    MkActionSchemaEntry [MkName "EntityType1" []]
                        [MkName "EntityType2" []] [])].

Definition canonical_request (aid : string) : RequestType :=
  MkRequest (MkName "EntityType1" [])
    (MkEntityUID (MkName "Action" []) aid)
    (MkName "EntityType2" []) [].

Definition canonical_input (aid : string) (ty : CedarType)
    (expr : CedarExpr * PathSet) : Original.Input :=
  Original.mkInput canonical_ets (canonical_acts aid)
    [canonical_request aid]
    (MkEnvironment (MkSchema canonical_ets (canonical_acts aid))
                   (canonical_request aid)) [] ty expr.

Lemma canonical_ets_wf :
  WfETS Original.entity_names Original.entity_names canonical_ets.
Proof.
  unfold Original.entity_names, canonical_ets.
  eapply WfETSCons.
  - apply DNFound. reflexivity.
  - apply NIECons. discriminate. apply NIENil.
  - apply WfETSingle; constructor.
  - apply WfETSSingle.
    + apply DNRest. discriminate. apply DNFound. reflexivity.
    + apply WfETSingle; constructor.
Qed.

Lemma canonical_acts_wf : forall aid,
  WfACTS Original.entity_names (canonical_acts aid).
Proof.
  intro aid.
  unfold Original.entity_names, canonical_acts.
  apply WfACTSSingle. apply WfACTSingle.
  - apply DNFound. reflexivity.
  - apply DNRest. discriminate. apply DNFound. reflexivity.
  - apply WfAttrsNil.
Qed.

Lemma canonical_schema_wf : forall aid,
  WfSchema Original.entity_names
    (MkSchema canonical_ets (canonical_acts aid)).
Proof.
  intro aid.
  eapply WfS with (acts := canonical_acts aid).
  - apply canonical_ets_wf.
  - apply canonical_acts_wf.
  - reflexivity.
Qed.

Lemma canonical_requests : forall aid,
  ActionSchemaToRequestTypes (canonical_acts aid) []
    [canonical_request aid].
Proof.
  intro aid.
  unfold canonical_acts, canonical_request.
  apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
Qed.

Lemma simple_wf_type : forall ty expr,
  Property.candidates.v003.Candidate.SimpleExpr ty expr ->
  WfCedarType Original.entity_names ty.
Proof.
  intros ty expr H. destruct H; constructor.
Qed.

Lemma simple_has_type : forall V ty expr,
  Property.candidates.v003.Candidate.SimpleExpr ty expr ->
  HasType (somepaths []) V expr ty.
Proof.
  intros V ty expr H. induction H.
  - apply TLitOther. discriminate. apply TInt.
  - apply TLitOther. discriminate. apply TString.
  - apply TLitOther. discriminate. apply TTrue.
  - apply TLitFalse. apply TFalse.
  - apply TRecNil.
  - eapply TNeg. exact IHSimpleExpr.
  - eapply TAdd; eassumption.
  - eapply TLessThan; eassumption.
Qed.

Lemma canonical_in_previous : forall aid ty expr,
  Property.candidates.v003.Candidate.SimpleExpr ty expr ->
  Property.candidates.v002.Candidate.predicate
    (canonical_input aid ty expr).
Proof.
  intros aid ty expr H.
  unfold canonical_input.
  apply Property.candidates.v002.Candidate.PredicatePrevious.
  apply Property.candidates.v001.Candidate.PredicateSingle.
  - apply canonical_schema_wf.
  - apply canonical_requests.
  - eapply simple_wf_type. exact H.
  - eapply simple_has_type. exact H.
Qed.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v002.Candidate.predicate x <->
  Property.candidates.v003.Candidate.predicate x.
Proof.
  intro x. split.
  - intro H. apply Property.candidates.v003.Candidate.PredicatePrevious.
    exact H.
  - intro H. destruct H as [i Hi | aid ty expr Hsimple | aid n].
    + exact Hi.
    + change (Property.candidates.v002.Candidate.predicate
                (canonical_input aid ty expr)).
      apply canonical_in_previous. exact Hsimple.
    + change (Property.candidates.v002.Candidate.predicate
                (canonical_input aid intType
                  (lit (int n), somepaths []))).
      apply canonical_in_previous. apply Property.candidates.v003.Candidate.SimpleInt.
Qed.
