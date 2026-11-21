(** The generation premises and test claim of prop_no_type_error.
    This file states the implementation claim; it does not prove that claim.
    See README.md and the byte-preserved upstream source. *)
Require Import String List.
Require Import Specification.cedar.Spec.
Import ListNotations.
Open Scope string_scope.

Definition entity_names : list EntityName :=
  [MkName "EntityType1" []; MkName "EntityType2" []].

(** Keep every quantified value of the artifact, including its witnesses. *)
Record Input : Type := mkInput {
  ets : list (EntityName * EntitySchemaEntry);
  acts : list (EntityUID * ActionSchemaEntry);
  rs : list RequestType;
  e : Environment;
  es : list Environment;
  ty : CedarType;
  expr : CedarExpr * PathSet
}.

Definition predicate (i : Input) : Prop :=
  WfSchema entity_names (MkSchema (ets i) (acts i)) /\
  ActionSchemaToRequestTypes (acts i) [] (rs i) /\
  SchemaToEnvironments (MkSchema (ets i) (acts i)) (rs i) (e i :: es i) /\
  WfCedarType entity_names (ty i) /\
  HasType (somepaths []) (e i) (expr i) (ty i).

(** Explicit argument for the external checker, not an assumed implementation.
    An adapter must reproduce upstream's serialization and response handling. *)
Definition Checker : Type := Schema -> Environment -> (CedarExpr * PathSet) -> bool.

Definition conclusion (check : Checker) (i : Input) : Prop :=
  check (MkSchema (ets i) (acts i)) (e i) (expr i) = true.

Definition property (check : Checker) : Prop :=
  forall i : Input, predicate i -> conclusion check i.

(** The artifact's statement, with its external function made an argument. *)
Definition prop_no_type_error (no_type_error_with_env : Checker) : Prop :=
  forall ets acts rs e es ty expr,
    WfSchema [MkName "EntityType1" []; MkName "EntityType2" []] (MkSchema ets acts) ->
    ActionSchemaToRequestTypes acts [] rs ->
    SchemaToEnvironments (MkSchema ets acts) rs (cons e es) ->
    WfCedarType [MkName "EntityType1" []; MkName "EntityType2" []] ty ->
    HasType (somepaths []) e expr ty ->
    no_type_error_with_env (MkSchema ets acts) e expr = true.

(** Packaging equivalence only; no assertion that the external checker passes. *)
Theorem property_matches_artifact : forall check,
  property check <-> prop_no_type_error check.
Proof.
  intro check. split.
  - intros H ets0 acts0 rs0 e0 es0 ty0 expr0 Hs Hr He Ht Hexpr.
    apply (H (mkInput ets0 acts0 rs0 e0 es0 ty0 expr0)).
    unfold predicate; simpl. repeat split; assumption.
  - intros H [ets0 acts0 rs0 e0 es0 ty0 expr0] Hp.
    unfold predicate in Hp; simpl in Hp.
    destruct Hp as [Hs [Hr [He [Ht Hexpr]]]].
    unfold conclusion; simpl. eapply H; eassumption.
Qed.
