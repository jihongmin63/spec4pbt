Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v006.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive BooleanAndTyped : (CedarExpr * PathSet) -> CedarType -> Prop :=
| AndTrueTrue :
    BooleanAndTyped
      (andExpr (lit (boolean true)) (lit (boolean true)), somepaths [])
      (boolType tt_)
| AndTrueFalse :
    BooleanAndTyped
      (andExpr (lit (boolean true)) (lit (boolean false)), allpaths)
      (boolType ff_)
| AndFalseTrue :
    BooleanAndTyped
      (andExpr (lit (boolean false)) (lit (boolean true)), allpaths)
      (boolType ff_)
| AndFalseFalse :
    BooleanAndTyped
      (andExpr (lit (boolean false)) (lit (boolean false)), allpaths)
      (boolType ff_).

Inductive predicate : Original.Input -> Prop :=
| PredicateBooleanAnd : forall p r action_id expr ty,
    DefinedName Original.entity_names p ->
    DefinedName Original.entity_names r ->
    BooleanAndTyped expr ty ->
    predicate
      (Original.mkInput
        [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
         (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
        [(MkEntityUID (MkName "Action" []) action_id,
          MkActionSchemaEntry [p] [r] [])]
        [MkRequest p (MkEntityUID (MkName "Action" []) action_id) r []]
        (MkEnvironment
          (MkSchema
            [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
             (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
            [(MkEntityUID (MkName "Action" []) action_id,
              MkActionSchemaEntry [p] [r] [])])
          (MkRequest p (MkEntityUID (MkName "Action" []) action_id) r []))
        [] ty expr)
| PredicatePredecessor : forall input,
    Property.candidates.v006.Candidate.predicate input ->
    predicate input.
