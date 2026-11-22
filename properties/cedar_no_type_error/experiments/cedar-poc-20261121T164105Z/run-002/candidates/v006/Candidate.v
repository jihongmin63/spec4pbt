Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v005.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive RecordFieldTyped : (CedarExpr * PathSet) -> CedarType -> Prop :=
| RecordFieldGet : forall field e,
    Property.candidates.v004.Candidate.IntegerExpr e ->
    RecordFieldTyped
      (getAttr (recExprCons field e recExprNil) field, somepaths [])
      intType
| RecordFieldHas : forall field e,
    Property.candidates.v004.Candidate.IntegerExpr e ->
    RecordFieldTyped
      (hasAttr (recExprCons field e recExprNil) field,
       somepaths [getAttr (recExprCons field e recExprNil) field])
      (boolType tt_).

Inductive predicate : Original.Input -> Prop :=
| PredicateRecordField : forall p r action_id expr ty,
    DefinedName Original.entity_names p ->
    DefinedName Original.entity_names r ->
    RecordFieldTyped expr ty ->
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
    Property.candidates.v005.Candidate.predicate input ->
    predicate input.
