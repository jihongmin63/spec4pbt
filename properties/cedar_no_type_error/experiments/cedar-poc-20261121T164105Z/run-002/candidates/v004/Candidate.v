Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v003.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive IntegerExpr : CedarExpr -> Prop :=
| IntegerLiteral : forall n,
    IntegerExpr (lit (int n))
| IntegerNegation : forall e,
    IntegerExpr e ->
    IntegerExpr (unaryApp neg e)
| IntegerAddition : forall e1 e2,
    IntegerExpr e1 ->
    IntegerExpr e2 ->
    IntegerExpr (binaryApp add_ e1 e2)
| IntegerSubtraction : forall e1 e2,
    IntegerExpr e1 ->
    IntegerExpr e2 ->
    IntegerExpr (binaryApp sub_ e1 e2)
| IntegerMultiplication : forall e1 e2,
    IntegerExpr e1 ->
    IntegerExpr e2 ->
    IntegerExpr (binaryApp mul_ e1 e2).

Inductive MoreTyped : (CedarExpr * PathSet) -> CedarType -> Prop :=
| MoreInteger : forall e,
    IntegerExpr e ->
    MoreTyped (e, somepaths []) intType
| MoreLess : forall e1 e2,
    IntegerExpr e1 ->
    IntegerExpr e2 ->
    MoreTyped (binaryApp less e1 e2, somepaths []) (boolType anyBool)
| MoreLessEqual : forall e1 e2,
    IntegerExpr e1 ->
    IntegerExpr e2 ->
    MoreTyped (binaryApp lessEq e1 e2, somepaths []) (boolType anyBool)
| MoreNotLess : forall e1 e2,
    IntegerExpr e1 ->
    IntegerExpr e2 ->
    MoreTyped (unaryApp not_ (binaryApp less e1 e2), somepaths [])
      (boolType anyBool)
| MoreSingleton : forall e,
    IntegerExpr e ->
    MoreTyped (setExprCons e setExprNil, somepaths []) (setType intType)
| MoreIfTrue : forall e1 e2,
    IntegerExpr e1 ->
    IntegerExpr e2 ->
    MoreTyped (ite (lit (boolean true)) e1 e2, somepaths []) intType
| MoreIfFalse : forall e1 e2,
    IntegerExpr e1 ->
    IntegerExpr e2 ->
    MoreTyped (ite (lit (boolean false)) e1 e2, somepaths []) intType
| MoreRecord : forall name e,
    IntegerExpr e ->
    MoreTyped (recExprCons name e recExprNil, somepaths [])
      (recordTypeCons name false intType recordTypeNil)
| MoreLike : forall value pattern,
    MoreTyped (unaryApp (like pattern) (lit (stringLit value)), somepaths [])
      (boolType anyBool).

Inductive predicate : Original.Input -> Prop :=
| PredicateMore :
    forall ets p r action_id attrs expr ty,
      WfETS Original.entity_names Original.entity_names ets ->
      WfACT Original.entity_names
        (MkEntityUID (MkName "Action" []) action_id,
         MkActionSchemaEntry [p] [r] attrs) ->
      WfCedarType Original.entity_names ty ->
      MoreTyped expr ty ->
      predicate
        (Original.mkInput ets
          [(MkEntityUID (MkName "Action" []) action_id,
            MkActionSchemaEntry [p] [r] attrs)]
          [MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs]
          (MkEnvironment
            (MkSchema ets
              [(MkEntityUID (MkName "Action" []) action_id,
                MkActionSchemaEntry [p] [r] attrs)])
            (MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs))
          [] ty expr)
| PredicatePredecessor : forall input,
    Property.candidates.v003.Candidate.predicate input ->
    predicate input.
