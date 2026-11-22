Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v004.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive LiteralComparison : Environment -> (CedarExpr * PathSet) -> BoolType -> Prop :=
| ComparisonSame : forall env value value_type,
    HasTypePrim env value value_type ->
    LiteralComparison env
      (binaryApp equals (lit value) (lit value), somepaths []) tt_
| ComparisonTrueFalse : forall env,
    LiteralComparison env
      (binaryApp equals (lit (boolean true)) (lit (boolean false)), allpaths) ff_
| ComparisonFalseTrue : forall env,
    LiteralComparison env
      (binaryApp equals (lit (boolean false)) (lit (boolean true)), allpaths) ff_
| ComparisonBoolInt : forall env b n,
    LiteralComparison env
      (binaryApp equals (lit (boolean b)) (lit (int n)), allpaths) ff_
| ComparisonIntBool : forall env n b,
    LiteralComparison env
      (binaryApp equals (lit (int n)) (lit (boolean b)), allpaths) ff_
| ComparisonBoolString : forall env b s,
    LiteralComparison env
      (binaryApp equals (lit (boolean b)) (lit (stringLit s)), allpaths) ff_
| ComparisonStringBool : forall env s b,
    LiteralComparison env
      (binaryApp equals (lit (stringLit s)) (lit (boolean b)), allpaths) ff_
| ComparisonIntString : forall env n s,
    LiteralComparison env
      (binaryApp equals (lit (int n)) (lit (stringLit s)), allpaths) ff_
| ComparisonStringInt : forall env s n,
    LiteralComparison env
      (binaryApp equals (lit (stringLit s)) (lit (int n)), allpaths) ff_.

Inductive predicate : Original.Input -> Prop :=
| PredicateLiteralComparison :
    forall ets p r action_id attrs expr result,
      WfETS Original.entity_names Original.entity_names ets ->
      WfACT Original.entity_names
        (MkEntityUID (MkName "Action" []) action_id,
         MkActionSchemaEntry [p] [r] attrs) ->
      LiteralComparison
        (MkEnvironment
          (MkSchema ets
            [(MkEntityUID (MkName "Action" []) action_id,
              MkActionSchemaEntry [p] [r] attrs)])
          (MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs))
        expr result ->
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
          [] (boolType result) expr)
| PredicatePredecessor : forall input,
    Property.candidates.v004.Candidate.predicate input ->
    predicate input.
