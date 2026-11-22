Require Import List String Specification.cedar.Spec Property.Original.
Require Import Property.candidates.v002.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive SimpleExpr : CedarType -> (CedarExpr * PathSet) -> Prop :=
  | SimpleInt : forall n,
      SimpleExpr intType (lit (int n), somepaths [])
  | SimpleString : forall s,
      SimpleExpr stringType (lit (stringLit s), somepaths [])
  | SimpleTrue :
      SimpleExpr (boolType tt_) (lit (boolean true), somepaths [])
  | SimpleFalse :
      SimpleExpr (boolType ff_) (lit (boolean false), allpaths)
  | SimpleRecordNil :
      SimpleExpr recordTypeNil (recExprNil, somepaths [])
  | SimpleNeg : forall e,
      SimpleExpr intType (e, somepaths []) ->
      SimpleExpr intType (unaryApp neg e, somepaths [])
  | SimpleAdd : forall e1 e2,
      SimpleExpr intType (e1, somepaths []) ->
      SimpleExpr intType (e2, somepaths []) ->
      SimpleExpr intType (binaryApp add_ e1 e2, somepaths [])
  | SimpleLess : forall e1 e2,
      SimpleExpr intType (e1, somepaths []) ->
      SimpleExpr intType (e2, somepaths []) ->
      SimpleExpr (boolType anyBool) (binaryApp less e1 e2, somepaths []).

Inductive predicate : Original.Input -> Prop :=
  | PredicatePrevious : forall i,
      Property.candidates.v002.Candidate.predicate i ->
      predicate i
  | PredicateCanonical : forall aid ty expr,
      SimpleExpr ty expr ->
      predicate (Original.mkInput
        [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
         (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
        [(MkEntityUID (MkName "Action" []) aid,
          MkActionSchemaEntry
            [MkName "EntityType1" []]
            [MkName "EntityType2" []] [])]
        [MkRequest (MkName "EntityType1" [])
          (MkEntityUID (MkName "Action" []) aid)
          (MkName "EntityType2" []) []]
        (MkEnvironment
          (MkSchema
            [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
             (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
            [(MkEntityUID (MkName "Action" []) aid,
              MkActionSchemaEntry
                [MkName "EntityType1" []]
                [MkName "EntityType2" []] [])])
          (MkRequest (MkName "EntityType1" [])
            (MkEntityUID (MkName "Action" []) aid)
            (MkName "EntityType2" []) []))
        [] ty expr)
  | PredicateCanonicalInt : forall aid n,
      predicate (Original.mkInput
        [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
         (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
        [(MkEntityUID (MkName "Action" []) aid,
          MkActionSchemaEntry
            [MkName "EntityType1" []]
            [MkName "EntityType2" []] [])]
        [MkRequest (MkName "EntityType1" [])
          (MkEntityUID (MkName "Action" []) aid)
          (MkName "EntityType2" []) []]
        (MkEnvironment
          (MkSchema
            [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
             (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
            [(MkEntityUID (MkName "Action" []) aid,
              MkActionSchemaEntry
                [MkName "EntityType1" []]
                [MkName "EntityType2" []] [])])
          (MkRequest (MkName "EntityType1" [])
            (MkEntityUID (MkName "Action" []) aid)
            (MkName "EntityType2" []) []))
        [] intType (lit (int n), somepaths [])).
