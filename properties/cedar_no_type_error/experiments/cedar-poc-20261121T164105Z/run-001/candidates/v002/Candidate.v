Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive SimpleCase : CedarType -> (CedarExpr * PathSet) -> Prop :=
  | IntegerLiteral : forall n,
      SimpleCase intType (lit (int n), somepaths [])
  | StringLiteral : forall s,
      SimpleCase stringType (lit (stringLit s), somepaths [])
  | PrincipalVariable :
      SimpleCase (entityType (MkName "EntityType1" []))
                 (var principal, somepaths [])
  | ResourceVariable :
      SimpleCase (entityType (MkName "EntityType1" []))
                 (var resource, somepaths [])
  | ContextVariable :
      SimpleCase recordTypeNil (var context, somepaths [])
  | NotTrue :
      SimpleCase (boolType ff_)
                 (unaryApp not_ (lit (boolean true)), allpaths)
  | NotFalse :
      SimpleCase (boolType tt_)
                 (unaryApp not_ (lit (boolean false)), somepaths [])
  | NegatedInteger : forall n,
      SimpleCase intType
                 (unaryApp neg (lit (int n)), somepaths [])
  | StringPattern : forall s,
      SimpleCase (boolType anyBool)
                 (unaryApp (like []) (lit (stringLit s)), somepaths [])
  | IntegerAddition : forall n m,
      SimpleCase intType
                 (binaryApp add_ (lit (int n)) (lit (int m)), somepaths [])
  | IntegerSubtraction : forall n m,
      SimpleCase intType
                 (binaryApp sub_ (lit (int n)) (lit (int m)), somepaths [])
  | IntegerMultiplication : forall n m,
      SimpleCase intType
                 (binaryApp mul_ (lit (int n)) (lit (int m)), somepaths [])
  | IntegerLess : forall n m,
      SimpleCase (boolType anyBool)
                 (binaryApp less (lit (int n)) (lit (int m)), somepaths [])
  | IntegerLessEqual : forall n m,
      SimpleCase (boolType anyBool)
                 (binaryApp lessEq (lit (int n)) (lit (int m)), somepaths [])
  | IntegerEqualSelf : forall n,
      SimpleCase (boolType tt_)
                 (binaryApp equals (lit (int n)) (lit (int n)), somepaths [])
  | SingletonIntegerSet : forall n,
      SimpleCase (setType intType)
                 (setExprCons (lit (int n)) setExprNil, somepaths [])
  | SingleIntegerField : forall field n,
      SimpleCase (recordTypeCons field false intType recordTypeNil)
                 (recExprCons field (lit (int n)) recExprNil, somepaths [])
  | TrueConditionalInteger : forall n m,
      SimpleCase intType
                 (ite (lit (boolean true)) (lit (int n)) (lit (int m)),
                  somepaths [])
  | FalseConditionalInteger : forall n m,
      SimpleCase intType
                 (ite (lit (boolean false)) (lit (int n)) (lit (int m)),
                  somepaths []).

Inductive predicate : Original.Input -> Prop :=
  | Inherited : forall i,
      Property.candidates.v001.Candidate.predicate i ->
      predicate i
  | Simple : forall (action_id : string) ty expr,
      SimpleCase ty expr ->
      predicate
        (Original.mkInput
          [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
           (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
          [(MkEntityUID (MkName "Action" []) action_id,
            MkActionSchemaEntry [MkName "EntityType1" []]
                                [MkName "EntityType1" []] [])]
          [MkRequest (MkName "EntityType1" [])
                     (MkEntityUID (MkName "Action" []) action_id)
                     (MkName "EntityType1" []) []]
          (MkEnvironment
            (MkSchema
              [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
               (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
              [(MkEntityUID (MkName "Action" []) action_id,
                MkActionSchemaEntry [MkName "EntityType1" []]
                                    [MkName "EntityType1" []] [])])
            (MkRequest (MkName "EntityType1" [])
                       (MkEntityUID (MkName "Action" []) action_id)
                       (MkName "EntityType1" []) []))
          [] ty expr).
