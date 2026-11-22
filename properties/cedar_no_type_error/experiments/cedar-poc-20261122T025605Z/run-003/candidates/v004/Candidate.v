Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v003.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive GroundInt : CedarExpr -> Prop :=
  | IntegerLiteral : forall n : BinNums.Z,
      GroundInt (lit (int n))
  | IntegerNegation : forall e,
      GroundInt e ->
      GroundInt (unaryApp neg e)
  | IntegerAddition : forall e1 e2,
      GroundInt e1 ->
      GroundInt e2 ->
      GroundInt (binaryApp add_ e1 e2)
  | IntegerSubtraction : forall e1 e2,
      GroundInt e1 ->
      GroundInt e2 ->
      GroundInt (binaryApp sub_ e1 e2)
  | IntegerMultiplication : forall e1 e2,
      GroundInt e1 ->
      GroundInt e2 ->
      GroundInt (binaryApp mul_ e1 e2).

Inductive GroundTyped : CedarType -> (CedarExpr * PathSet) -> Prop :=
  | IntegerExpression : forall e,
      GroundInt e ->
      GroundTyped intType (e, somepaths [])
  | IntegerLess : forall e1 e2,
      GroundInt e1 ->
      GroundInt e2 ->
      GroundTyped (boolType anyBool)
        (binaryApp less e1 e2, somepaths [])
  | IntegerLessEqual : forall e1 e2,
      GroundInt e1 ->
      GroundInt e2 ->
      GroundTyped (boolType anyBool)
        (binaryApp lessEq e1 e2, somepaths [])
  | IntegerSingleton : forall e,
      GroundInt e ->
      GroundTyped (setType intType)
        (setExprCons e setExprNil, somepaths [])
  | IntegerField : forall field e,
      GroundInt e ->
      GroundTyped (recordTypeCons field false intType recordTypeNil)
        (recExprCons field e recExprNil, somepaths [])
  | IntegerSelfEquality : forall n : BinNums.Z,
      GroundTyped (boolType tt_)
        (binaryApp equals (lit (int n)) (lit (int n)), somepaths [])
  | FalseLiteral :
      GroundTyped (boolType ff_) (lit (boolean false), allpaths)
  | NotTrue :
      GroundTyped (boolType ff_)
        (unaryApp not_ (lit (boolean true)), allpaths)
  | NotFalse :
      GroundTyped (boolType tt_)
        (unaryApp not_ (lit (boolean false)), somepaths []).

Inductive predicate : Original.Input -> Prop :=
  | Ground : forall (id : string) ty expr,
      GroundTyped ty expr ->
      predicate
        (Original.mkInput
          [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
           (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
          [(MkEntityUID (MkName "Action" []) id,
            MkActionSchemaEntry
              [MkName "EntityType1" []] [MkName "EntityType2" []] [])]
          [MkRequest
            (MkName "EntityType1" [])
            (MkEntityUID (MkName "Action" []) id)
            (MkName "EntityType2" []) []]
          (MkEnvironment
            (MkSchema
              [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
               (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
              [(MkEntityUID (MkName "Action" []) id,
                MkActionSchemaEntry
                  [MkName "EntityType1" []] [MkName "EntityType2" []] [])])
            (MkRequest
              (MkName "EntityType1" [])
              (MkEntityUID (MkName "Action" []) id)
              (MkName "EntityType2" []) []))
          [] ty expr)
  | General : forall i,
      Property.candidates.v003.Candidate.predicate i ->
      predicate i.
