Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v002.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive SimpleTyped : CedarType -> (CedarExpr * PathSet) -> Prop :=
  | TrueLiteral : SimpleTyped (boolType tt_) (lit (boolean true), somepaths [])
  | StringLiteral : forall s : string,
      SimpleTyped stringType (lit (stringLit s), somepaths [])
  | IntLiteral : forall n : BinNums.Z,
      SimpleTyped intType (lit (int n), somepaths [])
  | EmptyRecord : SimpleTyped recordTypeNil (recExprNil, somepaths [])
  | PrincipalVariable :
      SimpleTyped (entityType (MkName "EntityType1" []))
        (var principal, somepaths [])
  | ResourceVariable :
      SimpleTyped (entityType (MkName "EntityType2" []))
        (var resource, somepaths []).

Inductive predicate : Original.Input -> Prop :=
  | Simple : forall (id : string) ty expr,
      SimpleTyped ty expr ->
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
      Property.candidates.v002.Candidate.predicate i ->
      predicate i.
