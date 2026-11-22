Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v002.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive IntTree : CedarExpr -> Prop :=
  | C3IntLiteral : forall n,
      IntTree (lit (int n))
  | C3IntNeg : forall e,
      IntTree e ->
      IntTree (unaryApp neg e)
  | C3IntAdd : forall e1 e2,
      IntTree e1 ->
      IntTree e2 ->
      IntTree (binaryApp add_ e1 e2)
  | C3IntSub : forall e1 e2,
      IntTree e1 ->
      IntTree e2 ->
      IntTree (binaryApp sub_ e1 e2)
  | C3IntMul : forall e1 e2,
      IntTree e1 ->
      IntTree e2 ->
      IntTree (binaryApp mul_ e1 e2)
  | C3IntIfTrue : forall e1 e2,
      IntTree e1 ->
      IntTree e2 ->
      IntTree (ite (lit (boolean true)) e1 e2)
  | C3IntIfFalse : forall e1 e2,
      IntTree e1 ->
      IntTree e2 ->
      IntTree (ite (lit (boolean false)) e1 e2).

Inductive CompositeCase : CedarType -> (CedarExpr * PathSet) -> Prop :=
  | C3Integer : forall e,
      IntTree e ->
      CompositeCase intType (e, somepaths [])
  | C3Less : forall e1 e2,
      IntTree e1 ->
      IntTree e2 ->
      CompositeCase (boolType anyBool)
                    (binaryApp less e1 e2, somepaths [])
  | C3LessEqual : forall e1 e2,
      IntTree e1 ->
      IntTree e2 ->
      CompositeCase (boolType anyBool)
                    (binaryApp lessEq e1 e2, somepaths [])
  | C3Equal : forall e1 e2,
      IntTree e1 ->
      IntTree e2 ->
      CompositeCase (boolType anyBool)
                    (binaryApp equals e1 e2, somepaths [])
  | C3SingletonSet : forall e,
      IntTree e ->
      CompositeCase (setType intType)
                    (setExprCons e setExprNil, somepaths [])
  | C3SingleField : forall field e,
      IntTree e ->
      CompositeCase (recordTypeCons field false intType recordTypeNil)
                    (recExprCons field e recExprNil, somepaths []).

Inductive predicate : Original.Input -> Prop :=
  | C3Inherited : forall i,
      Property.candidates.v002.Candidate.predicate i ->
      predicate i
  | C3Composite : forall (action_id : string) ty expr,
      CompositeCase ty expr ->
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
