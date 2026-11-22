Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v006.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive C7IntTree : CedarExpr -> Prop :=
  | C7IntBase : forall e,
      Property.candidates.v003.Candidate.IntTree e ->
      C7IntTree e
  | C7IntNeg : forall e,
      C7IntTree e ->
      C7IntTree (unaryApp neg e)
  | C7IntAdd : forall e1 e2,
      C7IntTree e1 ->
      C7IntTree e2 ->
      C7IntTree (binaryApp add_ e1 e2)
  | C7IntSub : forall e1 e2,
      C7IntTree e1 ->
      C7IntTree e2 ->
      C7IntTree (binaryApp sub_ e1 e2)
  | C7IntMul : forall e1 e2,
      C7IntTree e1 ->
      C7IntTree e2 ->
      C7IntTree (binaryApp mul_ e1 e2)
  | C7IntIf : forall c e1 e2,
      Property.candidates.v006.Candidate.C6BoolTree c ->
      C7IntTree e1 ->
      C7IntTree e2 ->
      C7IntTree (ite c e1 e2).

Inductive C7IntSet : CedarExpr -> Prop :=
  | C7SetSingle : forall e,
      C7IntTree e ->
      C7IntSet (setExprCons e setExprNil)
  | C7SetCons : forall e rest,
      C7IntTree e ->
      C7IntSet rest ->
      C7IntSet (setExprCons e rest).

Inductive C7BoolTree : CedarExpr -> Prop :=
  | C7BoolBase : forall e,
      Property.candidates.v006.Candidate.C6BoolTree e ->
      C7BoolTree e
  | C7Less : forall e1 e2,
      C7IntTree e1 ->
      C7IntTree e2 ->
      C7BoolTree (binaryApp less e1 e2)
  | C7LessEq : forall e1 e2,
      C7IntTree e1 ->
      C7IntTree e2 ->
      C7BoolTree (binaryApp lessEq e1 e2)
  | C7Contains : forall set_e int_e,
      C7IntSet set_e ->
      C7IntTree int_e ->
      C7BoolTree (binaryApp contains set_e int_e)
  | C7ContainsAll : forall set_e1 set_e2,
      C7IntSet set_e1 ->
      C7IntSet set_e2 ->
      C7BoolTree (binaryApp containsAll set_e1 set_e2)
  | C7ContainsAny : forall set_e1 set_e2,
      C7IntSet set_e1 ->
      C7IntSet set_e2 ->
      C7BoolTree (binaryApp containsAny set_e1 set_e2)
  | C7Not : forall e,
      C7BoolTree e ->
      C7BoolTree (unaryApp not_ e)
  | C7And : forall e1 e2,
      C7BoolTree e1 ->
      C7BoolTree e2 ->
      C7BoolTree (andExpr e1 e2)
  | C7If : forall c e1 e2,
      C7BoolTree c ->
      C7BoolTree e1 ->
      C7BoolTree e2 ->
      C7BoolTree (ite c e1 e2).

Inductive C7Case : CedarType -> (CedarExpr * PathSet) -> Prop :=
  | C7Integer : forall e,
      C7IntTree e ->
      C7Case intType (e, somepaths [])
  | C7Set : forall e,
      C7IntSet e ->
      C7Case (setType intType) (e, somepaths [])
  | C7Boolean : forall e,
      C7BoolTree e ->
      C7Case (boolType anyBool) (e, somepaths [])
  | C7IntegerIf : forall c e1 e2,
      C7BoolTree c ->
      C7IntTree e1 ->
      C7IntTree e2 ->
      C7Case intType (ite c e1 e2, somepaths [])
  | C7SetIf : forall c e1 e2,
      C7BoolTree c ->
      C7IntSet e1 ->
      C7IntSet e2 ->
      C7Case (setType intType) (ite c e1 e2, somepaths [])
  | C7StringIf : forall c e1 e2,
      C7BoolTree c ->
      Property.candidates.v004.Candidate.C4StringTree e1 ->
      Property.candidates.v004.Candidate.C4StringTree e2 ->
      C7Case stringType (ite c e1 e2, somepaths [])
  | C7RecordField : forall field e,
      C7IntTree e ->
      C7Case (recordTypeCons field false intType recordTypeNil)
             (recExprCons field e recExprNil, somepaths [])
  | C7RecordGet : forall field e,
      C7IntTree e ->
      C7Case intType
             (getAttr (recExprCons field e recExprNil) field, somepaths []).

Inductive predicate : Original.Input -> Prop :=
  | C7Inherited : forall i,
      Property.candidates.v006.Candidate.predicate i ->
      predicate i
  | C7Structured : forall (action_id : string) ty expr,
      C7Case ty expr ->
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
