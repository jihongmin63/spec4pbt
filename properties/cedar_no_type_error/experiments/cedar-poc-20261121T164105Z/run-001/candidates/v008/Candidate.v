Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v007.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive C8StringTree : CedarExpr -> Prop :=
  | C8StringBase : forall e,
      Property.candidates.v004.Candidate.C4StringTree e ->
      C8StringTree e
  | C8StringIf : forall c e1 e2,
      Property.candidates.v007.Candidate.C7BoolTree c ->
      C8StringTree e1 ->
      C8StringTree e2 ->
      C8StringTree (ite c e1 e2).

Inductive C8StringSet : CedarExpr -> Prop :=
  | C8SetSingle : forall e,
      C8StringTree e ->
      C8StringSet (setExprCons e setExprNil)
  | C8SetCons : forall e rest,
      C8StringTree e ->
      C8StringSet rest ->
      C8StringSet (setExprCons e rest).

Inductive C8BoolTree : CedarExpr -> Prop :=
  | C8BoolBase : forall e,
      Property.candidates.v007.Candidate.C7BoolTree e ->
      C8BoolTree e
  | C8Like : forall pat e,
      C8StringTree e ->
      C8BoolTree (unaryApp (like pat) e)
  | C8Contains : forall set_e string_e,
      C8StringSet set_e ->
      C8StringTree string_e ->
      C8BoolTree (binaryApp contains set_e string_e)
  | C8ContainsAll : forall set_e1 set_e2,
      C8StringSet set_e1 ->
      C8StringSet set_e2 ->
      C8BoolTree (binaryApp containsAll set_e1 set_e2)
  | C8ContainsAny : forall set_e1 set_e2,
      C8StringSet set_e1 ->
      C8StringSet set_e2 ->
      C8BoolTree (binaryApp containsAny set_e1 set_e2)
  | C8BoolNot : forall e,
      C8BoolTree e ->
      C8BoolTree (unaryApp not_ e)
  | C8BoolAnd : forall e1 e2,
      C8BoolTree e1 ->
      C8BoolTree e2 ->
      C8BoolTree (andExpr e1 e2)
  | C8BoolIf : forall c e1 e2,
      C8BoolTree c ->
      C8BoolTree e1 ->
      C8BoolTree e2 ->
      C8BoolTree (ite c e1 e2)
  | C8BoolIfTrueFalse : forall c,
      C8BoolTree c ->
      C8BoolTree (ite c (lit (boolean true)) (lit (boolean false)))
  | C8BoolIfFalseTrue : forall c,
      C8BoolTree c ->
      C8BoolTree (ite c (lit (boolean false)) (lit (boolean true))).

Inductive C8Case : CedarType -> (CedarExpr * PathSet) -> Prop :=
  | C8String : forall e,
      C8StringTree e ->
      C8Case stringType (e, somepaths [])
  | C8StringSetCase : forall e,
      C8StringSet e ->
      C8Case (setType stringType) (e, somepaths [])
  | C8Bool : forall e,
      C8BoolTree e ->
      C8Case (boolType anyBool) (e, somepaths [])
  | C8StringSetIf : forall c e1 e2,
      C8BoolTree c ->
      C8StringSet e1 ->
      C8StringSet e2 ->
      C8Case (setType stringType) (ite c e1 e2, somepaths [])
  | C8StringField : forall field e,
      C8StringTree e ->
      C8Case (recordTypeCons field false stringType recordTypeNil)
             (recExprCons field e recExprNil, somepaths [])
  | C8StringGet : forall field e,
      C8StringTree e ->
      C8Case stringType
             (getAttr (recExprCons field e recExprNil) field, somepaths [])
  | C8BoolField : forall field e,
      C8BoolTree e ->
      C8Case (recordTypeCons field false (boolType anyBool) recordTypeNil)
             (recExprCons field e recExprNil, somepaths [])
  | C8BoolGet : forall field e,
      C8BoolTree e ->
      C8Case (boolType anyBool)
             (getAttr (recExprCons field e recExprNil) field, somepaths []).

Inductive predicate : Original.Input -> Prop :=
  | C8Inherited : forall i,
      Property.candidates.v007.Candidate.predicate i ->
      predicate i
  | C8Structured : forall (action_id : string) ty expr,
      C8Case ty expr ->
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
