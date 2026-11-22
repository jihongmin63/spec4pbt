Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive C6BoolTree : CedarExpr -> Prop :=
  | C6BoolLeaf : forall e,
      Property.candidates.v004.Candidate.C4BoolTree e ->
      C6BoolTree e
  | C6BoolNot : forall e,
      C6BoolTree e ->
      C6BoolTree (unaryApp not_ e)
  | C6BoolAnd : forall e1 e2,
      C6BoolTree e1 ->
      C6BoolTree e2 ->
      C6BoolTree (andExpr e1 e2)
  | C6BoolIf : forall c e1 e2,
      C6BoolTree c ->
      C6BoolTree e1 ->
      C6BoolTree e2 ->
      C6BoolTree (ite c e1 e2).

Inductive C6Case : CedarType -> (CedarExpr * PathSet) -> Prop :=
  | C6Boolean : forall e,
      C6BoolTree e ->
      C6Case (boolType anyBool) (e, somepaths [])
  | C6IntegerIf : forall c e1 e2,
      C6BoolTree c ->
      Property.candidates.v003.Candidate.IntTree e1 ->
      Property.candidates.v003.Candidate.IntTree e2 ->
      C6Case intType (ite c e1 e2, somepaths [])
  | C6StringIf : forall c e1 e2,
      C6BoolTree c ->
      Property.candidates.v004.Candidate.C4StringTree e1 ->
      Property.candidates.v004.Candidate.C4StringTree e2 ->
      C6Case stringType (ite c e1 e2, somepaths []).

Inductive predicate : Original.Input -> Prop :=
  | C6Inherited : forall i,
      Property.candidates.v005.Candidate.predicate i ->
      predicate i
  | C6Structured : forall (action_id : string) ty expr,
      C6Case ty expr ->
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
