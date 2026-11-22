Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v003.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive C4StringTree : CedarExpr -> Prop :=
  | C4StringLiteral : forall s,
      C4StringTree (lit (stringLit s))
  | C4StringIfTrue : forall e1 e2,
      C4StringTree e1 ->
      C4StringTree e2 ->
      C4StringTree (ite (lit (boolean true)) e1 e2)
  | C4StringIfFalse : forall e1 e2,
      C4StringTree e1 ->
      C4StringTree e2 ->
      C4StringTree (ite (lit (boolean false)) e1 e2).

Inductive C4IntSet : CedarExpr -> Prop :=
  | C4SetSingle : forall e,
      Property.candidates.v003.Candidate.IntTree e ->
      C4IntSet (setExprCons e setExprNil)
  | C4SetCons : forall e rest,
      Property.candidates.v003.Candidate.IntTree e ->
      C4IntSet rest ->
      C4IntSet (setExprCons e rest).

Inductive C4BoolTree : CedarExpr -> Prop :=
  | C4Less : forall e1 e2,
      Property.candidates.v003.Candidate.IntTree e1 ->
      Property.candidates.v003.Candidate.IntTree e2 ->
      C4BoolTree (binaryApp less e1 e2)
  | C4LessEq : forall e1 e2,
      Property.candidates.v003.Candidate.IntTree e1 ->
      Property.candidates.v003.Candidate.IntTree e2 ->
      C4BoolTree (binaryApp lessEq e1 e2)
  | C4Like : forall e,
      C4StringTree e ->
      C4BoolTree (unaryApp (like []) e)
  | C4Not : forall e,
      C4BoolTree e ->
      C4BoolTree (unaryApp not_ e)
  | C4BoolIfTrue : forall e1 e2,
      C4BoolTree e1 ->
      C4BoolTree e2 ->
      C4BoolTree (ite (lit (boolean true)) e1 e2)
  | C4BoolIfFalse : forall e1 e2,
      C4BoolTree e1 ->
      C4BoolTree e2 ->
      C4BoolTree (ite (lit (boolean false)) e1 e2)
  | C4Contains : forall set_e int_e,
      C4IntSet set_e ->
      Property.candidates.v003.Candidate.IntTree int_e ->
      C4BoolTree (binaryApp contains set_e int_e)
  | C4ContainsAll : forall set_e1 set_e2,
      C4IntSet set_e1 ->
      C4IntSet set_e2 ->
      C4BoolTree (binaryApp containsAll set_e1 set_e2)
  | C4ContainsAny : forall set_e1 set_e2,
      C4IntSet set_e1 ->
      C4IntSet set_e2 ->
      C4BoolTree (binaryApp containsAny set_e1 set_e2).

Inductive C4Case : CedarType -> (CedarExpr * PathSet) -> Prop :=
  | C4String : forall e,
      C4StringTree e ->
      C4Case stringType (e, somepaths [])
  | C4Set : forall e,
      C4IntSet e ->
      C4Case (setType intType) (e, somepaths [])
  | C4Bool : forall e,
      C4BoolTree e ->
      C4Case (boolType anyBool) (e, somepaths [])
  | C4DoubleField : forall e1 e2,
      Property.candidates.v003.Candidate.IntTree e1 ->
      Property.candidates.v003.Candidate.IntTree e2 ->
      C4Case
        (recordTypeCons "left" false intType
          (recordTypeCons "right" false intType recordTypeNil))
        (recExprCons "left" e1 (recExprCons "right" e2 recExprNil),
         somepaths []).

Inductive predicate : Original.Input -> Prop :=
  | C4Inherited : forall i,
      Property.candidates.v003.Candidate.predicate i ->
      predicate i
  | C4Structured : forall (action_id : string) ty expr,
      C4Case ty expr ->
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
