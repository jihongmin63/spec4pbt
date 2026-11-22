Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v003.Candidate.
Require Import Property.candidates.v004.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive C5Case : CedarType -> (CedarExpr * PathSet) -> Prop :=
  | C5And : forall e1 e2,
      Property.candidates.v004.Candidate.C4BoolTree e1 ->
      Property.candidates.v004.Candidate.C4BoolTree e2 ->
      C5Case (boolType anyBool) (andExpr e1 e2, somepaths [])
  | C5IntConditional : forall c e1 e2,
      Property.candidates.v004.Candidate.C4BoolTree c ->
      Property.candidates.v003.Candidate.IntTree e1 ->
      Property.candidates.v003.Candidate.IntTree e2 ->
      C5Case intType (ite c e1 e2, somepaths [])
  | C5StringConditional : forall c e1 e2,
      Property.candidates.v004.Candidate.C4BoolTree c ->
      Property.candidates.v004.Candidate.C4StringTree e1 ->
      Property.candidates.v004.Candidate.C4StringTree e2 ->
      C5Case stringType (ite c e1 e2, somepaths [])
  | C5SetConditional : forall c e1 e2,
      Property.candidates.v004.Candidate.C4BoolTree c ->
      Property.candidates.v004.Candidate.C4IntSet e1 ->
      Property.candidates.v004.Candidate.C4IntSet e2 ->
      C5Case (setType intType) (ite c e1 e2, somepaths [])
  | C5RecordGet : forall field e,
      Property.candidates.v003.Candidate.IntTree e ->
      C5Case intType
        (getAttr (recExprCons field e recExprNil) field, somepaths [])
  | C5RecordHas : forall field e,
      Property.candidates.v003.Candidate.IntTree e ->
      C5Case (boolType tt_)
        (hasAttr (recExprCons field e recExprNil) field,
         somepaths [getAttr (recExprCons field e recExprNil) field])
  | C5EntityLiteral : forall uid,
      C5Case (entityType (MkName "EntityType1" []))
        (lit (entityUID (MkEntityUID (MkName "EntityType1" []) uid)),
         somepaths [])
  | C5IsPrincipal :
      C5Case (boolType tt_)
        (unaryApp (is_ (MkName "EntityType1" [])) (var principal),
         somepaths []).

Inductive predicate : Original.Input -> Prop :=
  | C5Inherited : forall i,
      Property.candidates.v004.Candidate.predicate i ->
      predicate i
  | C5Structured : forall (action_id : string) ty expr,
      C5Case ty expr ->
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
