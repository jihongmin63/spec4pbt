Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v003.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive TinySchema : Schema -> RequestType -> Prop :=
  | TinySchemaOne : forall id,
      TinySchema
        (MkSchema
          [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
           (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
          [(MkEntityUID (MkName "Action" []) id,
            MkActionSchemaEntry
              [MkName "EntityType1" []]
              [MkName "EntityType1" []] [])])
        (MkRequest (MkName "EntityType1" [])
          (MkEntityUID (MkName "Action" []) id)
          (MkName "EntityType1" []) []).

Inductive predicate : Original.Input -> Prop :=
  | PredicateFalse : forall ets acts r,
      TinySchema (MkSchema ets acts) r ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        (boolType ff_) (lit (boolean false), allpaths))
  | PredicateTrue : forall ets acts r,
      TinySchema (MkSchema ets acts) r ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        (boolType tt_) (lit (boolean true), somepaths []))
  | PredicateInt : forall ets acts r z,
      TinySchema (MkSchema ets acts) r ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        intType (lit (int z), somepaths []))
  | PredicateString : forall ets acts r s,
      TinySchema (MkSchema ets acts) r ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        stringType (lit (stringLit s), somepaths []))
  | PredicateRecordNil : forall ets acts r,
      TinySchema (MkSchema ets acts) r ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        recordTypeNil (recExprNil, somepaths []))
  | PredicatePrevious : forall i,
      Property.candidates.v003.Candidate.predicate i ->
      predicate i.
