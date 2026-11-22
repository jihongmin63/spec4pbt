Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v005.Candidate.
Require Import Property.candidates.v007.Candidate.
Import ListNotations.

Inductive predicate : Original.Input -> Prop :=
  | PredicateIntRecord : forall ets acts r field value,
      Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
      Property.candidates.v005.Candidate.TinyIntExpr value ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        (recordTypeCons field false intType recordTypeNil)
        (recExprCons field value recExprNil, somepaths []))
  | PredicatePrevious : forall i,
      Property.candidates.v007.Candidate.predicate i ->
      predicate i.
