Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v005.Candidate.
Import ListNotations.

Inductive TinyBoolExpr : CedarExpr -> Prop :=
  | TinyBoolLess : forall e1 e2,
      Property.candidates.v005.Candidate.TinyIntExpr e1 ->
      Property.candidates.v005.Candidate.TinyIntExpr e2 ->
      TinyBoolExpr (binaryApp less e1 e2)
  | TinyBoolLessEq : forall e1 e2,
      Property.candidates.v005.Candidate.TinyIntExpr e1 ->
      Property.candidates.v005.Candidate.TinyIntExpr e2 ->
      TinyBoolExpr (binaryApp lessEq e1 e2)
  | TinyBoolNot : forall e,
      TinyBoolExpr e ->
      TinyBoolExpr (unaryApp not_ e).

Inductive predicate : Original.Input -> Prop :=
  | PredicateTinyBool : forall ets acts r e,
      Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
      TinyBoolExpr e ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        (boolType anyBool) (e, somepaths []))
  | PredicatePrevious : forall i,
      Property.candidates.v005.Candidate.predicate i ->
      predicate i.
