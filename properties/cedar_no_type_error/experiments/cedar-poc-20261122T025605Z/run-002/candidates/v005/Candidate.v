Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v004.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive TinyIntExpr : CedarExpr -> Prop :=
  | TinyIntLit : forall z,
      TinyIntExpr (lit (int z))
  | TinyIntNeg : forall e,
      TinyIntExpr e ->
      TinyIntExpr (unaryApp neg e)
  | TinyIntAdd : forall e1 e2,
      TinyIntExpr e1 ->
      TinyIntExpr e2 ->
      TinyIntExpr (binaryApp add_ e1 e2)
  | TinyIntSub : forall e1 e2,
      TinyIntExpr e1 ->
      TinyIntExpr e2 ->
      TinyIntExpr (binaryApp sub_ e1 e2)
  | TinyIntMul : forall e1 e2,
      TinyIntExpr e1 ->
      TinyIntExpr e2 ->
      TinyIntExpr (binaryApp mul_ e1 e2).

Inductive predicate : Original.Input -> Prop :=
  | PredicateTinyInt : forall ets acts r e,
      Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
      TinyIntExpr e ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        intType (e, somepaths []))
  | PredicatePrevious : forall i,
      Property.candidates.v004.Candidate.predicate i ->
      predicate i.
