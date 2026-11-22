Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v005.Candidate.
Require Import Property.candidates.v006.Candidate.
Import ListNotations.

Inductive TinyIntSetExpr : CedarExpr -> Prop :=
  | TinyIntSetOne : forall e,
      Property.candidates.v005.Candidate.TinyIntExpr e ->
      TinyIntSetExpr (setExprCons e setExprNil)
  | TinyIntSetMore : forall e rest,
      Property.candidates.v005.Candidate.TinyIntExpr e ->
      TinyIntSetExpr rest ->
      WfSetSyntax rest ->
      TinyIntSetExpr (setExprCons e rest).

Inductive predicate : Original.Input -> Prop :=
  | PredicateTinyIntSet : forall ets acts r e,
      Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
      TinyIntSetExpr e ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        (setType intType) (e, somepaths []))
  | PredicatePrevious : forall i,
      Property.candidates.v006.Candidate.predicate i ->
      predicate i.
