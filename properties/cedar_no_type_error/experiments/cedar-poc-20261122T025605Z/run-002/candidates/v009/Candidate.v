Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v004.Candidate.
Require Import Property.candidates.v008.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive predicate : Original.Input -> Prop :=
  | PredicatePrincipal : forall ets acts r,
      Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        (entityType (MkName "EntityType1" []))
        (var principal, somepaths []))
  | PredicateResource : forall ets acts r,
      Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        (entityType (MkName "EntityType1" []))
        (var resource, somepaths []))
  | PredicateContext : forall ets acts r,
      Property.candidates.v004.Candidate.TinySchema (MkSchema ets acts) r ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        recordTypeNil (var context, somepaths []))
  | PredicatePrevious : forall i,
      Property.candidates.v008.Candidate.predicate i ->
      predicate i.
