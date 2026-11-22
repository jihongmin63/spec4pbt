Require Import List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v002.Candidate.
Import ListNotations.

Inductive predicate : Original.Input -> Prop :=
  | PredicateFalse : forall ets acts r,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] [r] ->
      predicate
        (Original.mkInput ets acts [r]
          (MkEnvironment (MkSchema ets acts) r) []
          (boolType ff_) (lit (boolean false), allpaths))
  | PredicatePrevious : forall i,
      Property.candidates.v002.Candidate.predicate i ->
      predicate i.
