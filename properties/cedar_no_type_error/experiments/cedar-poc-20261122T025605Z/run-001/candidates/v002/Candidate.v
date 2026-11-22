Require Import List Specification.cedar.Spec Property.Original.
Require Import Property.candidates.v001.Candidate.
Import ListNotations.

Inductive predicate : Original.Input -> Prop :=
  | PredicatePrevious : forall i,
      Property.candidates.v001.Candidate.predicate i ->
      predicate i
  | PredicateTrueSingle : forall ets acts r,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] [r] ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        (boolType tt_) (lit (boolean true), somepaths []))
  | PredicateFalseSingle : forall ets acts r,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] [r] ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        (boolType ff_) (lit (boolean false), allpaths))
  | PredicateTrueCons : forall ets acts r rs es,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] (r :: rs) ->
      SchemaToEnvironments (MkSchema ets acts) rs es ->
      predicate (Original.mkInput ets acts (r :: rs)
        (MkEnvironment (MkSchema ets acts) r) es
        (boolType tt_) (lit (boolean true), somepaths []))
  | PredicateFalseCons : forall ets acts r rs es,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] (r :: rs) ->
      SchemaToEnvironments (MkSchema ets acts) rs es ->
      predicate (Original.mkInput ets acts (r :: rs)
        (MkEnvironment (MkSchema ets acts) r) es
        (boolType ff_) (lit (boolean false), allpaths)).
