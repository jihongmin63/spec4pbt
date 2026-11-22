Require Import List String Specification.cedar.Spec Property.Original.
Require Import Property.candidates.v004.Candidate.
Import ListNotations.

Inductive predicate : Original.Input -> Prop :=
  | PredicatePrevious : forall i,
      Property.candidates.v004.Candidate.predicate i ->
      predicate i
  | PredicateIntSingle : forall ets acts r n,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] [r] ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        intType (lit (int n), somepaths []))
  | PredicateIntCons : forall ets acts r rs es n,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] (r :: rs) ->
      SchemaToEnvironments (MkSchema ets acts) rs es ->
      predicate (Original.mkInput ets acts (r :: rs)
        (MkEnvironment (MkSchema ets acts) r) es
        intType (lit (int n), somepaths []))
  | PredicateStringSingle : forall ets acts r s,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] [r] ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        stringType (lit (stringLit s), somepaths []))
  | PredicateStringCons : forall ets acts r rs es s,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] (r :: rs) ->
      SchemaToEnvironments (MkSchema ets acts) rs es ->
      predicate (Original.mkInput ets acts (r :: rs)
        (MkEnvironment (MkSchema ets acts) r) es
        stringType (lit (stringLit s), somepaths [])).
