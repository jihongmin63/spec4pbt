Require Import List String Specification.cedar.Spec Property.Original.
Require Import Property.candidates.v003.Candidate.
Import ListNotations.

Inductive predicate : Original.Input -> Prop :=
  | PredicatePrevious : forall i,
      Property.candidates.v003.Candidate.predicate i ->
      predicate i
  | PredicateEqualIntSingle : forall ets acts r n,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] [r] ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        (boolType tt_)
        (binaryApp equals (lit (int n)) (lit (int n)), somepaths []))
  | PredicateEqualIntCons : forall ets acts r rs es n,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] (r :: rs) ->
      SchemaToEnvironments (MkSchema ets acts) rs es ->
      predicate (Original.mkInput ets acts (r :: rs)
        (MkEnvironment (MkSchema ets acts) r) es
        (boolType tt_)
        (binaryApp equals (lit (int n)) (lit (int n)), somepaths []))
  | PredicateEqualStringSingle : forall ets acts r s,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] [r] ->
      predicate (Original.mkInput ets acts [r]
        (MkEnvironment (MkSchema ets acts) r) []
        (boolType tt_)
        (binaryApp equals (lit (stringLit s)) (lit (stringLit s)), somepaths []))
  | PredicateEqualStringCons : forall ets acts r rs es s,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] (r :: rs) ->
      SchemaToEnvironments (MkSchema ets acts) rs es ->
      predicate (Original.mkInput ets acts (r :: rs)
        (MkEnvironment (MkSchema ets acts) r) es
        (boolType tt_)
        (binaryApp equals (lit (stringLit s)) (lit (stringLit s)), somepaths [])).
