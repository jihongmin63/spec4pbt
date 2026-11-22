Require Import List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Import ListNotations.

Inductive predicate : Original.Input -> Prop :=
  | PredicateSingle : forall ets acts r ty expr,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] [r] ->
      WfCedarType Original.entity_names ty ->
      HasType (somepaths []) (MkEnvironment (MkSchema ets acts) r) expr ty ->
      predicate
        (Original.mkInput ets acts [r]
          (MkEnvironment (MkSchema ets acts) r) [] ty expr)
  | PredicateCons : forall ets acts r rs envs ty expr,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] (r :: rs) ->
      SchemaToEnvironments (MkSchema ets acts) rs envs ->
      WfCedarType Original.entity_names ty ->
      HasType (somepaths []) (MkEnvironment (MkSchema ets acts) r) expr ty ->
      predicate
        (Original.mkInput ets acts (r :: rs)
          (MkEnvironment (MkSchema ets acts) r) envs ty expr).
