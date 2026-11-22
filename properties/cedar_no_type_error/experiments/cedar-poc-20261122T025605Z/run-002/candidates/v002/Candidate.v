Require Import List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Import ListNotations.

Inductive predicate : Original.Input -> Prop :=
  | PredicateEnvironments : forall ets acts r rs es ty expr,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts [] (r :: rs) ->
      SchemaToEnvironments (MkSchema ets acts) (r :: rs)
        (MkEnvironment (MkSchema ets acts) r :: es) ->
      WfCedarType Original.entity_names ty ->
      HasType (somepaths []) (MkEnvironment (MkSchema ets acts) r) expr ty ->
      predicate
        (Original.mkInput ets acts (r :: rs)
          (MkEnvironment (MkSchema ets acts) r) es ty expr).
