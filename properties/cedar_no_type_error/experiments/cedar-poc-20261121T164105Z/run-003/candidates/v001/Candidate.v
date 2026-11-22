Require Import Specification.cedar.Spec.
Require Import Property.Original.

Inductive predicate : Original.Input -> Prop :=
  | Predicate : forall ets acts rs e es ty expr,
      WfSchema Original.entity_names (MkSchema ets acts) ->
      ActionSchemaToRequestTypes acts nil rs ->
      SchemaToEnvironments (MkSchema ets acts) rs (cons e es) ->
      WfCedarType Original.entity_names ty ->
      HasType (somepaths nil) e expr ty ->
      predicate (Original.mkInput ets acts rs e es ty expr).
