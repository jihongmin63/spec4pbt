Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Import ListNotations.
Open Scope string_scope.

Inductive predicate : Original.Input -> Prop :=
  | CandidateInput :
      forall et1 et2 action_id principal_name resource_name attrs acts_tail
             request requests_tail environments_tail ty expr,
        WfSchema Original.entity_names
          (MkSchema
             [(MkName "EntityType1" [], et1); (MkName "EntityType2" [], et2)]
             ((MkEntityUID (MkName "Action" []) action_id,
               MkActionSchemaEntry [principal_name] [resource_name] attrs)
              :: acts_tail)) ->
        ActionSchemaToRequestTypes
          ((MkEntityUID (MkName "Action" []) action_id,
            MkActionSchemaEntry [principal_name] [resource_name] attrs)
           :: acts_tail) [] (request :: requests_tail) ->
        SchemaToEnvironments
          (MkSchema
             [(MkName "EntityType1" [], et1); (MkName "EntityType2" [], et2)]
             ((MkEntityUID (MkName "Action" []) action_id,
               MkActionSchemaEntry [principal_name] [resource_name] attrs)
              :: acts_tail))
          (request :: requests_tail)
          (MkEnvironment
             (MkSchema
                [(MkName "EntityType1" [], et1); (MkName "EntityType2" [], et2)]
                ((MkEntityUID (MkName "Action" []) action_id,
                  MkActionSchemaEntry [principal_name] [resource_name] attrs)
                 :: acts_tail)) request :: environments_tail) ->
        WfCedarType Original.entity_names ty ->
        HasType (somepaths [])
          (MkEnvironment
             (MkSchema
                [(MkName "EntityType1" [], et1); (MkName "EntityType2" [], et2)]
                ((MkEntityUID (MkName "Action" []) action_id,
                  MkActionSchemaEntry [principal_name] [resource_name] attrs)
                 :: acts_tail)) request) expr ty ->
        predicate
          (Original.mkInput
             [(MkName "EntityType1" [], et1); (MkName "EntityType2" [], et2)]
             ((MkEntityUID (MkName "Action" []) action_id,
               MkActionSchemaEntry [principal_name] [resource_name] attrs)
              :: acts_tail)
             (request :: requests_tail)
             (MkEnvironment
                (MkSchema
                   [(MkName "EntityType1" [], et1); (MkName "EntityType2" [], et2)]
                   ((MkEntityUID (MkName "Action" []) action_id,
                     MkActionSchemaEntry [principal_name] [resource_name] attrs)
                    :: acts_tail)) request)
             environments_tail ty expr).
