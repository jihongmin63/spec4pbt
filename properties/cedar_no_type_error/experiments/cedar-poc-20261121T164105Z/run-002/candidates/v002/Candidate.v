Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive predicate : Original.Input -> Prop :=
| PredicateTrue :
    forall ets p r action_id attrs,
      WfETS Original.entity_names Original.entity_names ets ->
      WfACT Original.entity_names
        (MkEntityUID (MkName "Action" []) action_id,
         MkActionSchemaEntry [p] [r] attrs) ->
      predicate
        (Original.mkInput ets
          [(MkEntityUID (MkName "Action" []) action_id,
            MkActionSchemaEntry [p] [r] attrs)]
          [MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs]
          (MkEnvironment
            (MkSchema ets
              [(MkEntityUID (MkName "Action" []) action_id,
                MkActionSchemaEntry [p] [r] attrs)])
            (MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs))
          [] (boolType tt_) (lit (boolean true), somepaths []))
| PredicateFalse :
    forall ets p r action_id attrs,
      WfETS Original.entity_names Original.entity_names ets ->
      WfACT Original.entity_names
        (MkEntityUID (MkName "Action" []) action_id,
         MkActionSchemaEntry [p] [r] attrs) ->
      predicate
        (Original.mkInput ets
          [(MkEntityUID (MkName "Action" []) action_id,
            MkActionSchemaEntry [p] [r] attrs)]
          [MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs]
          (MkEnvironment
            (MkSchema ets
              [(MkEntityUID (MkName "Action" []) action_id,
                MkActionSchemaEntry [p] [r] attrs)])
            (MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs))
          [] (boolType ff_) (lit (boolean false), allpaths))
| PredicateInt :
    forall ets p r action_id attrs n,
      WfETS Original.entity_names Original.entity_names ets ->
      WfACT Original.entity_names
        (MkEntityUID (MkName "Action" []) action_id,
         MkActionSchemaEntry [p] [r] attrs) ->
      predicate
        (Original.mkInput ets
          [(MkEntityUID (MkName "Action" []) action_id,
            MkActionSchemaEntry [p] [r] attrs)]
          [MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs]
          (MkEnvironment
            (MkSchema ets
              [(MkEntityUID (MkName "Action" []) action_id,
                MkActionSchemaEntry [p] [r] attrs)])
            (MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs))
          [] intType (lit (int n), somepaths []))
| PredicateString :
    forall ets p r action_id attrs value,
      WfETS Original.entity_names Original.entity_names ets ->
      WfACT Original.entity_names
        (MkEntityUID (MkName "Action" []) action_id,
         MkActionSchemaEntry [p] [r] attrs) ->
      predicate
        (Original.mkInput ets
          [(MkEntityUID (MkName "Action" []) action_id,
            MkActionSchemaEntry [p] [r] attrs)]
          [MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs]
          (MkEnvironment
            (MkSchema ets
              [(MkEntityUID (MkName "Action" []) action_id,
                MkActionSchemaEntry [p] [r] attrs)])
            (MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs))
          [] stringType (lit (stringLit value), somepaths []))
| PredicateGeneral :
    forall i,
      Property.candidates.v001.Candidate.predicate i ->
      predicate i.
