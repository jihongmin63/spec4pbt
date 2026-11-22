Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive predicate : Original.Input -> Prop :=
  | SimpleTrue : forall id : string,
      predicate
        (Original.mkInput
          [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
           (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
          [(MkEntityUID (MkName "Action" []) id,
            MkActionSchemaEntry
              [MkName "EntityType1" []] [MkName "EntityType2" []] [])]
          [MkRequest
            (MkName "EntityType1" [])
            (MkEntityUID (MkName "Action" []) id)
            (MkName "EntityType2" []) []]
          (MkEnvironment
            (MkSchema
              [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
               (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
              [(MkEntityUID (MkName "Action" []) id,
                MkActionSchemaEntry
                  [MkName "EntityType1" []] [MkName "EntityType2" []] [])])
            (MkRequest
              (MkName "EntityType1" [])
              (MkEntityUID (MkName "Action" []) id)
              (MkName "EntityType2" []) []))
          []
          (boolType tt_)
          (lit (boolean true), somepaths []))
  | General : forall i,
      Property.candidates.v001.Candidate.predicate i ->
      predicate i.
