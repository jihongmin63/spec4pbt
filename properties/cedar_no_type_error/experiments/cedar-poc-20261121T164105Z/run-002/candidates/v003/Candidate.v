Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v002.Candidate.
Import ListNotations.
Open Scope string_scope.

Inductive SimpleTyped : Environment -> (CedarExpr * PathSet) -> CedarType -> Prop :=
| SimpleRecordNil : forall env,
    SimpleTyped env (recExprNil, somepaths []) recordTypeNil
| SimplePrincipal : forall schema p uid r attrs,
    SimpleTyped
      (MkEnvironment schema (MkRequest p uid r attrs))
      (var principal, somepaths []) (entityType p)
| SimpleResource : forall schema p uid r attrs,
    SimpleTyped
      (MkEnvironment schema (MkRequest p uid r attrs))
      (var resource, somepaths []) (entityType r)
| SimpleContext : forall schema p uid r attrs ty,
    ReqContextToCedarType attrs ty ->
    SimpleTyped
      (MkEnvironment schema (MkRequest p uid r attrs))
      (var context, somepaths []) ty
| SimpleNotTrue : forall env,
    SimpleTyped env
      (unaryApp not_ (lit (boolean true)), allpaths) (boolType ff_)
| SimpleNotFalse : forall env,
    SimpleTyped env
      (unaryApp not_ (lit (boolean false)), somepaths []) (boolType tt_)
| SimpleNeg : forall env n,
    SimpleTyped env
      (unaryApp neg (lit (int n)), somepaths []) intType
| SimpleAdd : forall env n m,
    SimpleTyped env
      (binaryApp add_ (lit (int n)) (lit (int m)), somepaths []) intType
| SimpleLess : forall env n m,
    SimpleTyped env
      (binaryApp less (lit (int n)) (lit (int m)), somepaths [])
      (boolType anyBool)
| SimpleEqualInt : forall env n,
    SimpleTyped env
      (binaryApp equals (lit (int n)) (lit (int n)), somepaths [])
      (boolType tt_)
| SimpleSingletonInt : forall env n,
    SimpleTyped env
      (setExprCons (lit (int n)) setExprNil, somepaths [])
      (setType intType)
| SimpleIfTrue : forall env n m,
    SimpleTyped env
      (ite (lit (boolean true)) (lit (int n)) (lit (int m)), somepaths [])
      intType.

Inductive predicate : Original.Input -> Prop :=
| PredicateSimple :
    forall ets p r action_id attrs expr ty,
      WfETS Original.entity_names Original.entity_names ets ->
      WfACT Original.entity_names
        (MkEntityUID (MkName "Action" []) action_id,
         MkActionSchemaEntry [p] [r] attrs) ->
      WfCedarType Original.entity_names ty ->
      SimpleTyped
        (MkEnvironment
          (MkSchema ets
            [(MkEntityUID (MkName "Action" []) action_id,
              MkActionSchemaEntry [p] [r] attrs)])
          (MkRequest p (MkEntityUID (MkName "Action" []) action_id) r attrs))
        expr ty ->
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
          [] ty expr)
| PredicatePredecessor :
    forall input,
      Property.candidates.v002.Candidate.predicate input ->
      predicate input.
