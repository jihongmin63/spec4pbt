Require Import List String.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Import ListNotations.
Open Scope string_scope.

Inductive SeedSchema :
  list (EntityName * EntitySchemaEntry) ->
  list (EntityUID * ActionSchemaEntry) -> RequestType -> Prop :=
| SeedSchemaOne : forall id,
    SeedSchema
      [(MkName "EntityType1" [], MkEntitySchemaEntry [] []);
       (MkName "EntityType2" [], MkEntitySchemaEntry [] [])]
      [(MkEntityUID (MkName "Action" []) id,
        MkActionSchemaEntry [MkName "EntityType1" []]
                            [MkName "EntityType2" []] [])]
      (MkRequest (MkName "EntityType1" [])
                 (MkEntityUID (MkName "Action" []) id)
                 (MkName "EntityType2" []) []).

Inductive predicate : Original.Input -> Prop :=
| CFalse : forall ets acts req,
    SeedSchema ets acts req ->
    predicate (Original.mkInput ets acts [req]
      (MkEnvironment (MkSchema ets acts) req) []
      (boolType ff_) (lit (boolean false), allpaths))
| CTrue : forall ets acts req,
    SeedSchema ets acts req ->
    predicate (Original.mkInput ets acts [req]
      (MkEnvironment (MkSchema ets acts) req) []
      (boolType tt_) (lit (boolean true), somepaths []))
| CInt : forall ets acts req n,
    SeedSchema ets acts req ->
    predicate (Original.mkInput ets acts [req]
      (MkEnvironment (MkSchema ets acts) req) []
      intType (lit (int n), somepaths []))
| CString : forall ets acts req s,
    SeedSchema ets acts req ->
    predicate (Original.mkInput ets acts [req]
      (MkEnvironment (MkSchema ets acts) req) []
      stringType (lit (stringLit s), somepaths []))
| CPrincipal : forall ets acts req,
    SeedSchema ets acts req ->
    predicate (Original.mkInput ets acts [req]
      (MkEnvironment (MkSchema ets acts) req) []
      (entityType (MkName "EntityType1" []))
      (var principal, somepaths []))
| CResource : forall ets acts req,
    SeedSchema ets acts req ->
    predicate (Original.mkInput ets acts [req]
      (MkEnvironment (MkSchema ets acts) req) []
      (entityType (MkName "EntityType2" []))
      (var resource, somepaths []))
| CContext : forall ets acts req,
    SeedSchema ets acts req ->
    predicate (Original.mkInput ets acts [req]
      (MkEnvironment (MkSchema ets acts) req) []
      recordTypeNil (var context, somepaths []))
| CGeneral : forall ets acts rs e es ty expr,
    WfSchema Original.entity_names (MkSchema ets acts) ->
    ActionSchemaToRequestTypes acts [] rs ->
    SchemaToEnvironments (MkSchema ets acts) rs (e :: es) ->
    WfCedarType Original.entity_names ty ->
    HasType (somepaths []) e expr ty ->
    predicate (Original.mkInput ets acts rs e es ty expr).
