From QuickChick Require Import QuickChick.
Require Import Property.Original.
Require Import Specification.cedar.Spec.
From Coq Require Import List String ZArith.
Import ListNotations.
Import QcDefaultNotation.
Open Scope qc_scope.
Open Scope string_scope.

#[global] Instance DecidableEqEntityName : Dec_Eq EntityName.
Proof. dec_eq. Defined.
#[global] Instance DecidableEqCedarType : Dec_Eq CedarType.
Proof. dec_eq. Defined.
#[global] Instance DecidableEqPrim : Dec_Eq Prim.
Proof. dec_eq. Defined.
#[global] Instance DecidableEqEntityUID : Dec_Eq EntityUID.
Proof. dec_eq. Defined.
#[global] Instance DecidableEqActionSchemaEntry : Dec_Eq ActionSchemaEntry.
Proof. dec_eq. Defined.
Definition genCedarString (_ : nat) : G string :=
  freq_ (returnGen "Aaron") [(1, returnGen "Aaron"); (1, returnGen "John");
    (1, returnGen "Mike"); (1, returnGen "Kesha"); (1, returnGen "Hicks");
    (1, returnGen "A"); (1, returnGen "B"); (1, returnGen "C"); (1, returnGen "D")].
#[global] Instance genSizedString : GenSized string :=
  {| arbitrarySized := genCedarString |}.
#[global] Instance shrinkString : Shrink string :=
  {| shrink := fun _ => nil |}.
Derive (Arbitrary) for EntityName.
Definition genEntityNameCanonical : G EntityName :=
  freq_ (returnGen (MkName "EntityType1" []))
    [(1, returnGen (MkName "EntityType1" []));
     (1, returnGen (MkName "EntityType2" []))].
#[global] Instance genSizedEntityNameCanonical : GenSized EntityName | 1 :=
  {| arbitrarySized := fun _ => genEntityNameCanonical |}.

Derive (Arbitrary) for EntityUID.
(** Match the active fallback generator policy in the pinned Cedar.v. *)
Definition genEntityUIDCanonical : G EntityUID :=
  bindGen genEntityNameCanonical (fun n =>
    freq_ (returnGen (MkEntityUID n "A"))
      [(1, returnGen (MkEntityUID n "A"));
       (1, returnGen (MkEntityUID n "B"));
       (1, returnGen (MkEntityUID n "C"));
       (1, returnGen (MkEntityUID n "D"))]).
#[global] Instance genSizedEntityUIDCanonical : GenSized EntityUID | 1 :=
  {| arbitrarySized := fun _ => genEntityUIDCanonical |}.

Derive (Arbitrary) for Prim.
Derive (Arbitrary) for Var.
Derive (Arbitrary) for PatElem.
Derive (Arbitrary) for UnaryOp.
Derive (Arbitrary) for BinaryOp.
Derive (Arbitrary) for CedarExpr.
Derive (Arbitrary) for BoolType.
Derive (Arbitrary) for CedarType.
Derive (Arbitrary) for EntitySchemaEntry.
Derive (Arbitrary) for ActionSchemaEntry.
Derive (Arbitrary) for RequestType.
Derive (Arbitrary) for PathSet.
Derive Show for EntityName.
Derive Show for EntityUID.
Derive Show for Prim.
Derive Show for Var.
Derive Show for PatElem.
Derive Show for UnaryOp.
Derive Show for BinaryOp.
Derive Show for CedarExpr.
Derive Show for BoolType.
Derive Show for CedarType.
Derive Show for EntitySchemaEntry.
Derive Show for ActionSchemaEntry.
Derive Show for Schema.
Derive Show for RequestType.
Derive Show for PathSet.
Derive Show for Environment.
#[global] Instance DecidableEqPathSet : Dec_Eq PathSet.
Proof. dec_eq. Defined.
#[global] Instance DecEqEnvironment : Dec_Eq Environment.
Proof. dec_eq. Defined.
(** These default-priority overrides are the active instances in the pinned
    CedarWellTypedTermGenerator.v theorem, after Cedar.v's canonical instances. *)
Definition genEntityNameConst : G EntityName :=
  freq_ (returnGen (MkName "EntityType1" []))
    [(1, returnGen (MkName "EntityType1" []));
     (1, returnGen (MkName "EntityType2" []))].
#[global] Instance genSizedEntityNameConst : GenSized EntityName :=
  {| arbitrarySized := fun _ => genEntityNameConst |}.

Definition genEntityUIDConst : G EntityUID :=
  bindGen genEntityNameConst (fun n =>
    freq_ (returnGen (MkEntityUID n "A"))
      [(1, returnGen (MkEntityUID n "A"));
       (1, returnGen (MkEntityUID n "B"));
       (1, returnGen (MkEntityUID n "C"));
       (1, returnGen (MkEntityUID n "D"));
       (1, returnGen (MkEntityUID n "Hicks"));
       (1, returnGen (MkEntityUID n "Kesha"))]).
#[global] Instance genSizedEntityUIDConst : GenSized EntityUID :=
  {| arbitrarySized := fun _ => genEntityUIDConst |}.

(** Fixed schema fallback from the same upstream theorem file. *)
Definition benchmark_schema : Schema :=
  let team := MkName "Team" [] in
  let teamDef := MkEntitySchemaEntry [team] [] in
  let user := MkName "User" [] in
  let userDef := MkEntitySchemaEntry [team]
    [("manager", true, entityType user)] in
  let lst := MkName "List" [] in
  let lstDef := MkEntitySchemaEntry []
    [("owner", true, entityType user);
     ("readers", true, entityType team);
     ("editors", true, entityType team);
     ("age", true, intType);
     ("description", true, stringType)] in
  let app := MkName "Application" [] in
  let appDef := MkEntitySchemaEntry [] [] in
  let action := MkName "Action" [] in
  let actionDef := MkEntitySchemaEntry [action] [] in
  let ets := [(user, userDef); (team, teamDef); (lst, lstDef);
              (app, appDef); (action, actionDef)] in
  let getAct := MkActionSchemaEntry [user] [lst] [] in
  let createAct := MkActionSchemaEntry [user] [app] [] in
  let updateAct := MkActionSchemaEntry [user] [lst] [] in
  let acts := [(MkEntityUID action "getList", getAct);
               (MkEntityUID action "createList", createAct);
               (MkEntityUID action "updateList", updateAct)] in
  MkSchema ets acts.
#[global] Instance GenSizedSchemaconst : GenSized Schema :=
  {| arbitrarySized := fun _ => returnGen benchmark_schema |}.
Derive GenSized for Environment.

#[global] Instance DecEqInput : Dec_Eq Original.Input.
Proof. dec_eq. Defined.
#[global] Instance DecEqCedarExpr : Dec_Eq CedarExpr.
Proof. dec_eq. Defined.
#[global] Instance DecEqRequestType : Dec_Eq RequestType.
Proof. dec_eq. Defined.
#[global] Instance DecEqSchema : Dec_Eq Schema.
Proof. dec_eq. Defined.
#[global] Instance ShowInput : Show Original.Input :=
  {| show i := "Original.mkInput (" ++ show (Original.ets i) ++ ") (" ++
       show (Original.acts i) ++ ") (" ++ show (Original.rs i) ++ ") (" ++
       show (Original.e i) ++ ") (" ++ show (Original.es i) ++ ") (" ++
       show (Original.ty i) ++ ") (" ++ show (Original.expr i) ++ ")" |}.

(** The scheduler's seven-variable observation has exactly Original's five
    premises after packing; this is a proof about the predicate, not about the
    generated samples or external Cedar checker. *)
Theorem p0_packaging : forall ets acts rs e es ty expr,
  Original.predicate (Original.mkInput ets acts rs e es ty expr) <->
    WfSchema Original.entity_names (MkSchema ets acts) /\
    ActionSchemaToRequestTypes acts [] rs /\
    SchemaToEnvironments (MkSchema ets acts) rs (e :: es) /\
    WfCedarType Original.entity_names ty /\
    HasType (somepaths []) e expr ty.
Proof.
  intros; unfold Original.predicate; simpl; tauto.
Qed.
Print Assumptions p0_packaging.
