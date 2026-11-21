(** Cedar expression syntax, schemas, well-formedness and typing.
    Adapted from the Testing Theorems, Fully Automatically artifact's Cedar.v,
    which credits Mike Hicks's Coq formalization. See README.md and upstream/.
    Inductive definitions are preserved; generators, printers and execution
    commands are omitted. Only equality helpers are adapted to Coq 8.6.1.
*)
Require Import String ZArith List Bool.
Import ListNotations.
Open Scope string_scope.

(** Part One: Cedar expression syntax *)

(** The name of an entity *)
Inductive EntityName : Type :=
  | MkName : string -> list string -> EntityName.


(** Entity UIDs *)
Inductive EntityUID : Type :=
  | MkEntityUID : EntityName -> string -> EntityUID.


(** Primitive values *)
Inductive Prim : Type :=
  | boolean : bool -> Prim
  | int : Z -> Prim
  | stringLit : string -> Prim
  | entityUID : EntityUID -> Prim.


(** Variables *)
Inductive Var : Type :=
  | principal
  | action
  | resource
  | context.


(** Pattern elements *)
Inductive PatElem : Type :=
  | star
  | justLit : string -> PatElem.


(** Unary operations *)
Inductive UnaryOp : Type :=
  | not_
  | neg
  | like : list PatElem -> UnaryOp
  | is_ : EntityName -> UnaryOp.


(** Binary operations *)
Inductive BinaryOp : Type :=
  | equals
  | mem
  | less
  | lessEq
  | add_
  | sub_
  | mul_
  | contains
  | containsAll
  | containsAny.


(** Cedar expressions *)
Inductive CedarExpr : Type :=
  | lit : Prim -> CedarExpr
  | var : Var -> CedarExpr
  | ite : CedarExpr -> CedarExpr -> CedarExpr -> CedarExpr
  | andExpr : CedarExpr -> CedarExpr -> CedarExpr
  | orExpr : CedarExpr -> CedarExpr -> CedarExpr
  | unaryApp : UnaryOp -> CedarExpr -> CedarExpr
  | binaryApp : BinaryOp -> CedarExpr -> CedarExpr -> CedarExpr
  | getAttr : CedarExpr -> string -> CedarExpr
  | hasAttr : CedarExpr -> string -> CedarExpr
  | setExprNil : CedarExpr
  | setExprCons : CedarExpr -> CedarExpr -> CedarExpr
  | recExprNil : CedarExpr
  | recExprCons : string -> CedarExpr -> CedarExpr -> CedarExpr.


(** Entity data *)
Inductive EntityData : Type :=
  | MkEntityData : CedarExpr -> list EntityUID -> EntityData.


(** Request *)
Inductive Request : Type :=
  | MkReq : EntityUID -> EntityUID -> EntityUID -> CedarExpr -> Request.


(** Part Three: Cedar expression typing *)

(** Predicate: When an expression is a record *)
Inductive RecordExpr : CedarExpr -> Prop :=
  | RENil : RecordExpr recExprNil
  | RECons : forall fn e r, RecordExpr (recExprCons fn e r).

(** Predicate: field name is not present in a record expression *)
Inductive NotInRecExpr : string -> CedarExpr -> Prop :=
  | NIRNil : forall fn,
      NotInRecExpr fn recExprNil
  | NIRCons : forall fn fn' e r,
      fn <> fn' ->
      NotInRecExpr fn r ->
      NotInRecExpr fn (recExprCons fn' e r).

(** Predicate: When an expression is a set *)
Inductive SetExpr : CedarExpr -> Prop :=
  | SENil : SetExpr setExprNil
  | SECons : forall e r, SetExpr (setExprCons e r).

Inductive WfExprSyntax : CedarExpr -> Prop :=
  | WFSPrim : forall p, WfExprSyntax (lit p)
  | WFSVar : forall v, WfExprSyntax (var v)
  | WFSIte : forall c t e,
      WfExprSyntax c ->
      WfExprSyntax t ->
      WfExprSyntax e ->
      WfExprSyntax (ite c t e)
  | WFSAnd : forall e1 e2,
      WfExprSyntax e1 ->
      WfExprSyntax e2 ->
      WfExprSyntax (andExpr e1 e2)
  | WFSOr : forall e1 e2,
      WfExprSyntax e1 ->
      WfExprSyntax e2 ->
      WfExprSyntax (orExpr e1 e2)
  | WFSUnary : forall op e,
      WfExprSyntax e ->
      WfExprSyntax (unaryApp op e)
  | WFSBinary : forall op e1 e2,
      WfExprSyntax e1 ->
      WfExprSyntax e2 ->
      WfExprSyntax (binaryApp op e1 e2)
  | WFSGetAttr : forall e a,
      WfExprSyntax e ->
      WfExprSyntax (getAttr e a)
  | WFSHasAttr : forall e a,
      WfExprSyntax e ->
      WfExprSyntax (hasAttr e a)
  | WFSSetNil : WfExprSyntax setExprNil
  | WFSSetCons : forall e rest,
      WfExprSyntax e ->
      WfSetSyntax rest ->
      WfExprSyntax (setExprCons e rest)
  | WFSRecNil : WfExprSyntax recExprNil
  | WFSRecCons : forall s e rest,
      WfExprSyntax e ->
      WfRecSyntax rest ->
      NotInRecExpr s rest ->
      WfExprSyntax (recExprCons s e rest)

with WfSetSyntax : CedarExpr -> Prop :=
  | WFSSNil : WfSetSyntax setExprNil
  | WFSSCons : forall e rest,
      WfExprSyntax e ->
      WfSetSyntax rest ->
      WfSetSyntax (setExprCons e rest)

with WfRecSyntax : CedarExpr -> Prop :=
  | WFRNil : WfRecSyntax recExprNil
  | WFRCons : forall s e rest,
      WfExprSyntax e ->
      WfRecSyntax rest ->
      NotInRecExpr s rest ->
      WfRecSyntax (recExprCons s e rest).

(** Predicate: When an expression is a value *)
Inductive Value : CedarExpr -> Prop :=
  | VLit : forall p, Value (lit p)
  | VSNil : Value setExprNil
  | VSCons : forall e rest, Value e -> Value rest -> Value (setExprCons e rest)
  | VRNil : Value recExprNil
  | VRCons : forall s e rest, Value e -> Value rest -> Value (recExprCons s e rest).

(** Predicate: When an expression is a set of entity values *)
Inductive SetEntityValues : CedarExpr -> Prop :=
  | SEVNil : SetEntityValues setExprNil
  | SEVCons : forall uid r,
      SetEntityValues r ->
      SetEntityValues (setExprCons (lit (entityUID uid)) r).

(** Types *)

Inductive BoolType : Type :=
  | anyBool
  | tt_
  | ff_.


Inductive CedarType : Type :=
  | boolType : BoolType -> CedarType
  | intType : CedarType
  | stringType : CedarType
  | entityType : EntityName -> CedarType
  | setType : CedarType -> CedarType
  | recordTypeNil : CedarType
  | recordTypeCons : string -> bool -> CedarType -> CedarType -> CedarType.




(** Predicate: Determines whether a CedarType is a RecordType *)
Inductive RecordType : CedarType -> Prop :=
  | RTNil : RecordType recordTypeNil
  | RTCons : forall fn o T1 T2, RecordType (recordTypeCons fn o T1 T2).

(** Predicate: Name is defined in list *)
Inductive DefinedName : list EntityName -> EntityName -> Prop :=
  | DNFound : forall L A B, A = B -> DefinedName (A :: L) B
  | DNRest : forall L A B, A <> B -> DefinedName L A -> DefinedName (B :: L) A.

(** Predicate: All names in list are defined *)
Inductive DefinedNames : list EntityName -> list EntityName -> Prop :=
  | DNSNil : forall ns, DefinedNames ns nil
  | DNSCons : forall n ns0 ns, DefinedName ns n -> DefinedNames ns ns0 -> DefinedNames ns (n :: ns0).

Inductive NotInEntityNames : EntityName -> list EntityName -> Prop :=
  | NIENil : forall n,
      NotInEntityNames n nil
  | NIECons : forall n n' ns,
      n <> n' ->
      NotInEntityNames n ns ->
      NotInEntityNames n (n' :: ns).

(** Well-formedness of Cedar types *)
Inductive WfCedarType : list EntityName -> CedarType -> Prop :=
  | WfBoolType : forall ns B, WfCedarType ns (boolType B)
  | WfIntType : forall ns, WfCedarType ns intType
  | WfStringType : forall ns, WfCedarType ns stringType
  | WfEntityType : forall ns n,
      DefinedName ns n ->
      WfCedarType ns (entityType n)
  | WfSetType : forall ns T,
      WfCedarType ns T ->
      WfCedarType ns (setType T)
  | WfRecordTypeNil : forall ns, WfCedarType ns recordTypeNil
  | WfRecordTypeConsNil : forall ns fn o T1,
      WfCedarType ns T1 ->
      WfCedarType ns (recordTypeCons fn o T1 recordTypeNil)
  | WfRecordTypeConsCons : forall ns fn o T1 fn1 o1 T2 r,
      WfCedarType ns T1 ->
      WfCedarType ns (recordTypeCons fn1 o1 T2 r) ->
      WfCedarType ns (recordTypeCons fn o T1 (recordTypeCons fn1 o1 T2 r)).

(** Well-formedness of Cedar *schema* types: Bool is only ever anyBool in schemas *)
Inductive WfSchemaType : list EntityName -> CedarType -> Prop :=
  | WfSchemaBoolType : forall ns, WfSchemaType ns (boolType anyBool)
  | WfSchemaIntType : forall ns, WfSchemaType ns intType
  | WfSchemaStringType : forall ns, WfSchemaType ns stringType
  | WfSchemaEntityType : forall ns n,
      DefinedName ns n ->
      WfSchemaType ns (entityType n)
  | WfSchemaSetType : forall ns T,
      WfSchemaType ns T ->
      WfSchemaType ns (setType T)
  | WfSchemaRecordTypeNil : forall ns, WfSchemaType ns recordTypeNil
  | WfSchemaRecordTypeConsNil : forall ns fn o T1,
      WfSchemaType ns T1 ->
      WfSchemaType ns (recordTypeCons fn o T1 recordTypeNil)
  | WfSchemaRecordTypeConsCons : forall ns fn o T1 fn1 o1 T2 r,
      WfSchemaType ns T1 ->
      WfSchemaType ns (recordTypeCons fn1 o1 T2 r) ->
      WfSchemaType ns (recordTypeCons fn o T1 (recordTypeCons fn1 o1 T2 r)).

(** Well-formed record types *)
Inductive WfRecordType : list EntityName -> CedarType -> Prop :=
  | WfRecordTypeConsConsRTcons : forall ns fn' o' T1' fn1 o1 T2 r,
      WfCedarType ns (recordTypeCons fn1 o1 T2 r) ->
      WfCedarType ns T1' ->
      WfRecordType ns (recordTypeCons fn' o' T1' (recordTypeCons fn1 o1 T2 r))
  | WfRecordTypeConsNilRTcons : forall ns fn' o' T1',
      WfCedarType ns T1' ->
      WfRecordType ns (recordTypeCons fn' o' T1' recordTypeNil)
  | WfRecordTypeNilRTnil : forall ns, WfRecordType ns recordTypeNil.

(** Schemas *)

Inductive EntitySchemaEntry : Type :=
  | MkEntitySchemaEntry : list EntityName -> list (string * bool * CedarType) -> EntitySchemaEntry.


Inductive NotInAttrs : string -> list (string * bool * CedarType) -> Prop :=
  | NIANil : forall s,
      NotInAttrs s nil
  | NIACons : forall s s' b T attrs,
      s <> s' ->
      NotInAttrs s attrs ->
      NotInAttrs s ((s', b, T) :: attrs).

Inductive WfAttrs : list EntityName -> list (string * bool * CedarType) -> Prop :=
  | WfAttrsNil : forall ns, WfAttrs ns nil
  | WfAttrsCons : forall ns T s b attrs,
      WfSchemaType ns T ->
      NotInAttrs s attrs ->
      WfAttrs ns attrs ->
      WfAttrs ns ((s, b, T) :: attrs).

Inductive WfET : list EntityName -> EntitySchemaEntry -> Prop :=
  | WfETSingle : forall ns ancs attrs,
      DefinedNames ns ancs ->
      WfAttrs ns attrs ->
      WfET ns (MkEntitySchemaEntry ancs attrs).

Inductive WfETS : list EntityName -> list EntityName -> list (EntityName * EntitySchemaEntry) -> Prop :=
  | WfETSSingle : forall ns n et,
      DefinedName ns n ->
      WfET ns et ->
      WfETS ns (n :: nil) ((n, et) :: nil)
  | WfETSCons : forall ns n ns0 et ets,
      DefinedName ns n ->
      NotInEntityNames n ns0 ->
      WfET ns et ->
      WfETS ns ns0 ets ->
      WfETS ns (n :: ns0) ((n, et) :: ets).

Inductive ActionSchemaEntry : Type :=
  | MkActionSchemaEntry : list EntityName -> list EntityName -> list (string * bool * CedarType) -> ActionSchemaEntry.


Inductive WfACT : list EntityName -> (EntityUID * ActionSchemaEntry) -> Prop :=
  | WfACTSingle : forall ns p r s attrs,
      DefinedName ns p ->
      DefinedName ns r ->
      WfAttrs ns attrs ->
      WfACT ns ((MkEntityUID (MkName "Action" []) s), (MkActionSchemaEntry (p :: nil) (r :: nil) attrs)).

Inductive WfACTS : list EntityName -> list (EntityUID * ActionSchemaEntry) -> Prop :=
  | WfACTSSingle : forall ns act,
      WfACT ns act ->
      WfACTS ns (act :: nil)
  | WfACTSCons : forall ns act acts,
      WfACT ns act ->
      WfACTS ns acts ->
      WfACTS ns (act :: acts).

Inductive Schema : Type :=
  | MkSchema : list (EntityName * EntitySchemaEntry) -> list (EntityUID * ActionSchemaEntry) -> Schema.


(** Coq 8.6 compatibility for the artifact's String.eqb. *)
Definition cedar_string_eqb (x y : string) : bool :=
  if string_dec x y then true else false.

Definition actionIdOf (a : EntityUID * ActionSchemaEntry) : string :=
  match a with
  | (MkEntityUID _ id, _) => id
  end.

Fixpoint dedupActsByIdAcc
    (seen_ids : list string)
    (acts : list (EntityUID * ActionSchemaEntry))
    : list (EntityUID * ActionSchemaEntry) :=
  match acts with
  | nil => nil
  | cons a rest =>
      let id := actionIdOf a in
      if List.existsb (cedar_string_eqb id) seen_ids then
        dedupActsByIdAcc seen_ids rest
      else
        a :: dedupActsByIdAcc (id :: seen_ids) rest
  end.

Definition dedupActsById (acts : list (EntityUID * ActionSchemaEntry))
  : list (EntityUID * ActionSchemaEntry) :=
  dedupActsByIdAcc [] acts.

Inductive WfSchema : list EntityName -> Schema -> Prop :=
  | WfS : forall ns ets acts acts',
      WfETS ns ns ets ->
      WfACTS ns acts ->
      dedupActsById acts = acts' ->
      WfSchema ns (MkSchema ets acts').

Inductive DefinedEntity : list (EntityName * EntitySchemaEntry) -> EntityName -> Prop :=
  | DENow : forall n E R, DefinedEntity ((n, E) :: R) n
  | DELater : forall n n1 E R, n <> n1 -> DefinedEntity R n -> DefinedEntity ((n1, E) :: R) n.

Inductive DefinedEntities : list (EntityName * EntitySchemaEntry) -> list EntityName -> Prop :=
  | DESNil : DefinedEntities nil nil
  | DESCons : forall n ns et ets,
      DefinedEntities ets ns ->
      DefinedEntities ((n, et) :: ets) (n :: ns).

Inductive LookupEntityAttr : list (string * bool * CedarType) -> (string * bool) -> CedarType -> Prop :=
  | LUNow : forall F B FS TF, LookupEntityAttr ((F, B, TF) :: FS) (F, B) TF
  | LULater : forall F1 B1 F2 FS TF B,
      F1 <> F2 ->
      LookupEntityAttr FS (F1, B1) TF ->
      LookupEntityAttr ((F2, B, TF) :: FS) (F1, B1) TF.

Inductive GetEntityAttr : list (EntityName * EntitySchemaEntry) -> (EntityName * string * bool) -> CedarType -> Prop :=
  | GENow : forall n fn b A E R T,
      LookupEntityAttr E (fn, b) T ->
      GetEntityAttr ((n, (MkEntitySchemaEntry A E)) :: R) (n, fn, b) T
  | GELater : forall n n1 fn b E R T,
      n <> n1 ->
      GetEntityAttr R (n, fn, b) T ->
      GetEntityAttr ((n1, E) :: R) (n, fn, b) T.

(** Environments *)

Inductive RequestType : Type :=
  | MkRequest : EntityName -> EntityUID -> EntityName -> list (string * bool * CedarType) -> RequestType.


Inductive ReqContextToCedarType : list (string * bool * CedarType) -> CedarType -> Prop :=
  | RNil : ReqContextToCedarType nil recordTypeNil
  | RCons : forall i B T R TR,
      ReqContextToCedarType R TR ->
      ReqContextToCedarType ((i, B, T) :: R) (recordTypeCons i B T TR).

Inductive ActionToRequestTypes : EntityUID -> EntityName -> list EntityName -> 
    list (string * bool * CedarType) -> list RequestType -> list RequestType -> Prop :=
  | ATRTSingle : forall uid p r c acc,
      ActionToRequestTypes uid p (r :: nil) c acc ((MkRequest p uid r c) :: acc)
  | ATRTCons : forall uid p r rs c acc reqs,
      ActionToRequestTypes uid p rs c acc reqs ->
      ActionToRequestTypes uid p (r :: rs) c acc ((MkRequest p uid r c) :: reqs).

Inductive ActionSchemaEntryToRequestTypes : EntityUID -> ActionSchemaEntry -> 
    list RequestType -> list RequestType -> Prop :=
  | ASTRTSingle : forall uid p rs c acc reqs,
      ActionToRequestTypes uid p rs c acc reqs ->
      ActionSchemaEntryToRequestTypes uid (MkActionSchemaEntry (p :: nil) rs c) acc reqs
  | ASTRTCons : forall uid p ps rs c acc reqs reqs',
      ActionToRequestTypes uid p rs c acc reqs' ->
      ActionSchemaEntryToRequestTypes uid (MkActionSchemaEntry ps rs c) reqs' reqs ->
      ActionSchemaEntryToRequestTypes uid (MkActionSchemaEntry (p :: ps) rs c) acc reqs.

Inductive ActionSchemaToRequestTypes : list (EntityUID * ActionSchemaEntry) ->
    list RequestType -> list RequestType -> Prop :=
  | ASTESingle : forall uid a acc reqs,
      ActionSchemaEntryToRequestTypes uid a acc reqs ->
      ActionSchemaToRequestTypes ((uid, a) :: nil) acc reqs
  | ASTECons : forall uid a ass acc reqs' reqs,
      ActionSchemaEntryToRequestTypes uid a acc reqs' ->
      ActionSchemaToRequestTypes ass reqs' reqs ->
      ActionSchemaToRequestTypes ((uid, a) :: ass) acc reqs.

Inductive Environment : Type :=
  | MkEnvironment : Schema -> RequestType -> Environment.


Inductive SchemaToEnvironments : Schema -> list RequestType -> list Environment -> Prop :=
  | MkEnvsSingle : forall s r,
      SchemaToEnvironments s (r :: nil) ((MkEnvironment s r) :: nil)
  | MkEnvsCons : forall s r rs envs,
      SchemaToEnvironments s rs envs ->
      SchemaToEnvironments s (r :: rs) ((MkEnvironment s r) :: envs).

(** Subtyping *)

Inductive SubType : CedarType -> CedarType -> Prop :=
  | SBoolAny : forall B,
      SubType (boolType B) (boolType anyBool)
  | SSet : forall T1 T2,
      SubType T1 T2 ->
      SubType (setType T1) (setType T2)
  | SRecEmpty :
      SubType recordTypeNil recordTypeNil
  | SRecAttr : forall A o T1 T2 R1 R2,
      SubType T1 T2 ->
      RecordType R2 ->
      SubType R1 R2 ->
      RecordType R1 ->
      SubType (recordTypeCons A o T1 R1) (recordTypeCons A o T2 R2)
  | ST : forall T, SubType T T.

Inductive BranchJoin : CedarType -> CedarType -> CedarType -> Prop :=
  | BJExact : forall T,
      BranchJoin T T T
  | BJBool : forall B1 B2,
      BranchJoin (boolType B1) (boolType B2) (boolType anyBool)
  | BJSet : forall T1 T2 T,
      BranchJoin T1 T2 T ->
      BranchJoin (setType T1) (setType T2) (setType T)
  | BJRecordNil :
      BranchJoin recordTypeNil recordTypeNil recordTypeNil
  | BJRecordCons : forall k o T1 T2 T R1 R2 R,
      BranchJoin T1 T2 T ->
      BranchJoin R1 R2 R ->
      BranchJoin
        (recordTypeCons k o T1 R1)
        (recordTypeCons k o T2 R2)
        (recordTypeCons k o T R).

(** Typing: Primitives and Variables *)

Inductive HasTypePrim : Environment -> Prim -> CedarType -> Prop :=
  | TTrue : forall V, HasTypePrim V (boolean true) (boolType tt_)
  | TFalse : forall V, HasTypePrim V (boolean false) (boolType ff_)
  | TInt : forall V i, HasTypePrim V (int i) intType
  | TString : forall V s, HasTypePrim V (stringLit s) stringType
  | TEntity : forall ETS ACTS n i R,
      DefinedEntity ETS n ->
      HasTypePrim (MkEnvironment (MkSchema ETS ACTS) R) (entityUID (MkEntityUID n i)) (entityType n).

Inductive HasTypeVar : Environment -> Var -> CedarType -> Prop :=
  | TPrincipal : forall s P A R C,
      HasTypeVar (MkEnvironment s (MkRequest P A R C)) principal (entityType P)
  | TAction : forall s P i R C,
    HasTypeVar (MkEnvironment s (MkRequest P (MkEntityUID (MkName "Action" []) i) R C)) action (entityType (MkName "Action" []))
  | TResource : forall s P A R C,
      HasTypeVar (MkEnvironment s (MkRequest P A R C)) resource (entityType R)
  | TContext : forall s P A R C T,
      ReqContextToCedarType C T ->
      HasTypeVar (MkEnvironment s (MkRequest P A R C)) context T.

Inductive BindAttrType : list EntityName -> (CedarType * string * bool) -> CedarType -> Prop :=
  | BindNow : forall ns x t b r,
      WfRecordType ns r ->
      BindAttrType ns ((recordTypeCons x b t r), x, b) t
  | BindLater : forall ns x y b i t1 t r,
      x <> y ->
      WfRecordType ns r ->
      BindAttrType ns (r, x, b) t1 ->
      BindAttrType ns ((recordTypeCons y i t r), x, b) t1.

(** PathSet: Cedar typing "capability" *)
Inductive PathSet : Type :=
  | allpaths : PathSet
  | somepaths : list CedarExpr -> PathSet.

(** Compatibility helpers: transparent structural equality, no QuickChick dependency. *)
Definition entity_name_eq_dec : forall x y : EntityName, {x = y} + {x <> y}.
Proof. decide equality; auto using string_dec, list_eq_dec. Defined.
Definition entity_uid_eq_dec : forall x y : EntityUID, {x = y} + {x <> y}.
Proof. decide equality; auto using string_dec, entity_name_eq_dec. Defined.
Definition prim_eq_dec : forall x y : Prim, {x = y} + {x <> y}.
Proof. decide equality; auto using Bool.bool_dec, Z.eq_dec, string_dec, entity_uid_eq_dec. Defined.
Definition var_eq_dec : forall x y : Var, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition pat_elem_eq_dec : forall x y : PatElem, {x = y} + {x <> y}.
Proof. decide equality; apply string_dec. Defined.
Definition unary_op_eq_dec : forall x y : UnaryOp, {x = y} + {x <> y}.
Proof. decide equality; auto using entity_name_eq_dec, list_eq_dec, pat_elem_eq_dec. Defined.
Definition binary_op_eq_dec : forall x y : BinaryOp, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition cedar_expr_eq_dec : forall x y : CedarExpr, {x = y} + {x <> y}.
Proof. decide equality; auto using prim_eq_dec, var_eq_dec, unary_op_eq_dec, binary_op_eq_dec, string_dec. Defined.

(** Membership test of x in ps *)
Definition validPathExpr (x : CedarExpr) (ps : PathSet) : bool :=
  match ps with
  | allpaths => true
  | somepaths xs => existsb (fun y => if cedar_expr_eq_dec x y then true else false) xs
  end.

(** Intersect two pathsets *)
Definition interExprs (ps : PathSet) (ys : PathSet) : PathSet :=
  match ps with
  | allpaths => ys
  | somepaths xs =>
      match ys with
      | allpaths => ps
      | somepaths ys' =>
          somepaths (filter (fun x => validPathExpr x (somepaths ys')) xs)
      end
  end.

(** Remove x from list *)
Fixpoint subExprs (x : CedarExpr) (l : list CedarExpr) : list CedarExpr :=
  match l with
  | nil => nil
  | y :: ys => if cedar_expr_eq_dec x y then ys else y :: subExprs x ys
  end.

(** Union of xs and ys *)
Definition mergeExprs (xs : PathSet) (ys : PathSet) : PathSet :=
  match xs with
  | allpaths => allpaths
  | somepaths xs0 =>
      match ys with
      | allpaths => allpaths
      | somepaths ys0 =>
          let fix aux (xs : list CedarExpr) (ys : list CedarExpr) : list CedarExpr :=
            match xs with
            | nil => ys
            | x :: xs' => x :: aux xs' (subExprs x ys)
            end
          in
          somepaths (aux xs0 ys0)
      end
  end.

Inductive HasType : PathSet -> Environment -> (CedarExpr * PathSet) -> CedarType -> Prop :=
  | TLitFalse : forall a V P,
      HasTypePrim V P (boolType ff_) ->
      HasType a V ((lit P), allpaths) (boolType ff_)
  | TLitOther : forall a V P T,
      T <> (boolType ff_) ->
      HasTypePrim V P T ->
      HasType a V ((lit P), somepaths []) T
  | TVar : forall a V X T,
      HasTypeVar V X T ->
      HasType a V ((var X), somepaths []) T
  | TCondTrue : forall a V E2 E3 x2 T2,
      HasType a V (E2, x2) T2 ->
      WfExprSyntax E3 ->
      HasType a V ((ite (lit (boolean true)) E2 E3), x2) T2
  | TCondFalse : forall a V E2 E3 x3 T3,
      WfExprSyntax E2 ->
      HasType a V (E3, x3) T3 ->
      HasType a V ((ite (lit (boolean false)) E2 E3), x3) T3
  | TAnd : forall a x V E1 E2 B,
      HasType a V ((ite E1 E2 (lit (boolean false))), x) (boolType B) ->
      HasType a V ((andExpr E1 E2), x) (boolType B)
  (* | TOr : forall a x V E1 E2 T1,
      HasType a V ((ite E1 (lit (boolean true)) E2), x) T1 ->
      HasType a V ((orExpr E1 E2), x) T1 *)
  | TNotAny : forall a x V e,
      HasType a V (e, x) (boolType anyBool) ->
      HasType a V ((unaryApp not_ e), somepaths []) (boolType anyBool)
  | TNotTrue : forall a x V e,
      HasType a V (e, x) (boolType tt_) ->
      HasType a V ((unaryApp not_ e), allpaths) (boolType ff_)
  | TNotFalse : forall a x V e,
      HasType a V (e, x) (boolType ff_) ->
      HasType a V ((unaryApp not_ e), somepaths []) (boolType tt_)
  | TNeg : forall a V x e,
      HasType a V (e, x) intType ->
      HasType a V ((unaryApp neg e), somepaths []) intType
  | TLike : forall a V e x P,
      HasType a V (e, x) stringType ->
      HasType a V ((unaryApp (like P) e), somepaths []) (boolType anyBool)
  | TEqLitTrue : forall a V P T,
      HasTypePrim V P T ->
      HasType a V ((binaryApp equals (lit P) (lit P)), somepaths []) (boolType tt_)
  | TEqLitFalse : forall a V P1 P2 T1 T2,
      HasTypePrim V P1 T1 ->
      HasTypePrim V P2 T2 ->
      P1 <> P2 ->
      HasType a V ((binaryApp equals (lit P1) (lit P2)), allpaths) (boolType ff_)
  | TLessThan : forall a x1 x2 V E1 E2,
      HasType a V (E1, x1) intType ->
      HasType a V (E2, x2) intType ->
      HasType a V ((binaryApp less E1 E2), somepaths []) (boolType anyBool)
  | TLessEqualThan : forall a x1 x2 V E1 E2,
      HasType a V (E1, x1) intType ->
      HasType a V (E2, x2) intType ->
      HasType a V ((binaryApp lessEq E1 E2), somepaths []) (boolType anyBool)
  | TAdd : forall a x1 x2 V E1 E2,
      HasType a V (E1, x1) intType ->
      HasType a V (E2, x2) intType ->
      HasType a V ((binaryApp add_ E1 E2), somepaths []) intType
  | TSub : forall a x1 x2 V E1 E2,
      HasType a V (E1, x1) intType ->
      HasType a V (E2, x2) intType ->
      HasType a V ((binaryApp sub_ E1 E2), somepaths []) intType
  | TMul : forall a x1 x2 V E1 E2,
      HasType a V (E1, x1) intType ->
      HasType a V (E2, x2) intType ->
      HasType a V ((binaryApp mul_ E1 E2), somepaths []) intType
  | TRecNil : forall a V,
      HasType a V (recExprNil, somepaths []) recordTypeNil
  | TRecCons : forall a x rx V e i T R TR,
      HasType a V (e, x) T ->
      RecordType TR ->
      HasType a V (R, rx) TR ->
      WfRecSyntax R ->
      NotInRecExpr i R ->
      HasType a V ((recExprCons i e R), somepaths []) (recordTypeCons i false T TR)
  | TSetSingle : forall a x V e T,
      HasType a V (e, x) T ->
      HasType a V ((setExprCons e setExprNil), somepaths []) (setType T)
  | TSetMany : forall a x rx V e T R,
      HasType a V (e, x) T ->
      HasType a V (R, rx) (setType T) ->
      WfSetSyntax R ->
      HasType a V ((setExprCons e R), somepaths []) (setType T)
  | TIsTrue : forall a x V e n ets acts R ns,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      WfCedarType ns (entityType n) ->
      HasType a V (e, x) (entityType n) ->
      HasType a V ((unaryApp (is_ n) e), somepaths []) (boolType tt_)
  | TIsFalse : forall a x V e N1 N2 ets acts R ns,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      WfCedarType ns (entityType N1) ->
      HasType a V (e, x) (entityType N2) ->
      N1 <> N2 ->
      HasType a V ((unaryApp (is_ N1) e), allpaths) (boolType ff_)
  | TCondBool : forall a V E1 E2 E3 x1 x2 x3 T2 T3 T u,
      BranchJoin T2 T3 T ->
      HasType a V (E1, x1) (boolType anyBool) ->
      HasType (mergeExprs a x1) V (E2, x2) T2 ->
      HasType a V (E3, x3) T3 ->
      u = interExprs (mergeExprs x1 x2) x3 ->
      HasType a V ((ite E1 E2 E3), u) T
  | TEqEntity : forall a x1 x2 V E1 N1 E2 N2 ns ets acts R,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      WfCedarType ns (entityType N1) ->
      WfCedarType ns (entityType N2) ->
      N1 <> N2 ->
      HasType a V (E1, x1) (entityType N1) ->
      HasType a V (E2, x2) (entityType N2) ->
      HasType a V ((binaryApp equals E1 E2), allpaths) (boolType ff_)
  | TEqAny : forall a x1 x2 V E1 E2 T T1 T2 ets acts R ns,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      WfCedarType ns T ->
      SubType T1 T -> SubType T2 T ->
      HasType a V (E1, x1) T1 ->
      HasType a V (E2, x2) T2 ->
      HasType a V ((binaryApp equals E1 E2), somepaths []) (boolType anyBool)
  | TInEntity : forall a x1 x2 V E1 E2 N1 N2 ns ets acts R,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      WfCedarType ns (entityType N1) ->
      WfCedarType ns (entityType N2) ->
      HasType a V (E1, x1) (entityType N1) ->
      HasType a V (E2, x2) (entityType N2) ->
      HasType a V ((binaryApp mem E1 E2), somepaths []) (boolType anyBool)
  | TInEntitySet : forall a x1 x2 V E1 E2 N1 N2 ns ets acts R,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      WfCedarType ns (entityType N1) ->
      WfCedarType ns (entityType N2) ->
      HasType a V (E1, x1) (entityType N1) ->
      HasType a V (E2, x2) (setType (entityType N2)) ->
      HasType a V ((binaryApp mem E1 E2), somepaths []) (boolType anyBool)
  | TContains : forall a x1 x2 V E1 E2 ets acts R ns T1 T2 T,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      WfCedarType ns T ->
      SubType T1 T -> SubType T2 T ->
      HasType a V (E1, x1) (setType T1) ->
      HasType a V (E2, x2) T2 ->
      HasType a V ((binaryApp contains E1 E2), somepaths []) (boolType anyBool)
  | TContainsAll : forall a x1 x2 V E1 E2 ets acts R ns T1 T2 T,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      WfCedarType ns T ->
      SubType T1 T -> SubType T2 T ->
      HasType a V (E1, x1) (setType T1) ->
      HasType a V (E2, x2) (setType T2) ->
      HasType a V ((binaryApp containsAll E1 E2), somepaths []) (boolType anyBool)
  | TContainsAny : forall a x1 x2 V E1 E2 ets acts R ns T1 T2 T,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      WfCedarType ns T ->
      SubType T1 T -> SubType T2 T ->
      HasType a V (E1, x1) (setType T1) ->
      HasType a V (E2, x2) (setType T2) ->
      HasType a V ((binaryApp containsAny E1 E2), somepaths []) (boolType anyBool)
  | THasAttrRecOpt : forall a x V e F T TE ns ets acts R,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      BindAttrType ns (TE, F, true) T ->
      HasType a V (e, x) TE ->
      HasType a V ((hasAttr e F), (somepaths [getAttr e F])) (boolType anyBool)
  | THasAttrRecReq : forall a x V e F T TE ns ets acts R,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      BindAttrType ns (TE, F, false) T ->
      HasType a V (e, x) TE ->
      HasType a V ((hasAttr e F), (somepaths [getAttr e F])) (boolType tt_)
  | TGetAttrRecOpt : forall a x V e F T TE ns ets acts R,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      BindAttrType ns (TE, F, true) T ->
      HasType a V (e, x) TE ->
      validPathExpr (getAttr e F) a = true ->
      HasType a V ((getAttr e F), somepaths []) T
  | TGetAttrRecReq : forall a x V e F T TE ns ets acts R,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      DefinedEntities ets ns ->
      BindAttrType ns (TE, F, false) T ->
      HasType a V (e, x) TE ->
      HasType a V ((getAttr e F), somepaths []) T
  | THasAttrEntityOpt : forall a x V ets acts R e n fn T,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      GetEntityAttr ets (n, fn, true) T ->
      HasType a V (e, x) (entityType n) ->
      HasType a V ((hasAttr e fn), somepaths [getAttr e fn]) (boolType anyBool)
  | THasAttrEntityReq : forall a x V ets acts R e n fn T,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      GetEntityAttr ets (n, fn, false) T ->
      HasType a V (e, x) (entityType n) ->
      HasType a V ((hasAttr e fn), somepaths [getAttr e fn]) (boolType anyBool)
  | TGetAttrEntityOpt : forall a x V ets acts R e n fn T,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      GetEntityAttr ets (n, fn, true) T ->
      HasType a V (e, x) (entityType n) ->
      validPathExpr (getAttr e fn) a = true ->
      HasType a V ((getAttr e fn), somepaths []) T
  | TGetAttrEntityReq : forall a x V ets acts R e n fn T,
      V = (MkEnvironment (MkSchema ets acts) R) ->
      GetEntityAttr ets (n, fn, false) T ->
      HasType a V (e, x) (entityType n) ->
      HasType a V ((getAttr e fn), somepaths []) T.

