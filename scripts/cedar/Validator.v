(** Bounded, kernel-checked proof search for the five original Cedar premises.
    The Python driver defines a transparent [option ({P}+{~P})] for each
    premise.  Its computed tag depends on the retained proof constructor.
    Search failure never counts as evidence of falsity. *)
Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.

Create HintDb cedar_validator.
(** Every inductive proposition of Spec.v.  [Hint Constructors] on one member
    of a mutual block adds only that member's constructors, so WfSetSyntax and
    WfRecSyntax are listed separately from WfExprSyntax.  Without them no
    record with a field and no set with two or more elements was provable. *)
Hint Constructors
  DefinedName DefinedNames NotInEntityNames WfCedarType WfSchemaType
  WfRecordType NotInAttrs WfAttrs WfET WfETS WfACT WfACTS WfSchema
  ReqContextToCedarType ActionToRequestTypes
  ActionSchemaEntryToRequestTypes ActionSchemaToRequestTypes
  SchemaToEnvironments HasTypePrim HasTypeVar HasType
  RecordType RecordExpr SetExpr WfExprSyntax WfSetSyntax WfRecSyntax
  Value SetEntityValues SubType BranchJoin BindAttrType
  DefinedEntity DefinedEntities LookupEntityAttr GetEntityAttr NotInRecExpr
  : cedar_validator.
Hint Extern 1 (_ <> _) => congruence : cedar_validator.
Hint Extern 1 (_ = _) => reflexivity : cedar_validator.

(** Depth 30: a two-entity schema with attributes needs more than 12 nested
    constructor applications under WfETS, so depth 12 failed quickly on
    well-formed P0 schemas. *)
Ltac cedar_prove :=
  solve [
    cbv;
    first [
      lazymatch goal with
      | |- WfSchema ?ns (MkSchema ?ets ?ac) =>
          eapply (WfS ns ets ac ac);
          [eauto 30 with cedar_validator
          |eauto 30 with cedar_validator
          |reflexivity]
      end
    | eauto 30 with cedar_validator
    ]
  ].

Ltac cedar_disprove :=
  solve [
    cbv;
    intro H;
    repeat (match goal with
      | H : WfSchema _ _ |- False => inversion H; clear H; subst
      | H : WfETS _ _ _ |- False => inversion H; clear H; subst
      | H : WfACTS _ _ |- False => inversion H; clear H; subst
      | H : ActionSchemaToRequestTypes _ _ _ |- False => inversion H; clear H; subst
      | H : ActionSchemaEntryToRequestTypes _ _ _ _ |- False => inversion H; clear H; subst
      | H : ActionToRequestTypes _ _ _ _ _ _ |- False => inversion H; clear H; subst
      | H : SchemaToEnvironments _ _ _ |- False => inversion H; clear H; subst
      | H : WfCedarType _ _ |- False => inversion H; clear H; subst
      | H : DefinedName _ _ |- False => inversion H; clear H; subst
      | H : HasType _ _ _ _ |- False => inversion H; clear H; subst
      | H : HasTypePrim _ _ _ |- False => inversion H; clear H; subst
      | H : HasTypeVar _ _ _ |- False => inversion H; clear H; subst
      end);
    congruence
  ].

(** Both proof searches have a one-second tactic timeout. *)
Ltac cedar_verdict :=
  first [
    refine (Some (left _)); timeout 1 cedar_prove
  | refine (Some (right _)); timeout 1 cedar_disprove
  | exact None
  ].

Definition cedar_verdict_tag {P : Prop} (v : option ({P}+{~P})) : string :=
  match v with
  | Some (left _) => "valid"
  | Some (right _) => "invalid"
  | None => "unknown"
  end.
