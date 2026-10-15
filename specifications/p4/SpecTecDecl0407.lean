import SpecTecDecl0406

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Cast_impl_neq:sequenceTypeIR:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:sequenceTypeIR:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:4» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:tupleTypeIR_2:iter:4» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:arrayTypeIR_2:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:arrayTypeIR_2:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:headerStackTypeIR_2:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerStackTypeIR_2:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_2:iter:6» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:structTypeIR_2:iter:6» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_3:iter:6» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerTypeIR_3:iter:6» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:21» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:structTypeIR_3:iter:21» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_4:iter:21» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerTypeIR_4:iter:21» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_4:iter:21» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:structTypeIR_4:iter:21» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_5:iter:21» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerTypeIR_5:iter:21» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$flatten_controlLocalDeclarationList» (arg0 : controlLocalDeclarationList) (arg1 : (_root_.List controlLocalDeclaration)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List controlLocalDeclaration), SpecTecCall.«$flatten_controlLocalDeclarationList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$join_ctk» (arg0 : ctk) (arg1 : ctk) (arg2 : ctk) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨ctk, SpecTecCall.«$join_ctk» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$joins_ctk» (arg0 : (_root_.List ctk)) (arg1 : ctk) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨ctk, SpecTecCall.«$joins_ctk» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$add_callableDef_overload_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : callableId) (arg3 : callableTypeDefIR) (arg4 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_callableDef_overload_t» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_callableDef_non_overload_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : callableId) (arg3 : callableTypeDefIR) (arg4 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_callableDef_non_overload_t» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_typeDef_i» (arg0 : cursor) (arg1 : instContext) (arg2 : typeId) (arg3 : typeDefIR) (arg4 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$add_typeDef_i» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_callableDef_overload_i» (arg0 : cursor) (arg1 : instContext) (arg2 : callableId) (arg3 : callableDef) (arg4 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$add_callableDef_overload_i» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_callableDef_non_overload_i» (arg0 : cursor) (arg1 : instContext) (arg2 : callableId) (arg3 : callableDef) (arg4 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$add_callableDef_non_overload_i» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def FuncDecl_inst (arg0 : cursor) (arg1 : instContext) (arg2 : functionDeclarationIR) (arg3 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.FuncDecl_inst arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.FuncDecl_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.FuncDecl_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.FuncDecl_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.FuncDecl_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.FuncDecl_inst] unexpandRelationNotation
end Notation.FuncDecl_inst


noncomputable def ActionDecl_inst (arg0 : cursor) (arg1 : instContext) (arg2 : actionDeclarationIR) (arg3 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.ActionDecl_inst arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.ActionDecl_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ActionDecl_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ActionDecl_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.ActionDecl_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ActionDecl_inst] unexpandRelationNotation
end Notation.ActionDecl_inst


noncomputable def «$bound» (arg0 : cursor) (arg1 : typingContext) (arg2 : bound) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨bound, SpecTecCall.«$bound» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$add_typeDef_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : typeId) (arg3 : typeDefIR) (arg4 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_typeDef_t» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_typeDefs_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : (_root_.List typeId)) (arg3 : (_root_.List typeDefIR)) (arg4 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_typeDefs_t» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_typeParameters_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : (_root_.List typeId)) (arg3 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_typeParameters_t» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$instantiable_extern» (arg0 : cursor) (arg1 : typingContext) (arg2 : instctxt) (arg3 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$instantiable_extern» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$instantiable_parser» (arg0 : cursor) (arg1 : typingContext) (arg2 : instctxt) (arg3 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$instantiable_parser» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$instantiable_control» (arg0 : cursor) (arg1 : typingContext) (arg2 : instctxt) (arg3 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$instantiable_control» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$instantiable_package» (arg0 : cursor) (arg1 : typingContext) (arg2 : instctxt) (arg3 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$instantiable_package» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$instantiable_table» (arg0 : cursor) (arg1 : typingContext) (arg2 : instctxt) (arg3 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$instantiable_table» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$callable_action» (arg0 : cursor) (arg1 : typingContext) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$callable_action» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$callable_externFunction» (arg0 : cursor) (arg1 : typingContext) (arg2 : nameIR) (arg3 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$callable_externFunction» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$callable_externMethod» (arg0 : cursor) (arg1 : typingContext) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$callable_externMethod» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
