import SpecTecDecl0407

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$callable_parserApplyMethod» (arg0 : cursor) (arg1 : typingContext) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$callable_parserApplyMethod» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$callable_controlApplyMethod» (arg0 : cursor) (arg1 : typingContext) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$callable_controlApplyMethod» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$callable_tableApplyMethod» (arg0 : cursor) (arg1 : typingContext) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$callable_tableApplyMethod» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$inherit_i» (arg0 : cursor) (arg1 : instContext) (arg2 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$inherit_i» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$add_var_i» (arg0 : cursor) (arg1 : instContext) (arg2 : id) (arg3 : value) (arg4 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$add_var_i» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_vars_i» (arg0 : cursor) (arg1 : instContext) (arg2 : (_root_.List id)) (arg3 : (_root_.List value)) (arg4 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$add_vars_i» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_type_i» (arg0 : cursor) (arg1 : instContext) (arg2 : typeId) (arg3 : typeIR) (arg4 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$add_type_i» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_types_i» (arg0 : cursor) (arg1 : instContext) (arg2 : (_root_.List typeId)) (arg3 : (_root_.List typeIR)) (arg4 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$add_types_i» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def ConstDecl_inst (arg0 : cursor) (arg1 : instContext) (arg2 : constantDeclarationIR) (arg3 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.ConstDecl_inst arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.ConstDecl_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ConstDecl_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ConstDecl_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.ConstDecl_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ConstDecl_inst] unexpandRelationNotation
end Notation.ConstDecl_inst


noncomputable def «$inherit_e» (arg0 : cursor) (arg1 : evalContext) (arg2 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.«$inherit_e» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$copy_e» (arg0 : cursor) (arg1 : evalContext) (arg2 : evalContext) (arg3 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.«$copy_e» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_type_e» (arg0 : cursor) (arg1 : evalContext) (arg2 : nameIR) (arg3 : (_root_.Option typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option typeIR), SpecTecCall.«$find_type_e» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$directionless_trailing'» (arg0 : _root_.Bool) (arg1 : (_root_.List direction)) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$directionless_trailing'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$directionless_trailing» (arg0 : (_root_.List direction)) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$directionless_trailing» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$split_dataplane_parameters» (arg0 : (_root_.List parameterIR)) (arg1 : ((_root_.List parameterIR) × (_root_.List parameterIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List parameterIR) × (_root_.List parameterIR)), SpecTecCall.«$split_dataplane_parameters» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_externConstructorOrMethodPrototypeList» (arg0 : externConstructorOrMethodPrototypeList) (arg1 : (_root_.List externConstructorOrMethodPrototype)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List externConstructorOrMethodPrototype), SpecTecCall.«$flatten_externConstructorOrMethodPrototypeList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_externMethodDef» (arg0 : externMethodDef) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_externMethodDef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$type_of_externMethodPrototypeIR» (arg0 : externMethodPrototypeIR) (arg1 : externMethodTypeDefIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externMethodTypeDefIR, SpecTecCall.«$type_of_externMethodPrototypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:externObjectDeclaration:iter:7» (arg0 : (_root_.List externMethodPrototypeIR)) (arg1 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List externMethodTypeDefIR), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:7» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def ExternMethod_inst (arg0 : instContext) (arg1 : externMethodPrototypeIR) (arg2 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.ExternMethod_inst arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.ExternMethod_inst
scoped notation:50 x0:51 " |- " x1:51 " : " x2:51 => _root_.SpecTec.ExternMethod_inst x0 x1 x2
end Notation.ExternMethod_inst


noncomputable def ExternMethods_inst (arg0 : instContext) (arg1 : (_root_.List externMethodPrototypeIR)) (arg2 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.ExternMethods_inst arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.ExternMethods_inst
scoped notation:50 x0:51 " |- " x1:51 " : " x2:51 => _root_.SpecTec.ExternMethods_inst x0 x1 x2
end Notation.ExternMethods_inst


noncomputable def «Decl_inst:non-constructor:iter:3» (arg0 : (_root_.List externMethodPrototypeIR)) (arg1 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List externMethodTypeDefIR), SpecTecCall.«Decl_inst:non-constructor:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_inst:constructor:iter:3» (arg0 : (_root_.List externMethodPrototypeIR)) (arg1 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List externMethodTypeDefIR), SpecTecCall.«Decl_inst:constructor:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$callableId_of_externMethodPrototypeIR» (arg0 : externMethodPrototypeIR) (arg1 : callableId) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callableId, SpecTecCall.«$callableId_of_externMethodPrototypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_inst:non-constructor:iter:1» (arg0 : (_root_.List externMethodPrototypeIR)) (arg1 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List callableId), SpecTecCall.«Decl_inst:non-constructor:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_inst:constructor:iter:1» (arg0 : (_root_.List externMethodPrototypeIR)) (arg1 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List callableId), SpecTecCall.«Decl_inst:constructor:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_concrete_extern_object''» (arg0 : externMethodTypeDefIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_concrete_extern_object''» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_concrete_extern_object':case_2:iter:3» (arg0 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$is_concrete_extern_object':case_2:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$parameterListIR_of_externMethodTypeDefIR» (arg0 : externMethodTypeDefIR) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_externMethodTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$join_flow» (arg0 : flow) (arg1 : flow) (arg2 : flow) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨flow, SpecTecCall.«$join_flow» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$join_control_t» (arg0 : typingContext) (arg1 : typingContext) (arg2 : flow) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨flow, SpecTecCall.«$join_control_t» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$resolve_constraint» (arg0 : strictness) (arg1 : constraint) (arg2 : inference) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨inference, SpecTecCall.«$resolve_constraint» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
