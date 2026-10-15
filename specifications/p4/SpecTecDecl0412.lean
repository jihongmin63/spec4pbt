import SpecTecDecl0411

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$find_constructorDef_overloaded_t» (arg0 : typingContext) (arg1 : prefixedNameIR) (arg2 : (_root_.List argumentIR)) (arg3 : (_root_.Option (callResolution constructorTypeDefIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (callResolution constructorTypeDefIR)), SpecTecCall.«$find_constructorDef_overloaded_t» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$flatten_argumentList» (arg0 : argumentList) (arg1 : (_root_.List argument)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List argument), SpecTecCall.«$flatten_argumentList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_baseTypeIR» (arg0 : baseTypeIR) (arg1 : baseType) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨baseType, SpecTecCall.«$lift_baseTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$signature_of_builtinMethodTypeIR» (arg0 : builtinMethodTypeIR) (arg1 : ((_root_.List parameterIR) × typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List parameterIR) × typeIR), SpecTecCall.«$signature_of_builtinMethodTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def TableAction_inst (arg0 : instContext) (arg1 : store) (arg2 : tableActionIR) (arg3 : store) (arg4 : tableActionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × tableActionIR), SpecTecCall.TableAction_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableAction_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableAction_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableAction_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableAction_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableAction_inst] unexpandRelationNotation
end Notation.TableAction_inst


noncomputable def TableActions_inst (arg0 : instContext) (arg1 : store) (arg2 : (_root_.List tableActionIR)) (arg3 : store) (arg4 : (_root_.List tableActionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(store × (_root_.List tableActionIR)), SpecTecCall.TableActions_inst arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableActions_inst
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableActions_inst arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableActions_inst.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableActions_inst.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableActions_inst] unexpandRelationNotation
end Notation.TableActions_inst


noncomputable def «Constructor_call:controlConstructorDef:iter:8» (arg0 : (_root_.List callableDef)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Constructor_call:controlConstructorDef:iter:8» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$merge_externMethodDefEnvs» (arg0 : externMethodDefEnv) (arg1 : callableDefEnv) (arg2 : externMethodDefEnv) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externMethodDefEnv, SpecTecCall.«$merge_externMethodDefEnvs» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Constructor_call:externConstructorDef:iter:8» (arg0 : (_root_.List callableDef)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Constructor_call:externConstructorDef:iter:8» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$subst_typeIR':case_15:iter:7» (arg0 : (_root_.List callableTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$subst_typeIR':case_15:iter:7» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$callableTypeIR_of_callableTypeDefIR» (arg0 : callableTypeDefIR) (arg1 : callableTypeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callableTypeIR, SpecTecCall.«$callableTypeIR_of_callableTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typeParameterListIR_of_callableTypeDefIR» (arg0 : callableTypeDefIR) (arg1 : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List typeParameterIR) × (_root_.List typeParameterIR)), SpecTecCall.«$typeParameterListIR_of_callableTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_static_callableTypeIR» (arg0 : callableTypeIR) (arg1 : ctk) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨ctk, SpecTecCall.«$is_static_callableTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_static_assert_callableTypeIR» (arg0 : callableTypeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_static_assert_callableTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_constOpt» (arg0 : constOpt) (arg1 : (_root_.Option const)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option const), SpecTecCall.«$flatten_constOpt» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_constructorDef» (arg0 : constructorDef) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_constructorDef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_constructorDef_i» (arg0 : instContext) (arg1 : prefixedNameIR) (arg2 : (_root_.List argumentIR)) (arg3 : (_root_.Option (callResolution constructorDef))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (callResolution constructorDef)), SpecTecCall.«$find_constructorDef_i» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_constructorDef_e» (arg0 : evalContext) (arg1 : prefixedNameIR) (arg2 : (_root_.List argumentIR)) (arg3 : (_root_.Option (callResolution constructorDef))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (callResolution constructorDef)), SpecTecCall.«$find_constructorDef_e» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$flatten_expressionList» (arg0 : expressionList) (arg1 : (_root_.List expression)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List expression), SpecTecCall.«$flatten_expressionList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_externConstructorPrototype» (arg0 : externConstructorOrMethodPrototype) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_externConstructorPrototype» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_externMethodPrototype» (arg0 : externConstructorOrMethodPrototype) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_externMethodPrototype» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$split_externConstructorOrMethodPrototypeList:case_1:iter:1» (arg0 : (_root_.List externConstructorOrMethodPrototype)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$split_externConstructorOrMethodPrototypeList:case_1:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$split_externConstructorOrMethodPrototypeList:case_1:iter:6» (arg0 : (_root_.List externConstructorOrMethodPrototype)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$split_externConstructorOrMethodPrototypeList:case_1:iter:6» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$split_externConstructorOrMethodPrototypeList» (arg0 : externConstructorOrMethodPrototypeList) (arg1 : ((_root_.List externConstructorPrototype) × (_root_.List externMethodPrototype))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List externConstructorPrototype) × (_root_.List externMethodPrototype)), SpecTecCall.«$split_externConstructorOrMethodPrototypeList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_forInitStatementList» (arg0 : forInitStatementList) (arg1 : (_root_.List forInitStatement)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List forInitStatement), SpecTecCall.«$flatten_forInitStatementList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_forUpdateStatementList» (arg0 : forUpdateStatementList) (arg1 : (_root_.List forUpdateStatement)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List forUpdateStatement), SpecTecCall.«$flatten_forUpdateStatementList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_functionDef» (arg0 : functionDef) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_functionDef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_functionTypeDefIR» (arg0 : functionTypeDefIR) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_functionTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$width_of_integerTypeIR» (arg0 : integerTypeIR) (arg1 : (_root_.Option _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option _root_.Nat), SpecTecCall.«$width_of_integerTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$int_of_integerValue» (arg0 : integerValue) (arg1 : _root_.Int) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Int, SpecTecCall.«$int_of_integerValue» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nat_of_integerValue» (arg0 : integerValue) (arg1 : (_root_.Option _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option _root_.Nat), SpecTecCall.«$nat_of_integerValue» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$set_priorities_of_tableEntryListIR'» (arg0 : tableContext) (arg1 : _root_.Nat) (arg2 : (_root_.List tableEntryIR)) (arg3 : (_root_.List tableEntryIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List tableEntryIR), SpecTecCall.«$set_priorities_of_tableEntryListIR'» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

end SpecTec
