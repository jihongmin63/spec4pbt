import SpecTecDecl0418

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$update_mode_tbl» (arg0 : tableContext) (arg1 : (_root_.List tableKeyIR)) (arg2 : tableContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableContext, SpecTecCall.«$update_mode_tbl» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def Type_wf (arg0 : bound) (arg1 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.Type_wf arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.Type_wf
scoped notation:50 x0:51 " |- " x1:51 => _root_.SpecTec.Type_wf x0 x1
end Notation.Type_wf


noncomputable def «Type_wf:tupleTypeIR:iter:3» (arg0 : bound) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:tupleTypeIR:iter:3» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_wf:structTypeIR:iter:6» (arg0 : bound) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:structTypeIR:iter:6» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_wf:headerTypeIR:iter:6» (arg0 : bound) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:headerTypeIR:iter:6» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_wf:headerUnionTypeIR:iter:6» (arg0 : bound) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:headerUnionTypeIR:iter:6» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_wf:externObjectTypeIR:iter:3» (arg0 : bound) (arg1 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:externObjectTypeIR:iter:3» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_wf:parserObjectTypeIR:iter:1» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:parserObjectTypeIR:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_wf:controlObjectTypeIR:iter:1» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:controlObjectTypeIR:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_wf:packageObjectTypeIR:iter:1» (arg0 : bound) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:packageObjectTypeIR:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_wf:non-default:iter:1» (arg0 : bound) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:non-default:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_wf:default:iter:1» (arg0 : bound) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:default:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_wf:non-default_2:iter:4» (arg0 : bound) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:non-default_2:iter:4» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_wf:default_2:iter:4» (arg0 : bound) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:default_2:iter:4» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def ParameterType_wf (arg0 : bound) (arg1 : parameterIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.ParameterType_wf arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.ParameterType_wf
scoped notation:50 x0:51 " |- " x1:51 => _root_.SpecTec.ParameterType_wf x0 x1
end Notation.ParameterType_wf


noncomputable def ReturnType_wf (arg0 : bound) (arg1 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.ReturnType_wf arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.ReturnType_wf
scoped notation:50 x0:51 " |- " x1:51 => _root_.SpecTec.ReturnType_wf x0 x1
end Notation.ReturnType_wf


noncomputable def CallableType_wf (arg0 : bound) (arg1 : callableTypeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.CallableType_wf arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.CallableType_wf
scoped notation:50 x0:51 " |- " x1:51 => _root_.SpecTec.CallableType_wf x0 x1
end Notation.CallableType_wf


noncomputable def «CallableType_wf:actionTypeIR:iter:1» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:actionTypeIR:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:1» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:definedFunctionTypeIR:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:1» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:externFunctionTypeIR:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «CallableType_wf:non-abstract:iter:1» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:non-abstract:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «CallableType_wf:abstract:iter:1» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:abstract:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «CallableType_wf:parserApplyMethodTypeIR:iter:1» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:parserApplyMethodTypeIR:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «CallableType_wf:controlApplyMethodTypeIR:iter:1» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:controlApplyMethodTypeIR:iter:1» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def CallableTypeDef_wf (arg0 : bound) (arg1 : callableTypeDefIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.CallableTypeDef_wf arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.CallableTypeDef_wf
scoped notation:50 x0:51 " |- " x1:51 => _root_.SpecTec.CallableTypeDef_wf x0 x1
end Notation.CallableTypeDef_wf


noncomputable def TypeDef_wf (arg0 : bound) (arg1 : typeDefIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.TypeDef_wf arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.TypeDef_wf
scoped notation:50 x0:51 " |- " x1:51 => _root_.SpecTec.TypeDef_wf x0 x1
end Notation.TypeDef_wf


noncomputable def ConstructorParameterType_wf (arg0 : bound) (arg1 : parameterIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.ConstructorParameterType_wf arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.ConstructorParameterType_wf
scoped notation:50 x0:51 " |- " x1:51 => _root_.SpecTec.ConstructorParameterType_wf x0 x1
end Notation.ConstructorParameterType_wf


noncomputable def «ConstructorType_wf:externObjectTypeIR:iter:0» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:externObjectTypeIR:iter:0» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «ConstructorType_wf:parserObjectTypeIR:iter:0» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:parserObjectTypeIR:iter:0» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «ConstructorType_wf:controlObjectTypeIR:iter:0» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:controlObjectTypeIR:iter:0» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «ConstructorType_wf:packageObjectTypeIR:iter:0» (arg0 : bound) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:packageObjectTypeIR:iter:0» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def ConstructorType_wf (arg0 : bound) (arg1 : constructorTypeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.ConstructorType_wf arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.ConstructorType_wf
scoped notation:50 x0:51 " |- " x1:51 => _root_.SpecTec.ConstructorType_wf x0 x1
end Notation.ConstructorType_wf

end SpecTec
