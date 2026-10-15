import SpecTecDecl0417

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$subst_callableTypeDefIR':case_5:iter:3» (arg0 : theta) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$subst_callableTypeDefIR':case_5:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$subst_callableTypeIR» (arg0 : theta) (arg1 : callableTypeIR) (arg2 : callableTypeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callableTypeIR, SpecTecCall.«$subst_callableTypeIR» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$subst_constructorTypeIR':case_1:iter:0» (arg0 : theta) (arg1 : (_root_.List constructorParameterIR)) (arg2 : (_root_.List constructorParameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List constructorParameterIR), SpecTecCall.«$subst_constructorTypeIR':case_1:iter:0» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$subst_constructorTypeIR'» (arg0 : theta) (arg1 : constructorTypeIR) (arg2 : constructorTypeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constructorTypeIR, SpecTecCall.«$subst_constructorTypeIR'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$subst_constructorTypeIR» (arg0 : theta) (arg1 : constructorTypeIR) (arg2 : constructorTypeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constructorTypeIR, SpecTecCall.«$subst_constructorTypeIR» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$specialize_typeDefIR» (arg0 : typeDefIR) (arg1 : (_root_.List typeIR)) (arg2 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$specialize_typeDefIR» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$specialize_callableTypeDefIR» (arg0 : callableTypeDefIR) (arg1 : (_root_.List typeIR)) (arg2 : (callableTypeIR × (_root_.List typeId))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(callableTypeIR × (_root_.List typeId)), SpecTecCall.«$specialize_callableTypeDefIR» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$specialize_constructorTypeDefIR» (arg0 : constructorTypeDefIR) (arg1 : (_root_.List typeIR)) (arg2 : (constructorTypeIR × (_root_.List typeId))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(constructorTypeIR × (_root_.List typeId)), SpecTecCall.«$specialize_constructorTypeDefIR» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def Type_alpha (arg0 : typeIR) (arg1 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.Type_alpha arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.Type_alpha
scoped notation:50 x0:51 " ~~ " x1:51 => _root_.SpecTec.Type_alpha x0 x1
end Notation.Type_alpha


noncomputable def «Type_alpha:tupleTypeIR:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:tupleTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:structTypeIR:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:structTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:headerTypeIR:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:headerTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:headerUnionTypeIR:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:headerUnionTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:externObjectTypeIR:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:externObjectTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:parserObjectTypeIR:iter:2» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:parserObjectTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:controlObjectTypeIR:iter:2» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:controlObjectTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:packageObjectTypeIR:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:packageObjectTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:non-default:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:non-default:iter:2» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:default:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:default:iter:2» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:non-default_2:iter:8» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:non-default_2:iter:8» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Type_alpha:default_2:iter:8» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:default_2:iter:8» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def ParameterType_alpha (arg0 : parameterIR) (arg1 : parameterIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.ParameterType_alpha arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.ParameterType_alpha
scoped notation:50 x0:51 " ~~ " x1:51 => _root_.SpecTec.ParameterType_alpha x0 x1
end Notation.ParameterType_alpha


noncomputable def «ExternMethodType_alpha:non-abstract:iter:0» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ExternMethodType_alpha:non-abstract:iter:0» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «ExternMethodType_alpha:abstract:iter:0» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ExternMethodType_alpha:abstract:iter:0» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def ExternMethodType_alpha (arg0 : externMethodTypeIR) (arg1 : externMethodTypeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.ExternMethodType_alpha arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.ExternMethodType_alpha
scoped notation:50 x0:51 " ~~ " x1:51 => _root_.SpecTec.ExternMethodType_alpha x0 x1
end Notation.ExternMethodType_alpha


noncomputable def ExternMethodTypeDef_alpha (arg0 : externMethodTypeDefIR) (arg1 : externMethodTypeDefIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.ExternMethodTypeDef_alpha arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.ExternMethodTypeDef_alpha
scoped notation:50 x0:51 " ~~ " x1:51 => _root_.SpecTec.ExternMethodTypeDef_alpha x0 x1
end Notation.ExternMethodTypeDef_alpha


noncomputable def «$add_var_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : id) (arg3 : varTypeIR) (arg4 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_var_t» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_vars_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : (_root_.List id)) (arg3 : (_root_.List varTypeIR)) (arg4 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_vars_t» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$add_parameter_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : parameterIR) (arg3 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_parameter_t» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$add_parameters_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : (_root_.List parameterIR)) (arg3 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_parameters_t» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$add_constructorParameter_t» (arg0 : typingContext) (arg1 : parameterIR) (arg2 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_constructorParameter_t» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$add_constructorParameters_t» (arg0 : typingContext) (arg1 : (_root_.List parameterIR)) (arg2 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_constructorParameters_t» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
