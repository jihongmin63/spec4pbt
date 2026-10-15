import SpecTecDecl0377

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$is_defaultable_typeIR:row_6:iter:0» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_defaultable_typeIR:row_6:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_defaultable_typeIR:row_9:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_defaultable_typeIR:row_9:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_defaultable_typeIR:row_10:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_defaultable_typeIR:row_10:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_defaultable_typeIR:row_11:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_defaultable_typeIR:row_11:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_equalable_typeIR» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_equalable_typeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_assignable_typeIR» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_assignable_typeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_serializable_typeIR:row_10:pattern-iter:0» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$is_serializable_typeIR:row_10:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$is_serializable_typeIR:row_11:pattern-iter:0» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$is_serializable_typeIR:row_11:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$is_serializable_typeIR:row_12:pattern-iter:0» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$is_serializable_typeIR:row_12:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$is_serializable_typeIR» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_serializable_typeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_serializable_typeIR:row_7:iter:0» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_7:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_serializable_typeIR:row_10:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_10:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_serializable_typeIR:row_11:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_11:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_serializable_typeIR:row_12:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_12:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typeIR_of_typeDefIR:case_3:iter:1» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_3:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typeIR_of_typeDefIR:case_4:iter:1» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_4:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typeIR_of_typeDefIR:case_5:iter:1» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_5:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typeIR_of_typeDefIR:case_7:pattern-iter:1» (arg0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List callableId) × (_root_.List externMethodTypeDefIR)), SpecTecCall.«$typeIR_of_typeDefIR:case_7:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$typeIR_of_typeDefIR:case_7:iter:3» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_7:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typeIR_of_typeDefIR:case_7:iter:5» (arg0 : (_root_.List callableId)) (arg1 : (_root_.List externMethodTypeDefIR)) (arg2 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId externMethodTypeDefIR)), SpecTecCall.«$typeIR_of_typeDefIR:case_7:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$typeIR_of_typeDefIR:case_8:iter:1» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_8:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typeIR_of_typeDefIR:case_9:iter:1» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_9:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typeIR_of_typeDefIR:case_10:iter:1» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_10:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$id_of_parameterIR» (arg0 : parameterIR) (arg1 : id) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨id, SpecTecCall.«$id_of_parameterIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_default_parameterIR» (arg0 : parameterIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_default_parameterIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$annotationList_of_parameterIR» (arg0 : parameterIR) (arg1 : annotationList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨annotationList, SpecTecCall.«$annotationList_of_parameterIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_actionTypeDefIR» (arg0 : actionTypeDefIR) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_actionTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_definedFunctionTypeDefIR» (arg0 : definedFunctionTypeDefIR) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_definedFunctionTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_externFunctionTypeDefIR» (arg0 : externFunctionTypeDefIR) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_externFunctionTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_parserApplyMethodTypeIR» (arg0 : parserApplyMethodTypeIR) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_parserApplyMethodTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_controlApplyMethodTypeIR» (arg0 : controlApplyMethodTypeIR) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_controlApplyMethodTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_tableApplyMethodTypeDefIR» (arg0 : tableApplyMethodTypeDefIR) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_tableApplyMethodTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
