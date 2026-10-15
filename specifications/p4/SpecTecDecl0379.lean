import SpecTecDecl0378

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$parameterListIR_of_constructorTypeDefIR» (arg0 : constructorTypeDefIR) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_constructorTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_9:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$free_typeIR:case_9:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$free_typeIR:case_10:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$free_typeIR:case_10:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$free_typeIR:case_11:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$free_typeIR:case_11:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$free_typeIR:case_14:pattern-iter:1» (arg0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List callableId) × (_root_.List externMethodTypeDefIR)), SpecTecCall.«$free_typeIR:case_14:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$free_typeIR:case_23:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$free_typeIR:case_23:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$free_typeIR:case_24:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$free_typeIR:case_24:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$empty_theta» (arg0 : theta) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨theta, SpecTecCall.«$empty_theta» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$capture_avoiding_:case_1:iter:0» (arg0 : theta) (arg1 : (_root_.List typeId)) (arg2 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«$capture_avoiding_:case_1:iter:0» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$capture_avoiding_:case_1:iter:2» (arg0 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$capture_avoiding_:case_1:iter:2» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$capture_avoiding_:case_1:iter:3» (arg0 : (_root_.List (_root_.Option typeIR))) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding_:case_1:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$capture_avoiding_:case_1:iter:10» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding_:case_1:iter:10» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$capture_avoiding:case_1:iter:0» (arg0 : theta) (arg1 : (_root_.List typeId)) (arg2 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«$capture_avoiding:case_1:iter:0» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$capture_avoiding:case_1:iter:2» (arg0 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$capture_avoiding:case_1:iter:2» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$capture_avoiding:case_1:iter:3» (arg0 : (_root_.List (_root_.Option typeIR))) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding:case_1:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$capture_avoiding:case_1:iter:10» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding:case_1:iter:10» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$capture_avoiding:case_1:iter:12» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding:case_1:iter:12» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subst_typeIR':case_10:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$subst_typeIR':case_10:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$subst_typeIR':case_10:iter:7» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$subst_typeIR':case_10:iter:7» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$subst_typeIR':case_11:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$subst_typeIR':case_11:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$subst_typeIR':case_11:iter:7» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$subst_typeIR':case_11:iter:7» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$subst_typeIR':case_12:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$subst_typeIR':case_12:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$subst_typeIR':case_12:iter:7» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$subst_typeIR':case_12:iter:7» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$subst_typeIR':case_15:pattern-iter:1» (arg0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List callableId) × (_root_.List externMethodTypeDefIR)), SpecTecCall.«$subst_typeIR':case_15:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$subst_typeIR':case_15:iter:8» (arg0 : (_root_.List callableTypeDefIR)) (arg1 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List externMethodTypeDefIR), SpecTecCall.«$subst_typeIR':case_15:iter:8» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subst_typeIR':case_15:iter:10» (arg0 : (_root_.List callableId)) (arg1 : (_root_.List externMethodTypeDefIR)) (arg2 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId externMethodTypeDefIR)), SpecTecCall.«$subst_typeIR':case_15:iter:10» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$subst_typeIR':case_24:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$subst_typeIR':case_24:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$subst_typeIR':case_24:iter:5» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List id)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$subst_typeIR':case_24:iter:5» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$subst_typeIR':case_25:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$subst_typeIR':case_25:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$subst_typeIR':case_25:iter:5» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List id)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$subst_typeIR':case_25:iter:5» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$specialize_typeDefIR:case_1:iter:1» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_typeDefIR:case_1:iter:1» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$specialize_callableTypeDefIR:case_1:iter:2» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«$specialize_callableTypeDefIR:case_1:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
