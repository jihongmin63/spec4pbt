import SpecTecDecl0379

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$specialize_callableTypeDefIR:case_1:iter:3» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_callableTypeDefIR:case_1:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$specialize_callableTypeDefIR:case_1:iter:5» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_callableTypeDefIR:case_1:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$specialize_callableTypeDefIR:case_2:iter:2» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«$specialize_callableTypeDefIR:case_2:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$specialize_callableTypeDefIR:case_2:iter:3» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_callableTypeDefIR:case_2:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:1» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«$specialize_constructorTypeDefIR:case_1:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_constructorTypeDefIR:case_1:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:4» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_constructorTypeDefIR:case_1:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$specialize_constructorTypeDefIR:case_2:iter:1» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«$specialize_constructorTypeDefIR:case_2:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$specialize_constructorTypeDefIR:case_2:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_constructorTypeDefIR:case_2:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Type_alpha:non-default_2:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_alpha:non-default_2:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Type_alpha:non-default_2:pattern-iter:4» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List annotationList)) (arg3 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List nameIR))), SpecTecCall.«Type_alpha:non-default_2:pattern-iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Type_alpha:default_2:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_alpha:default_2:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Type_alpha:default_2:pattern-iter:4» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List annotationList)) (arg3 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List nameIR))), SpecTecCall.«Type_alpha:default_2:pattern-iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «ExternMethodTypeDef_alpha:rule:iter:3» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«ExternMethodTypeDef_alpha:rule:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «ExternMethodTypeDef_alpha:rule:iter:9» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«ExternMethodTypeDef_alpha:rule:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$default:case_13:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$default:case_13:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$default:case_14:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$default:case_14:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$default:case_15:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$default:case_15:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$cast_sequence:case_7:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$cast_sequence:case_7:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$cast_sequence:case_8:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$cast_sequence:case_8:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$cast_sequence:case_13:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$cast_sequence:case_13:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$cast_sequence:case_14:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$cast_sequence:case_14:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$cast_record:case_1:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_1:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$cast_record:case_2:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$cast_record:case_3:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_3:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$cast_record:case_4:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_4:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$cast_record:case_5:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_5:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$cast_record:case_6:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_6:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$sizeof_minSizeInBits':case_11:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$sizeof_minSizeInBits':case_11:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$sizeof_minSizeInBits':case_12:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$sizeof_minSizeInBits':case_12:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$sizeof_minSizeInBits':case_13:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$sizeof_minSizeInBits':case_13:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$sizeof_maxSizeInBits':case_11:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$sizeof_maxSizeInBits':case_11:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply

end SpecTec
