import SpecTecDecl0385

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:2» (arg0 : (_root_.List tableEntryState)) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:3» (arg0 : (_root_.List tableEntryIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$set_priorities_of_tableEntryListIR:case_4:iter:1» (arg0 : (_root_.List tableEntryIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_4:iter:1» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$set_priority_of_tableEntryIR» (arg0 : tableEntryIR) (arg1 : _root_.Nat) (arg2 : tableEntryIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntryIR, SpecTecCall.«$set_priority_of_tableEntryIR» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:5» (arg0 : (_root_.List _root_.Nat)) (arg1 : (_root_.List tableEntryIR)) (arg2 : (_root_.List tableEntryIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List tableEntryIR), SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Type_wf:structTypeIR:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_wf:structTypeIR:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Type_wf:headerTypeIR:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_wf:headerTypeIR:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Type_wf:headerUnionTypeIR:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_wf:headerUnionTypeIR:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Type_wf:serializable:pattern-iter:1» (arg0 : (_root_.List valueFieldIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List value) × (_root_.List nameIR)), SpecTecCall.«Type_wf:serializable:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Type_wf:externObjectTypeIR:pattern-iter:1» (arg0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List callableId) × (_root_.List externMethodTypeDefIR)), SpecTecCall.«Type_wf:externObjectTypeIR:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Type_wf:non-default_2:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_wf:non-default_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Type_wf:default_2:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_wf:default_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «CallableType_wf:actionTypeIR:iter:4» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List direction)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR))))), SpecTecCall.«CallableType_wf:actionTypeIR:iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:4» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«CallableType_wf:definedFunctionTypeIR:iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:2» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«CallableType_wf:externFunctionTypeIR:iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «CallableType_wf:non-abstract:iter:2» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«CallableType_wf:non-abstract:iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «CallableType_wf:abstract:iter:4» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«CallableType_wf:abstract:iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «CallableType_wf:parserApplyMethodTypeIR:iter:4» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«CallableType_wf:parserApplyMethodTypeIR:iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «CallableType_wf:controlApplyMethodTypeIR:iter:4» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«CallableType_wf:controlApplyMethodTypeIR:iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «ConstructorType_wf:externObjectTypeIR:iter:3» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«ConstructorType_wf:externObjectTypeIR:iter:3» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «ConstructorType_wf:parserObjectTypeIR:iter:5» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«ConstructorType_wf:parserObjectTypeIR:iter:5» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «ConstructorType_wf:controlObjectTypeIR:iter:5» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«ConstructorType_wf:controlObjectTypeIR:iter:5» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «ConstructorType_wf:packageObjectTypeIR:iter:3» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«ConstructorType_wf:packageObjectTypeIR:iter:3» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$nestable_typedef» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_typedef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_new» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_new» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_list» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_list» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_array_in_tuple» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_array_in_tuple» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_tuple» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_tuple» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Type_wf:tupleTypeIR:iter:1» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:tupleTypeIR:iter:1» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_array» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_array» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_headerStack» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_headerStack» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_struct» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_struct» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
