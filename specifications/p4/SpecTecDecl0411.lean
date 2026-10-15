import SpecTecDecl0410

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$match_overloaded_named:case_2:iter:14» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_named:case_2:iter:14» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$match_overloaded_named» (V_T : Type) (arg0 : (pair callTargetId V_T)) (arg1 : namedCallTargetKey) (arg2 : (V_T → (SpecTecCall parameterListIR))) (arg3 : callTargetMatch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callTargetMatch, SpecTecCall.«$match_overloaded_named» V_T arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$match_overloaded_unnamed:case_1:iter:3» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_unnamed:case_1:iter:3» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$match_overloaded_unnamed:case_2:iter:3» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_unnamed:case_2:iter:3» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$match_overloaded_unnamed:case_2:iter:8» (V_T : Type) (arg0 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$match_overloaded_unnamed:case_2:iter:8» V_T arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$match_overloaded_unnamed:case_3:iter:3» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_unnamed:case_3:iter:3» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$match_overloaded_unnamed:case_3:iter:10» (V_T : Type) (arg0 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$match_overloaded_unnamed:case_3:iter:10» V_T arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$match_overloaded_unnamed» (V_T : Type) (arg0 : (pair callTargetId V_T)) (arg1 : unnamedCallTargetKey) (arg2 : (V_T → (SpecTecCall parameterListIR))) (arg3 : callTargetMatch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callTargetMatch, SpecTecCall.«$match_overloaded_unnamed» V_T arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_overloadeds_named» (V : Type) (arg0 : (map callableId V)) (arg1 : namedCallTargetKey) (arg2 : (V → (SpecTecCall parameterListIR))) (arg3 : (_root_.List (callResolution V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (callResolution V)), SpecTecCall.«$find_overloadeds_named» V arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_overloadeds_unnamed» (V : Type) (arg0 : (map callableId V)) (arg1 : unnamedCallTargetKey) (arg2 : (V → (SpecTecCall parameterListIR))) (arg3 : (_root_.List (callResolution V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (callResolution V)), SpecTecCall.«$find_overloadeds_unnamed» V arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_overloaded» (V_T : Type) (arg0 : (map callTargetId V_T)) (arg1 : callTargetKey) (arg2 : (V_T → (SpecTecCall parameterListIR))) (arg3 : (_root_.Option (callResolution V_T))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (callResolution V_T)), SpecTecCall.«$find_overloaded» V_T arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$name_annotation» (arg0 : annotationList) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«$name_annotation» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$name_annotation_default» (arg0 : annotationList) (arg1 : nameIR) (arg2 : nameIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨nameIR, SpecTecCall.«$name_annotation_default» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_name_annotation_opt» (arg0 : annotationList) (arg1 : (_root_.Option annotation)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option annotation), SpecTecCall.«$find_name_annotation_opt» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$add_annotationList» (arg0 : annotationList) (arg1 : (_root_.Option annotation)) (arg2 : annotationList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨annotationList, SpecTecCall.«$add_annotationList» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «CallableType_wf:actionTypeIR:iter:2» (arg0 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:actionTypeIR:iter:2» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:2» (arg0 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:definedFunctionTypeIR:iter:2» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «CallableType_wf:abstract:iter:2» (arg0 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:abstract:iter:2» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «CallableType_wf:parserApplyMethodTypeIR:iter:2» (arg0 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:parserApplyMethodTypeIR:iter:2» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «CallableType_wf:controlApplyMethodTypeIR:iter:2» (arg0 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:controlApplyMethodTypeIR:iter:2» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «ConstructorType_wf:parserObjectTypeIR:iter:1» (arg0 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:parserObjectTypeIR:iter:1» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «ConstructorType_wf:controlObjectTypeIR:iter:1» (arg0 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:controlObjectTypeIR:iter:1» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:1» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List (_root_.List annotation))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List annotation)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$alias_to_original_lookup_map» (arg0 : (_root_.List parameterIR)) (arg1 : (map nameIR nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(map nameIR nameIR), SpecTecCall.«$alias_to_original_lookup_map» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List tableActionArgumentInterface)) (arg2 : (_root_.List _root_.Int)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Int), SpecTecCall.«$align_tableActionArgumentInterfaces» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$field_list_annotation_index'» (arg0 : annotation) (arg1 : (_root_.Option integerLiteral)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option integerLiteral), SpecTecCall.«$field_list_annotation_index'» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$field_list_annotation_index:case_1:iter:1» (arg0 : (_root_.List annotation)) (arg1 : (_root_.List (_root_.Option integerLiteral))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option integerLiteral)), SpecTecCall.«$field_list_annotation_index:case_1:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$align_parameterListIR_given» (arg0 : (map id parameterIR)) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List argumentIR)) (arg3 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$align_parameterListIR_given» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$align_parameterListIR» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List argumentIR)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List nameIR)) (arg4 : callAlign) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callAlign, SpecTecCall.«$align_parameterListIR» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$callTargetKey'» (arg0 : argumentIR) (arg1 : (_root_.Option id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option id), SpecTecCall.«$callTargetKey'» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$callTargetKey:case_1:iter:0» (arg0 : (_root_.List argumentIR)) (arg1 : (_root_.List (_root_.Option id))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option id)), SpecTecCall.«$callTargetKey:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$callTargetKey» (arg0 : nameIR) (arg1 : argumentListIR) (arg2 : callTargetKey) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callTargetKey, SpecTecCall.«$callTargetKey» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
