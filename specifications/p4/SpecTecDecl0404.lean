import SpecTecDecl0403

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$alias_to_original_lookup_map:case_1:pattern-iter:15» (arg0 : (_root_.List (_root_.String × (_root_.List _root_.String)))) (arg1 : (_root_.List (_root_.List nameIR))) (arg2 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List (_root_.List nameIR)) × (_root_.List nameIR)), SpecTecCall.«$alias_to_original_lookup_map:case_1:pattern-iter:15» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:17» (arg0 : (_root_.List (_root_.List nameIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:17» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:18» (arg0 : (_root_.List (_root_.List nameIR))) (arg1 : (_root_.List _root_.String)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.String), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:18» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:21» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List (pair _root_.String _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String _root_.String)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:21» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:23» (arg0 : (_root_.List id)) (arg1 : (_root_.List (pair _root_.String _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String _root_.String)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:23» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces:case_1:pattern-iter:0» (arg0 : (_root_.List (_root_.String × _root_.Int))) (arg1 : (_root_.List _root_.Int)) (arg2 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List _root_.Int) × (_root_.List nameIR)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces:case_1:pattern-iter:3» (arg0 : (_root_.List (pair _root_.String _root_.String))) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List nameIR)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:6» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List (pair _root_.String _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String _root_.String)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List (_root_.Option nameIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option nameIR)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:5» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:9» (arg0 : (_root_.List (_root_.Option nameIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:9» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:10» (arg0 : (_root_.List (_root_.Option nameIR))) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:10» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:11» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:11» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:14» (arg0 : (_root_.List _root_.Int)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List (pair _root_.String _root_.Int))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String _root_.Int)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:14» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces':case_1:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String _root_.Int))) (arg1 : (_root_.List _root_.Int)) (arg2 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List _root_.Int) × (_root_.List id)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces':case_1:iter:2» (arg0 : (_root_.List _root_.Int)) (arg1 : (_root_.List id)) (arg2 : (_root_.List (pair _root_.String _root_.Int))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String _root_.Int)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_1:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces':case_2:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String _root_.Int))) (arg1 : (_root_.List _root_.Int)) (arg2 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List _root_.Int) × (_root_.List id)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_2:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces':case_2:iter:2» (arg0 : (_root_.List _root_.Int)) (arg1 : (_root_.List id)) (arg2 : (_root_.List (pair _root_.String _root_.Int))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String _root_.Int)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_2:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces'» (arg0 : (map id _root_.Int)) (arg1 : parameterIR) (arg2 : _root_.Int) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Int, SpecTecCall.«$align_tableActionArgumentInterfaces'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:13» (arg0 : (_root_.List _root_.Int)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List parameterIR)) (arg3 : (_root_.List _root_.Int)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Int), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:13» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$tableObject_create_entry_action:case_1:iter:2» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«$tableObject_create_entry_action:case_1:iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$tableObject_create_entry_action:case_1:iter:3» (arg0 : (_root_.List _root_.Int)) (arg1 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«$tableObject_create_entry_action:case_1:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$tableObject_create_entry_action:case_1:iter:6» (arg0 : (_root_.List (_root_.Option typedExpressionIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$tableObject_create_entry_action:case_1:iter:6» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$tableObject_create_entry_action:case_1:iter:7» (arg0 : (_root_.List (_root_.Option typedExpressionIR))) (arg1 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«$tableObject_create_entry_action:case_1:iter:7» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$tableObject_create_entry_action:case_2:iter:3» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«$tableObject_create_entry_action:case_2:iter:3» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$tableObject_create_entry_action:case_2:iter:4» (arg0 : (_root_.List _root_.Int)) (arg1 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«$tableObject_create_entry_action:case_2:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$tableObject_create_entry_action:case_2:iter:7» (arg0 : (_root_.List (_root_.Option typedExpressionIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$tableObject_create_entry_action:case_2:iter:7» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$tableObject_create_entry_action:case_2:iter:8» (arg0 : (_root_.List (_root_.Option typedExpressionIR))) (arg1 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«$tableObject_create_entry_action:case_2:iter:8» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$V1Model_meta_fields_of_index:case_1:pattern-iter:4» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List nameIR))), SpecTecCall.«$V1Model_meta_fields_of_index:case_1:pattern-iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$V1Model_meta_fields_of_index:case_1:pattern-iter:7» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List nameIR))), SpecTecCall.«$V1Model_meta_fields_of_index:case_1:pattern-iter:7» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Call_eval:controlApplyMethodCallee-copyin-exit:iter:4» (arg0 : (_root_.List actionDef)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId callableDef))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId callableDef)), SpecTecCall.«Call_eval:controlApplyMethodCallee-copyin-exit:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:controlApplyMethodCallee-localDecl-exit:iter:4» (arg0 : (_root_.List actionDef)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId callableDef))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId callableDef)), SpecTecCall.«Call_eval:controlApplyMethodCallee-localDecl-exit:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:iter:4» (arg0 : (_root_.List actionDef)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId callableDef))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId callableDef)), SpecTecCall.«Call_eval:controlApplyMethodCallee-controlBodyIR-exit:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
