import SpecTecDecl0402

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$select_action:case_3:iter:0» (arg0 : (_root_.List tableMatch)) (arg1 : (_root_.List (_root_.Option _root_.Nat))) (arg2 : (_root_.List tableActionReferenceIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List (_root_.Option _root_.Nat)) × (_root_.List tableActionReferenceIR)), SpecTecCall.«$select_action:case_3:iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$select_action:case_3:iter:1» (arg0 : (_root_.List (_root_.Option _root_.Nat))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$select_action:case_3:iter:1» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$select_action:case_3:iter:2» (arg0 : (_root_.List (_root_.Option _root_.Nat))) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$select_action:case_3:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$select_action:case_3:iter:3» (arg0 : (_root_.List _root_.Nat)) (arg1 : (_root_.List tableActionReferenceIR)) (arg2 : (_root_.List (_root_.Nat × tableActionReferenceIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Nat × tableActionReferenceIR)), SpecTecCall.«$select_action:case_3:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$select_action:case_3:pattern-iter:5» (arg0 : (_root_.List (_root_.Nat × tableActionReferenceIR))) (arg1 : (_root_.List _root_.Nat)) (arg2 : (_root_.List tableActionReferenceIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR)), SpecTecCall.«$select_action:case_3:pattern-iter:5» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$select_action:case_4:iter:0» (arg0 : (_root_.List tableMatch)) (arg1 : (_root_.List (_root_.Option _root_.Nat))) (arg2 : (_root_.List tableActionReferenceIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List (_root_.Option _root_.Nat)) × (_root_.List tableActionReferenceIR)), SpecTecCall.«$select_action:case_4:iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$select_action:case_4:iter:1» (arg0 : (_root_.List (_root_.Option _root_.Nat))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$select_action:case_4:iter:1» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$select_action:case_4:iter:2» (arg0 : (_root_.List (_root_.Option _root_.Nat))) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$select_action:case_4:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$select_action:case_4:iter:3» (arg0 : (_root_.List _root_.Nat)) (arg1 : (_root_.List tableActionReferenceIR)) (arg2 : (_root_.List (_root_.Nat × tableActionReferenceIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Nat × tableActionReferenceIR)), SpecTecCall.«$select_action:case_4:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$select_action:case_4:pattern-iter:5» (arg0 : (_root_.List (_root_.Nat × tableActionReferenceIR))) (arg1 : (_root_.List _root_.Nat)) (arg2 : (_root_.List tableActionReferenceIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR)), SpecTecCall.«$select_action:case_4:pattern-iter:5» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$reverse_bytes_of_hex'» (arg0 : _root_.String) (arg1 : _root_.String) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.String, SpecTecCall.«$reverse_bytes_of_hex'» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$reverse_bytes_of_hex» (arg0 : _root_.String) (arg1 : _root_.String) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.String, SpecTecCall.«$reverse_bytes_of_hex» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$tableObject_create_entry_priority» (arg0 : tableEntryPriorityInterface) (arg1 : tableEntryPriorityOptIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntryPriorityOptIR, SpecTecCall.«$tableObject_create_entry_priority» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$needs_priority_tableKeysPropertyIR:case_1:iter:0» (arg0 : (_root_.List tableKeyIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typedExpressionIR)) (arg4 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × ((_root_.List typedExpressionIR) × (_root_.List nameIR)))), SpecTecCall.«$needs_priority_tableKeysPropertyIR:case_1:iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, arg4)))))) finalSupply


noncomputable def «$needs_priority_tableKeysPropertyIR:case_1:iter:1» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$needs_priority_tableKeysPropertyIR:case_1:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$needs_priority_tableKeysPropertyIR» (arg0 : tableKeysPropertyIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$needs_priority_tableKeysPropertyIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$tableObject_create_entry_keys:case_2:pattern-iter:0» (arg0 : (_root_.List (_root_.String × (_root_.String × typeIR)))) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$tableObject_create_entry_keys:case_2:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$tableObject_create_entry_keys:case_2:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List (_root_.String × (_root_.String × typeIR)))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × (_root_.String × typeIR))), SpecTecCall.«$tableObject_create_entry_keys:case_2:iter:3» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$interface_of_tableKeyIR» (arg0 : tableKeyIR) (arg1 : (nameIR × (nameIR × typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(nameIR × (nameIR × typeIR)), SpecTecCall.«$interface_of_tableKeyIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$key_interface_of_tableObject:case_1:iter:0» (arg0 : (_root_.List tableKeyIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$key_interface_of_tableObject:case_1:iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$key_interface_of_tableObject:case_1:iter:2» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List (_root_.String × (_root_.String × typeIR)))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × (_root_.String × typeIR))), SpecTecCall.«$key_interface_of_tableObject:case_1:iter:2» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$key_interface_of_tableObject» (arg0 : tableObject) (arg1 : (_root_.List (nameIR × (nameIR × typeIR)))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (nameIR × (nameIR × typeIR))), SpecTecCall.«$key_interface_of_tableObject» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:0» (arg0 : (_root_.List tableKeyIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$tableObject_create_entry_keyset:case_1:iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:2» (arg0 : (_root_.List tableKeyInterface)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List tableKeyValueInterface)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List tableKeyValueInterface)), SpecTecCall.«$tableObject_create_entry_keyset:case_1:iter:2» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$tableObject_create_entry_keyset:case_1:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:7» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List (_root_.String × (_root_.String × typeIR)))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × (_root_.String × typeIR))), SpecTecCall.«$tableObject_create_entry_keyset:case_1:iter:7» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:0» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List direction)) (arg2 : (_root_.List parameterInitializerOptIR)) (arg3 : (_root_.List typeIR)) (arg4 : (_root_.List annotationList)) (arg5 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List id))))), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:7» (arg0 : (_root_.List (_root_.Option nameIR))) (arg1 : (_root_.List (_root_.List nameIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List nameIR)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:7» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:6» (arg0 : (_root_.List (_root_.List (_root_.Option nameIR)))) (arg1 : (_root_.List (_root_.List (_root_.List nameIR)))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List (_root_.List nameIR))), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:6» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:9» (arg0 : (_root_.List (_root_.List (_root_.List nameIR)))) (arg1 : (_root_.List (_root_.List nameIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List nameIR)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:9» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:10» (arg0 : (_root_.List id)) (arg1 : (_root_.List (_root_.List nameIR))) (arg2 : (_root_.List (_root_.String × (_root_.List _root_.String)))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × (_root_.List _root_.String))), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:10» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:12» (arg0 : (_root_.List (_root_.List nameIR))) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:12» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
