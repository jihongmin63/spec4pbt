import SpecTecDecl0384

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$empty_typeDefEnv» (arg0 : typeDefEnv) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeDefEnv, SpecTecCall.«$empty_typeDefEnv» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$empty_callableTypeDefEnv» (arg0 : callableTypeDefEnv) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callableTypeDefEnv, SpecTecCall.«$empty_callableTypeDefEnv» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$empty_constructorTypeDefEnv» (arg0 : constructorTypeDefEnv) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constructorTypeDefEnv, SpecTecCall.«$empty_constructorTypeDefEnv» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$empty_typingContext» (arg0 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$empty_typingContext» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$enter_t» (arg0 : typingContext) (arg1 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$enter_t» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$exit_t» (arg0 : typingContext) (arg1 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$exit_t» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$set_control_t» (arg0 : typingContext) (arg1 : flow) (arg2 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$set_control_t» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$enter_loop_t» (arg0 : typingContext) (arg1 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$enter_loop_t» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$set_loop_t» (arg0 : typingContext) (arg1 : loop) (arg2 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$set_loop_t» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$add_typeParameters_t:case_1:iter:0» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeDefIR), SpecTecCall.«$add_typeParameters_t:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$add_callableDef_non_overload_t:case_1:pattern-iter:1» (arg0 : (_root_.List callTargetId)) (arg1 : (_root_.List (_root_.List id))) (arg2 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List (_root_.List id)) × (_root_.List nameIR)), SpecTecCall.«$add_callableDef_non_overload_t:case_1:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$add_callableDef_non_overload_t:case_2:pattern-iter:1» (arg0 : (_root_.List callTargetId)) (arg1 : (_root_.List (_root_.List id))) (arg2 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List (_root_.List id)) × (_root_.List nameIR)), SpecTecCall.«$add_callableDef_non_overload_t:case_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$add_constructorDef_t» (arg0 : typingContext) (arg1 : callableId) (arg2 : constructorTypeDefIR) (arg3 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_constructorDef_t» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$add_constructorDef_non_overload_t:case_1:pattern-iter:1» (arg0 : (_root_.List callTargetId)) (arg1 : (_root_.List (_root_.List id))) (arg2 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List (_root_.List id)) × (_root_.List nameIR)), SpecTecCall.«$add_constructorDef_non_overload_t:case_1:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$add_constructorDef_non_overload_t» (arg0 : typingContext) (arg1 : callableId) (arg2 : constructorTypeDefIR) (arg3 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_constructorDef_non_overload_t» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$add_constructorDefs_t» (arg0 : typingContext) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List constructorTypeDefIR)) (arg3 : typingContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typingContext, SpecTecCall.«$add_constructorDefs_t» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$empty_tableContext» (arg0 : tableContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableContext, SpecTecCall.«$empty_tableContext» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$add_key_tbl» (arg0 : tableContext) (arg1 : id) (arg2 : typeIR) (arg3 : tableContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableContext, SpecTecCall.«$add_key_tbl» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$add_action_tbl» (arg0 : tableContext) (arg1 : prefixedNameIR) (arg2 : (_root_.List parameterIR)) (arg3 : argumentListIR) (arg4 : tableContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableContext, SpecTecCall.«$add_action_tbl» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$is_lpm_key'» (arg0 : nameIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_lpm_key'» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_lpm_key» (arg0 : tableKeyIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_lpm_key» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$requires_priority'» (arg0 : nameIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$requires_priority'» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$requires_priority» (arg0 : tableKeyIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$requires_priority» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$update_mode_tbl:case_1:iter:0» (arg0 : (_root_.List tableKeyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_mode_tbl:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$update_mode_tbl:case_2:iter:0» (arg0 : (_root_.List tableKeyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_mode_tbl:case_2:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$update_mode_tbl:case_2:iter:3» (arg0 : (_root_.List tableKeyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_mode_tbl:case_2:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$update_mode_tbl:case_3:iter:0» (arg0 : (_root_.List tableKeyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_mode_tbl:case_3:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$update_mode_tbl:case_3:iter:3» (arg0 : (_root_.List tableKeyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_mode_tbl:case_3:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_action'» (arg0 : (_root_.List matchAction)) (arg1 : prefixedNameIR) (arg2 : (_root_.Option ((_root_.List parameterIR) × argumentListIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option ((_root_.List parameterIR) × argumentListIR)), SpecTecCall.«$find_action'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_action» (arg0 : tableContext) (arg1 : prefixedNameIR) (arg2 : (_root_.Option ((_root_.List parameterIR) × argumentListIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option ((_root_.List parameterIR) × argumentListIR)), SpecTecCall.«$find_action» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$set_priorities_of_tableEntryListIR:case_1:iter:0» (arg0 : (_root_.List tableEntryIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_1:iter:0» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:0» (arg0 : (_root_.List tableEntryState)) (arg1 : (_root_.List tableEntryState)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List tableEntryState), SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
