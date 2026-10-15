import SpecTecDecl0409

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «SwitchCases_general_eval:cons-fallthrough-match:iter:2» (arg0 : (_root_.List switchCaseIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«SwitchCases_general_eval:cons-fallthrough-match:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «SwitchCases_general_eval:cons-fallthrough-match-no-block:iter:2» (arg0 : (_root_.List switchCaseIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«SwitchCases_general_eval:cons-fallthrough-match-no-block:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_switchCaseList» (arg0 : switchCaseList) (arg1 : (_root_.List switchCase)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List switchCase), SpecTecCall.«$flatten_switchCaseList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_tableActionList» (arg0 : tableActionList) (arg1 : (_root_.List tableAction)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List tableAction), SpecTecCall.«$flatten_tableActionList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_largest_priority_wins» (arg0 : tableCustomPropertyIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_largest_priority_wins» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$largest_priority_wins:case_1:iter:0» (arg0 : (_root_.List tableCustomPropertyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$largest_priority_wins:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$largest_priority_wins:case_2:iter:0» (arg0 : (_root_.List tableCustomPropertyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$largest_priority_wins:case_2:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_tableEntryList» (arg0 : tableEntryList) (arg1 : (_root_.List tableEntry)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List tableEntry), SpecTecCall.«$flatten_tableEntryList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:1» (arg0 : (_root_.List tableEntryState)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:1» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$join_tableEntryState» (arg0 : tableEntryState) (arg1 : tableEntryState) (arg2 : tableEntryState) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntryState, SpecTecCall.«$join_tableEntryState» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$flatten_tableKeyList» (arg0 : tableKeyList) (arg1 : (_root_.List tableKey)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List tableKey), SpecTecCall.«$flatten_tableKeyList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$text_of_number_tableKeyValueInterface» (arg0 : tableKeyValueInterface) (arg1 : (_root_.Option _root_.String)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option _root_.String), SpecTecCall.«$text_of_number_tableKeyValueInterface» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_tableDefaultActionProperty» (arg0 : tableProperty) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_tableDefaultActionProperty» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Table_ok:zero-default-action:iter:8» (arg0 : (_root_.List tableProperty)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:zero-default-action:iter:8» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Table_ok:one-default-action:iter:8» (arg0 : (_root_.List tableProperty)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:one-default-action:iter:8» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_tableLargestPriorityWinsProperty» (arg0 : tableProperty) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_tableLargestPriorityWinsProperty» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Table_ok:zero-default-action:iter:12» (arg0 : (_root_.List tableProperty)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:zero-default-action:iter:12» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Table_ok:one-default-action:iter:12» (arg0 : (_root_.List tableProperty)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:one-default-action:iter:12» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_tableActionsProperty» (arg0 : tableProperty) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_tableActionsProperty» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Table_ok:zero-default-action:iter:4» (arg0 : (_root_.List tableProperty)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:zero-default-action:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Table_ok:one-default-action:iter:4» (arg0 : (_root_.List tableProperty)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:one-default-action:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_tableKeysProperty» (arg0 : tableProperty) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_tableKeysProperty» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Table_ok:zero-default-action:iter:0» (arg0 : (_root_.List tableProperty)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:zero-default-action:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Table_ok:one-default-action:iter:0» (arg0 : (_root_.List tableProperty)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:one-default-action:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_tablePropertyList» (arg0 : tablePropertyList) (arg1 : (_root_.List tableProperty)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List tableProperty), SpecTecCall.«$flatten_tablePropertyList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_typeFieldList» (arg0 : typeFieldList) (arg1 : (_root_.List typeField)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeField), SpecTecCall.«$flatten_typeFieldList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_aliasTypeIR» (arg0 : aliasTypeIR) (arg1 : type) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨type, SpecTecCall.«$lift_aliasTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_annotationList» (arg0 : annotationList) (arg1 : (_root_.List annotation)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List annotation), SpecTecCall.«$flatten_annotationList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$optional_annotation_of_parameterIR'» (arg0 : annotationList) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$optional_annotation_of_parameterIR'» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$optional_annotation_of_parameterIR» (arg0 : parameterIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$optional_annotation_of_parameterIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_optional_parameterIR» (arg0 : parameterIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_optional_parameterIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$match_overloaded_named:case_2:iter:5» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_named:case_2:iter:5» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
