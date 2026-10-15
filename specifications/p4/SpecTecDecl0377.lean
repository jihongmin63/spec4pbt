import SpecTecDecl0376

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$cast_record:case_2:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_record:case_2:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$cast_record:case_2:iter:6» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (pair _root_.String value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String value)), SpecTecCall.«$cast_record:case_2:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record:case_2:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option value)), SpecTecCall.«$cast_record:case_2:iter:5» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$cast_record:case_2:iter:9» (arg0 : (_root_.List (_root_.Option value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$cast_record:case_2:iter:9» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$cast_record:case_2:iter:10» (arg0 : (_root_.List (_root_.Option value))) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«$cast_record:case_2:iter:10» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$cast_record:case_2:iter:13» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_record:case_2:iter:13» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record:case_3:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_record:case_3:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$cast_record:case_3:iter:6» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (pair _root_.String value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String value)), SpecTecCall.«$cast_record:case_3:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record:case_3:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option value)), SpecTecCall.«$cast_record:case_3:iter:5» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$cast_record:case_3:iter:9» (arg0 : (_root_.List (_root_.Option value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$cast_record:case_3:iter:9» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$cast_record:case_3:iter:10» (arg0 : (_root_.List (_root_.Option value))) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«$cast_record:case_3:iter:10» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$cast_record:case_3:iter:13» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_record:case_3:iter:13» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record:case_4:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_record:case_4:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$cast_record:case_4:iter:6» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (pair _root_.String value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String value)), SpecTecCall.«$cast_record:case_4:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record:case_4:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option value)), SpecTecCall.«$cast_record:case_4:iter:5» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$cast_record:case_4:iter:9» (arg0 : (_root_.List (_root_.Option value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$cast_record:case_4:iter:9» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$cast_record:case_4:iter:10» (arg0 : (_root_.List (_root_.Option value))) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«$cast_record:case_4:iter:10» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$cast_record:case_4:iter:13» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_record:case_4:iter:13» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record:case_5:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_record:case_5:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$cast_record:case_5:iter:6» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (pair _root_.String value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String value)), SpecTecCall.«$cast_record:case_5:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record:case_5:iter:9» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_record:case_5:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record:case_6:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_record:case_6:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$cast_record:case_6:iter:6» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (pair _root_.String value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String value)), SpecTecCall.«$cast_record:case_6:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record:case_6:iter:9» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_record:case_6:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record_field:case_1:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String value))) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«$cast_record_field:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$cast_record_field:case_1:iter:2» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (pair _root_.String value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String value)), SpecTecCall.«$cast_record_field:case_1:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record_field:case_2:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String value))) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«$cast_record_field:case_2:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$cast_record_field:case_2:iter:2» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (pair _root_.String value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String value)), SpecTecCall.«$cast_record_field:case_2:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$is_defaultable_typeIR:row_9:pattern-iter:0» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$is_defaultable_typeIR:row_9:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$is_defaultable_typeIR:row_10:pattern-iter:0» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$is_defaultable_typeIR:row_10:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$is_defaultable_typeIR:row_11:pattern-iter:0» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$is_defaultable_typeIR:row_11:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$is_defaultable_typeIR» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_defaultable_typeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
