import SpecTecDecl0375

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$shr_arith» (arg0 : _root_.Int) (arg1 : _root_.Int) (arg2 : _root_.Int) (arg3 : _root_.Int) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Int, SpecTecCall.«$shr_arith» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$bitacc» (arg0 : _root_.Int) (arg1 : _root_.Int) (arg2 : _root_.Int) (arg3 : _root_.Int) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Int, SpecTecCall.«$bitacc» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$bitacc_replace» (arg0 : _root_.Int) (arg1 : _root_.Int) (arg2 : _root_.Int) (arg3 : _root_.Int) (arg4 : _root_.Int) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Int, SpecTecCall.«$bitacc_replace» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$bin_eq:case_14:iter:2» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_14:iter:2» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$bin_eq:case_14:iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_14:iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$bin_eq:case_14:iter:8» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_14:iter:8» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_eq:case_15:iter:2» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_15:iter:2» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$bin_eq:case_15:iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_15:iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$bin_eq:case_15:iter:8» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_15:iter:8» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_eq:case_16:iter:2» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_16:iter:2» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$bin_eq:case_16:iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_16:iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$bin_eq:case_16:iter:8» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_16:iter:8» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$default:case_17:pattern-iter:1» (arg0 : (_root_.List valueFieldIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$default:case_17:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$default:case_17:iter:4» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (value × _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (value × _root_.String)), SpecTecCall.«$default:case_17:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$default:case_18:pattern-iter:1» (arg0 : (_root_.List valueFieldIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$default:case_18:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$default:case_18:iter:4» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (value × _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (value × _root_.String)), SpecTecCall.«$default:case_18:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_struct:case_1:pattern-iter:0» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_struct:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$cast_struct:case_1:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_struct:case_1:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_header:case_1:pattern-iter:0» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_header:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$cast_header:case_1:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_header:case_1:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_header_union:case_1:pattern-iter:0» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_header_union:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$cast_header_union:case_1:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_header_union:case_1:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_sequence:case_7:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_sequence:case_7:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_sequence:case_8:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_sequence:case_8:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_sequence:case_13:iter:8» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_sequence:case_13:iter:8» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_sequence:case_14:iter:8» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_sequence:case_14:iter:8» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record:case_1:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_record:case_1:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$cast_record:case_1:iter:6» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (pair _root_.String value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String value)), SpecTecCall.«$cast_record:case_1:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_record:case_1:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option value)), SpecTecCall.«$cast_record:case_1:iter:5» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$cast_record:case_1:iter:9» (arg0 : (_root_.List (_root_.Option value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$cast_record:case_1:iter:9» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$cast_record:case_1:iter:10» (arg0 : (_root_.List (_root_.Option value))) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«$cast_record:case_1:iter:10» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$cast_record:case_1:iter:13» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_record:case_1:iter:13» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
