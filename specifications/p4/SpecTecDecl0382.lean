import SpecTecDecl0381

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$match_overloaded_unnamed:case_3:iter:8» (V_T : Type) (arg0 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$match_overloaded_unnamed:case_3:iter:8» V_T arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$match_overloaded_unnamed:case_3:iter:12» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List id), SpecTecCall.«$match_overloaded_unnamed:case_3:iter:12» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_overloadeds_named:case_2:pattern-iter:0» (V : Type) (arg0 : (_root_.List (pair callTargetId V))) (arg1 : (_root_.List V)) (arg2 : (_root_.List callTargetId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V) × (_root_.List callTargetId)), SpecTecCall.«$find_overloadeds_named:case_2:pattern-iter:0» V arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_overloadeds_named:case_2:iter:3» (V : Type) (arg0 : (_root_.List V)) (arg1 : (_root_.List callTargetId)) (arg2 : (_root_.List (pair callTargetId V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_overloadeds_named:case_2:iter:3» V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_overloadeds_named:case_3:pattern-iter:0» (V : Type) (arg0 : (_root_.List (pair callTargetId V))) (arg1 : (_root_.List V)) (arg2 : (_root_.List callTargetId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V) × (_root_.List callTargetId)), SpecTecCall.«$find_overloadeds_named:case_3:pattern-iter:0» V arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_overloadeds_named:case_3:iter:3» (V : Type) (arg0 : (_root_.List V)) (arg1 : (_root_.List callTargetId)) (arg2 : (_root_.List (pair callTargetId V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_overloadeds_named:case_3:iter:3» V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_overloadeds_unnamed:case_2:pattern-iter:0» (V : Type) (arg0 : (_root_.List (pair callTargetId V))) (arg1 : (_root_.List V)) (arg2 : (_root_.List callTargetId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V) × (_root_.List callTargetId)), SpecTecCall.«$find_overloadeds_unnamed:case_2:pattern-iter:0» V arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_overloadeds_unnamed:case_2:iter:3» (V : Type) (arg0 : (_root_.List V)) (arg1 : (_root_.List callTargetId)) (arg2 : (_root_.List (pair callTargetId V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_overloadeds_unnamed:case_2:iter:3» V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_overloadeds_unnamed:case_3:pattern-iter:0» (V : Type) (arg0 : (_root_.List (pair callTargetId V))) (arg1 : (_root_.List V)) (arg2 : (_root_.List callTargetId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V) × (_root_.List callTargetId)), SpecTecCall.«$find_overloadeds_unnamed:case_3:pattern-iter:0» V arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_overloadeds_unnamed:case_3:iter:3» (V : Type) (arg0 : (_root_.List V)) (arg1 : (_root_.List callTargetId)) (arg2 : (_root_.List (pair callTargetId V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_overloadeds_unnamed:case_3:iter:3» V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_overloaded:case_1:pattern-iter:0» (V_T : Type) (arg0 : (_root_.List (pair callTargetId V_T))) (arg1 : (_root_.List V_T)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V_T) × (_root_.List callableId)), SpecTecCall.«$find_overloaded:case_1:pattern-iter:0» V_T arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_overloaded:case_1:iter:2» (V_T : Type) (arg0 : (_root_.List (_root_.Option id))) (arg1 : (_root_.List (_root_.Option id))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option id)), SpecTecCall.«$find_overloaded:case_1:iter:2» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_overloaded:case_1:iter:3» (V_T : Type) (arg0 : (_root_.List (_root_.Option id))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$find_overloaded:case_1:iter:3» V_T arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$find_overloaded:case_1:iter:4» (V_T : Type) (arg0 : (_root_.List (_root_.Option id))) (arg1 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List id), SpecTecCall.«$find_overloaded:case_1:iter:4» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_overloaded:case_1:iter:5» (V_T : Type) (arg0 : (_root_.List V_T)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId V_T))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId V_T)), SpecTecCall.«$find_overloaded:case_1:iter:5» V_T arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_overloaded:case_2:pattern-iter:0» (V_T : Type) (arg0 : (_root_.List (pair callTargetId V_T))) (arg1 : (_root_.List V_T)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V_T) × (_root_.List callableId)), SpecTecCall.«$find_overloaded:case_2:pattern-iter:0» V_T arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_overloaded:case_2:iter:2» (V_T : Type) (arg0 : (_root_.List (_root_.Option id))) (arg1 : (_root_.List (_root_.Option id))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option id)), SpecTecCall.«$find_overloaded:case_2:iter:2» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_overloaded:case_2:iter:3» (V_T : Type) (arg0 : (_root_.List (_root_.Option id))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$find_overloaded:case_2:iter:3» V_T arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$find_overloaded:case_2:iter:4» (V_T : Type) (arg0 : (_root_.List (_root_.Option id))) (arg1 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List id), SpecTecCall.«$find_overloaded:case_2:iter:4» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_overloaded:case_2:iter:5» (V_T : Type) (arg0 : (_root_.List V_T)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId V_T))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId V_T)), SpecTecCall.«$find_overloaded:case_2:iter:5» V_T arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_overloaded:case_3:pattern-iter:0» (V_T : Type) (arg0 : (_root_.List (pair callTargetId V_T))) (arg1 : (_root_.List V_T)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V_T) × (_root_.List callableId)), SpecTecCall.«$find_overloaded:case_3:pattern-iter:0» V_T arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_overloaded:case_3:iter:2» (V_T : Type) (arg0 : (_root_.List (_root_.Option id))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$find_overloaded:case_3:iter:2» V_T arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$find_overloaded:case_3:iter:3» (V_T : Type) (arg0 : (_root_.List V_T)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId V_T))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId V_T)), SpecTecCall.«$find_overloaded:case_3:iter:3» V_T arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_overloaded:case_4:pattern-iter:0» (V_T : Type) (arg0 : (_root_.List (pair callTargetId V_T))) (arg1 : (_root_.List V_T)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V_T) × (_root_.List callableId)), SpecTecCall.«$find_overloaded:case_4:pattern-iter:0» V_T arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_overloaded:case_4:iter:2» (V_T : Type) (arg0 : (_root_.List (_root_.Option id))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$find_overloaded:case_4:iter:2» V_T arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$find_overloaded:case_4:iter:3» (V_T : Type) (arg0 : (_root_.List V_T)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId V_T))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId V_T)), SpecTecCall.«$find_overloaded:case_4:iter:3» V_T arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_non_overloaded:case_1:pattern-iter:0» (V_T : Type) (arg0 : (_root_.List (pair callTargetId V_T))) (arg1 : (_root_.List V_T)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V_T) × (_root_.List callableId)), SpecTecCall.«$find_non_overloaded:case_1:pattern-iter:0» V_T arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_non_overloaded:case_1:iter:2» (V_T : Type) (arg0 : (_root_.List V_T)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId V_T))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId V_T)), SpecTecCall.«$find_non_overloaded:case_1:iter:2» V_T arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_non_overloaded:case_2:pattern-iter:0» (V_T : Type) (arg0 : (_root_.List (pair callTargetId V_T))) (arg1 : (_root_.List V_T)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V_T) × (_root_.List callableId)), SpecTecCall.«$find_non_overloaded:case_2:pattern-iter:0» V_T arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_non_overloadeds:case_2:pattern-iter:0» (V : Type) (arg0 : (_root_.List (pair callTargetId V))) (arg1 : (_root_.List V)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_2:pattern-iter:0» V arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_non_overloadeds:case_2:iter:2» (V : Type) (arg0 : (_root_.List V)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_non_overloadeds:case_2:iter:2» V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_non_overloadeds:case_2:pattern-iter:5» (V : Type) (arg0 : (_root_.List (callTargetId × V))) (arg1 : (_root_.List V)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_2:pattern-iter:5» V arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply

end SpecTec
