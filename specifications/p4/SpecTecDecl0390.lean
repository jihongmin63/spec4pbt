import SpecTecDecl0389

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Cast_expl_neq:headerTypeIR_4:iter:15» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_4:iter:15» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_4:iter:14» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_4:iter:14» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_4:iter:18» (arg0 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_4:iter:18» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_4:iter:19» (arg0 : (_root_.List (_root_.Option typeIR))) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Cast_expl_neq:headerTypeIR_4:iter:19» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_4:iter:22» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_4:iter:22» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«Cast_expl_neq:structTypeIR_4:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:pattern-iter:4» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«Cast_expl_neq:structTypeIR_4:pattern-iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:7» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:7» arg0 arg1 arg2⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:9» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:8» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:8» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:12» (arg0 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:12» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:13» (arg0 : (_root_.List (_root_.Option typeIR))) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:13» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:15» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:15» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:14» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:14» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:18» (arg0 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:18» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:19» (arg0 : (_root_.List (_root_.Option typeIR))) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:19» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:22» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:22» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:24» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:24» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:23» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:23» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:27» (arg0 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:27» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:28» (arg0 : (_root_.List (_root_.Option typeIR))) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:28» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:29» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:29» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:pattern-iter:4» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:pattern-iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:7» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:7» arg0 arg1 arg2⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:9» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:8» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:8» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:12» (arg0 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:12» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:13» (arg0 : (_root_.List (_root_.Option typeIR))) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:13» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:15» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:15» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:14» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:14» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:18» (arg0 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:18» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

end SpecTec
