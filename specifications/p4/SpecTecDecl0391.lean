import SpecTecDecl0390

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:19» (arg0 : (_root_.List (_root_.Option typeIR))) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:19» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:22» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:22» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:24» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:24» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:23» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:23» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:27» (arg0 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:27» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:28» (arg0 : (_root_.List (_root_.Option typeIR))) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:28» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:29» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:29» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:listTypeIR:iter:4» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:listTypeIR:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:tupleTypeIR:iter:4» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:tupleTypeIR:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:arrayTypeIR:iter:4» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:arrayTypeIR:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:headerStackTypeIR:iter:4» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:headerStackTypeIR:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Cast_impl_neq:structTypeIR:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR:iter:6» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:structTypeIR:iter:6» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_2:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Cast_impl_neq:headerTypeIR_2:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_2:iter:6» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:headerTypeIR_2:iter:6» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:sequenceTypeIR:iter:4» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:sequenceTypeIR:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:5» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:tupleTypeIR_2:iter:5» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:6» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:tupleTypeIR_2:iter:6» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:arrayTypeIR_2:iter:4» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:arrayTypeIR_2:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:headerStackTypeIR_2:iter:4» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:headerStackTypeIR_2:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_2:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Cast_impl_neq:structTypeIR_2:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_2:iter:7» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:structTypeIR_2:iter:7» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_2:iter:8» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:structTypeIR_2:iter:8» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_3:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Cast_impl_neq:headerTypeIR_3:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_3:iter:7» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:headerTypeIR_3:iter:7» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_3:iter:8» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerTypeIR_3:iter:8» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_3:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«Cast_impl_neq:structTypeIR_3:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_3:pattern-iter:4» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«Cast_impl_neq:structTypeIR_3:pattern-iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:7» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:structTypeIR_3:iter:7» arg0 arg1 arg2⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:9» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_impl_neq:structTypeIR_3:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:8» (arg0 : (_root_.List id)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List id)) (arg3 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«Cast_impl_neq:structTypeIR_3:iter:8» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:12» (arg0 : (_root_.List (_root_.Option typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:structTypeIR_3:iter:12» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

end SpecTec
