import SpecTecDecl0415

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$free_typeIR:case_14:iter:6» (arg0 : (_root_.List externMethodTypeDefIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_14:iter:6» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_15:iter:1» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_15:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_15:iter:4» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_15:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_16:iter:1» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_16:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_16:iter:4» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_16:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_17:iter:1» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_17:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_17:iter:4» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_17:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_21:iter:1» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_21:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_22:iter:1» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_22:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_23:iter:3» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_23:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_24:iter:3» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_24:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_parameterIR» (arg0 : parameterIR) (arg1 : bound) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨bound, SpecTecCall.«$free_parameterIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_callableTypeIR» (arg0 : callableTypeIR) (arg1 : bound) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨bound, SpecTecCall.«$free_callableTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_callableTypeIR:case_1:iter:1» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_1:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_callableTypeIR:case_2:iter:1» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_2:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_callableTypeIR:case_3:iter:1» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_3:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_callableTypeIR:case_5:iter:1» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_5:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_callableTypeIR:case_6:iter:1» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_6:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_callableTypeIR:case_7:iter:1» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_7:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_callableTypeIR:case_8:iter:1» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_8:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_callableTypeDefIR» (arg0 : callableTypeDefIR) (arg1 : bound) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨bound, SpecTecCall.«$free_callableTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeDefIR» (arg0 : typeDefIR) (arg1 : bound) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨bound, SpecTecCall.«$free_typeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_parameterIRs:case_1:iter:0» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_parameterIRs:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_parameterIRs» (arg0 : (_root_.List parameterIR)) (arg1 : bound) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨bound, SpecTecCall.«$free_parameterIRs» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$capture_avoiding_:case_1:iter:4» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$capture_avoiding_:case_1:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$capture_avoiding_» (arg0 : theta) (arg1 : (_root_.List typeParameterIR)) (arg2 : bound) (arg3 : (theta × (_root_.List typeParameterIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(theta × (_root_.List typeParameterIR)), SpecTecCall.«$capture_avoiding_» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$capture_avoiding:case_1:iter:4» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$capture_avoiding:case_1:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$capture_avoiding» (arg0 : theta) (arg1 : (_root_.List typeId)) (arg2 : (_root_.List typeId)) (arg3 : bound) (arg4 : (theta × ((_root_.List typeId) × (_root_.List typeId)))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(theta × ((_root_.List typeId) × (_root_.List typeId))), SpecTecCall.«$capture_avoiding» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$subst_typeIR» (arg0 : theta) (arg1 : typeIR) (arg2 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$subst_typeIR» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$subst_typeIR'» (arg0 : theta) (arg1 : typeIR) (arg2 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$subst_typeIR':case_7:iter:1» (arg0 : theta) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$subst_typeIR':case_7:iter:1» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$subst_typeIR':case_10:iter:3» (arg0 : theta) (arg1 : (_root_.List typeArgumentIR)) (arg2 : (_root_.List typeArgumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«$subst_typeIR':case_10:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
