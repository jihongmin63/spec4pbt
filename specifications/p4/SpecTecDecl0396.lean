import SpecTecDecl0395

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «CallableType_ok:externMethodTypeIR:iter:6» (arg0 : (_root_.List callableId)) (arg1 : (_root_.List externMethodTypeDefIR)) (arg2 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId externMethodTypeDefIR)), SpecTecCall.«CallableType_ok:externMethodTypeIR:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «CallableType_ok:parserApplyMethodTypeIR:iter:3» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«CallableType_ok:parserApplyMethodTypeIR:iter:3» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «CallableType_ok:controlApplyMethodTypeIR:iter:3» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«CallableType_ok:controlApplyMethodTypeIR:iter:3» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$chain_casts'» (arg0 : typeIR) (arg1 : (_root_.List typeIR)) (arg2 : (typeIR × (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typeIR × (_root_.List typeIR)), SpecTecCall.«$chain_casts'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$chain_casts:case_2:iter:0» (arg0 : (_root_.List (_root_.List typeIR))) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (_root_.List typeIR))) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List (_root_.List typeIR)) × (_root_.List typeIR)), SpecTecCall.«$chain_casts:case_2:iter:0» arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply


noncomputable def «$chain_casts» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (_root_.List typeIR))) (arg2 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«$chain_casts» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$chain_casts_sequenceTypeIR:case_1:iter:1» (arg0 : (_root_.List (_root_.List typeIR))) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_sequenceTypeIR:case_1:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$chain_casts_sequenceTypeIR» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (_root_.List typeIR))) (arg2 : typeIR) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_sequenceTypeIR» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$chain_casts_sequenceTypeIR_default:case_1:iter:1» (arg0 : (_root_.List (_root_.List typeIR))) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_sequenceTypeIR_default:case_1:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$chain_casts_sequenceTypeIR_default» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (_root_.List typeIR))) (arg2 : typeIR) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_sequenceTypeIR_default» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$chain_casts_recordTypeIR:case_1:pattern-iter:0» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$chain_casts_recordTypeIR:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:3» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List id)) (arg2 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$chain_casts_recordTypeIR:case_1:iter:3» arg0 arg1 arg2⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:5» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List id)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$chain_casts_recordTypeIR:case_1:iter:5» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:4» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List id)) (arg2 : (_root_.List (_root_.List typeIR))) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_recordTypeIR:case_1:iter:4» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$chain_casts_recordTypeIR» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List (_root_.List typeIR))) (arg2 : typeIR) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_recordTypeIR» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$chain_casts_recordTypeIR_default:case_1:pattern-iter:0» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:3» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List id)) (arg2 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:iter:3» arg0 arg1 arg2⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:5» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List id)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:iter:5» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:4» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List id)) (arg2 : (_root_.List (_root_.List typeIR))) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:iter:4» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$chain_casts_recordTypeIR_default» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List (_root_.List typeIR))) (arg2 : typeIR) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_recordTypeIR_default» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$apply_cast» (arg0 : typedExpressionIR) (arg1 : (_root_.List typeIR)) (arg2 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.«$apply_cast» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$compat_lnot» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_lnot» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$compat_bnot» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_bnot» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$compat_uplusminus» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_uplusminus» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$compat_plusminusmult» (arg0 : typeIR) (arg1 : typeIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_plusminusmult» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$compat_satplusminus» (arg0 : typeIR) (arg1 : typeIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_satplusminus» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$compat_divmod» (arg0 : typeIR) (arg1 : typeIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_divmod» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$compat_shift» (arg0 : typeIR) (arg1 : typeIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_shift» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$compat_compare» (arg0 : typeIR) (arg1 : typeIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_compare» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$compat_bitwise» (arg0 : typeIR) (arg1 : typeIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_bitwise» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$compat_concat» (arg0 : typeIR) (arg1 : typeIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_concat» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$compat_logical» (arg0 : typeIR) (arg1 : typeIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_logical» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
