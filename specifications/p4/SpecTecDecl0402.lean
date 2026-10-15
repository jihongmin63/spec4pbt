import SpecTecDecl0401

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Lvalue_read:header-union:pattern-iter:1» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Lvalue_read:header-union:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Lvalue_read:header-union:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Lvalue_read:header-union:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Lvalue_write:header-union-keep-valid-header:pattern-iter:1» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Lvalue_write:header-union-keep-valid-header:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Lvalue_write:header-union-keep-valid-header:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Lvalue_write:header-union-keep-valid-header:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Lvalue_write:header-union-replace-valid-header:pattern-iter:1» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Lvalue_write:header-union-replace-valid-header:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Lvalue_write:header-union-replace-valid-header:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Lvalue_write:header-union-replace-valid-header:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Copy_in_default:rule:iter:0» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List typeIR)) (arg4 : (_root_.List nameIR)) (arg5 : (_root_.List parameterInitializerOptIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List typeIR) × ((_root_.List nameIR) × (_root_.List parameterInitializerOptIR))))), SpecTecCall.«Copy_in_default:rule:iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Copy_in_default:rule:iter:1» (arg0 : (_root_.List parameterInitializerOptIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Copy_in_default:rule:iter:1» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Copy_in_default:rule:iter:2» (arg0 : (_root_.List parameterInitializerOptIR)) (arg1 : (_root_.List parameterInitializerIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterInitializerIR), SpecTecCall.«Copy_in_default:rule:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Copy_in_default:rule:iter:4» (arg0 : (_root_.List parameterInitializerIR)) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Copy_in_default:rule:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Copy_in_default:rule:iter:6» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List prefixedNameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List prefixedNameIR), SpecTecCall.«Copy_in_default:rule:iter:6» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Call_eval:definedFunctionCallee-copyin-abort:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:definedFunctionCallee-copyin-abort:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:definedFunctionCallee-cont:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:definedFunctionCallee-cont:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:externFunctionCallee-copyin-abort:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:externFunctionCallee-copyin-abort:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:6» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))), SpecTecCall.«Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:6» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Call_eval:externFunctionCallee-copyin-cont-call-non-reject:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:externFunctionCallee-copyin-cont-call-non-reject:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:externFunctionCallee-copyin-cont-call-non-reject:iter:6» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))), SpecTecCall.«Call_eval:externFunctionCallee-copyin-cont-call-non-reject:iter:6» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Call_eval:builtinIsValidMethodCallee-header-union:iter:2» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Call_eval:builtinIsValidMethodCallee-header-union:iter:2» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Call_eval:copyin-abort-initializer:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:copyin-abort-initializer:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:copyin-cont-initializer:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:copyin-cont-initializer:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:copyin-abort:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:copyin-abort:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:copyin-cont-non-abstract-reject:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:copyin-cont-non-abstract-reject:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:copyin-cont-non-abstract-reject:iter:6» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))), SpecTecCall.«Call_eval:copyin-cont-non-abstract-reject:iter:6» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Call_eval:copyin-cont-non-abstract-non-reject:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:copyin-cont-non-abstract-non-reject:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Call_eval:copyin-cont-non-abstract-non-reject:iter:6» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))), SpecTecCall.«Call_eval:copyin-cont-non-abstract-non-reject:iter:6» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Call_eval:controlApplyMethodCallee-copyin-exit:pattern-iter:2» (arg0 : (_root_.List (pair callTargetId actionDef))) (arg1 : (_root_.List actionDef)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List actionDef) × (_root_.List callableId)), SpecTecCall.«Call_eval:controlApplyMethodCallee-copyin-exit:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Call_eval:controlApplyMethodCallee-localDecl-exit:pattern-iter:2» (arg0 : (_root_.List (pair callTargetId actionDef))) (arg1 : (_root_.List actionDef)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List actionDef) × (_root_.List callableId)), SpecTecCall.«Call_eval:controlApplyMethodCallee-localDecl-exit:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:pattern-iter:2» (arg0 : (_root_.List (pair callTargetId actionDef))) (arg1 : (_root_.List actionDef)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List actionDef) × (_root_.List callableId)), SpecTecCall.«Call_eval:controlApplyMethodCallee-controlBodyIR-exit:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Call_eval:controlApplyMethodCallee-cont:pattern-iter:2» (arg0 : (_root_.List (pair callTargetId actionDef))) (arg1 : (_root_.List actionDef)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List actionDef) × (_root_.List callableId)), SpecTecCall.«Call_eval:controlApplyMethodCallee-cont:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «TableMatch_eval:no-match:iter:2» (arg0 : (_root_.List tableKeyValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«TableMatch_eval:no-match:iter:2» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «TableMatch_eval:match:iter:2» (arg0 : (_root_.List tableKeyValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«TableMatch_eval:match:iter:2» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply

end SpecTec
