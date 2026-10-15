import SpecTecDecl0380

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$sizeof_maxSizeInBits':case_12:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$sizeof_maxSizeInBits':case_12:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$sizeof_maxSizeInBits':case_13:pattern-iter:1» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$sizeof_maxSizeInBits':case_13:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$type_of_typedExpressionIR» (arg0 : typedExpressionIR) (arg1 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$type_of_typedExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$ctk_of_typedExpressionIR» (arg0 : typedExpressionIR) (arg1 : ctk) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨ctk, SpecTecCall.«$ctk_of_typedExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$type_of_typedLvalueIR» (arg0 : typedLvalueIR) (arg1 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$type_of_typedLvalueIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_objectInitializerOptIR» (arg0 : objectInitializerOptIR) (arg1 : objectDeclarationListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨objectDeclarationListIR, SpecTecCall.«$flatten_objectInitializerOptIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$tableEntryPriorityOptIR_of_tableEntryIR» (arg0 : tableEntryIR) (arg1 : tableEntryPriorityOptIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntryPriorityOptIR, SpecTecCall.«$tableEntryPriorityOptIR_of_tableEntryIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$partition_parameterListIR» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List nameIR)) (arg3 : ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR)))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR))), SpecTecCall.«$partition_parameterListIR» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$align_parameterListIR:case_1:iter:1» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))), SpecTecCall.«$align_parameterListIR:case_1:iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$align_parameterListIR:case_1:iter:2» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List (pair _root_.String parameterIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String parameterIR)), SpecTecCall.«$align_parameterListIR:case_1:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$align_parameterListIR_given:case_1:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String parameterIR))) (arg1 : (_root_.List id)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$align_parameterListIR_given:case_2:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String parameterIR))) (arg1 : (_root_.List id)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_2:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$align_parameterListIR_given:case_2:iter:3» (arg0 : (_root_.List id)) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List (pair _root_.String parameterIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_2:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$align_parameterListIR_given:case_3:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String parameterIR))) (arg1 : (_root_.List id)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_3:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$align_parameterListIR_given:case_3:iter:2» (arg0 : (_root_.List id)) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List (pair _root_.String parameterIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_3:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$align_parameterListIR_given:case_4:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String parameterIR))) (arg1 : (_root_.List id)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_4:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$align_parameterListIR_given:case_4:iter:2» (arg0 : (_root_.List id)) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List (pair _root_.String parameterIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_4:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$align_parameterListIR_given:case_4:iter:5» (arg0 : (_root_.List id)) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List (pair _root_.String parameterIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_4:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$align_parameterListIR_given:case_5:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String parameterIR))) (arg1 : (_root_.List id)) (arg2 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_5:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$align_parameterListIR_given:case_5:iter:2» (arg0 : (_root_.List id)) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List (pair _root_.String parameterIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_5:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$align_parameterListIR_given:case_5:iter:5» (arg0 : (_root_.List id)) (arg1 : (_root_.List parameterIR)) (arg2 : (_root_.List (pair _root_.String parameterIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_5:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$match_overloaded_named:case_1:iter:1» (V_T : Type) (arg0 : (_root_.List id)) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$match_overloaded_named:case_1:iter:1» V_T arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$match_overloaded_named:case_2:iter:1» (V_T : Type) (arg0 : (_root_.List id)) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$match_overloaded_named:case_2:iter:1» V_T arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$match_overloaded_named:case_2:iter:3» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_named:case_2:iter:3» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$match_overloaded_named:case_2:iter:7» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_named:case_2:iter:7» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$match_overloaded_named:case_2:iter:11» (V_T : Type) (arg0 : (_root_.List id)) (arg1 : (_root_.List id)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_named:case_2:iter:11» V_T arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$match_overloaded_named:case_2:iter:18» (V_T : Type) (arg0 : (_root_.List id)) (arg1 : (_root_.List id)) (arg2 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_named:case_2:iter:18» V_T arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$match_overloaded_unnamed:case_1:iter:1» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_unnamed:case_1:iter:1» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$match_overloaded_unnamed:case_2:iter:1» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_unnamed:case_2:iter:1» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$match_overloaded_unnamed:case_2:iter:10» (V_T : Type) (arg0 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$match_overloaded_unnamed:case_2:iter:10» V_T arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$match_overloaded_unnamed:case_2:iter:12» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List id), SpecTecCall.«$match_overloaded_unnamed:case_2:iter:12» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$match_overloaded_unnamed:case_3:iter:1» (V_T : Type) (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_unnamed:case_3:iter:1» V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
