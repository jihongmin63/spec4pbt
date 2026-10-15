import SpecTecDecl0397

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$gen_constraint_pair:case_14:iter:4» (arg0 : (_root_.List direction)) (arg1 : (_root_.List direction)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$gen_constraint_pair:case_14:iter:4» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$resolve_constraint:case_2:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String infer))) (arg1 : (_root_.List infer)) (arg2 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List infer) × (_root_.List typeId)), SpecTecCall.«$resolve_constraint:case_2:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$resolve_constraint:case_2:iter:2» (arg0 : (_root_.List infer)) (arg1 : (_root_.List typeId)) (arg2 : (_root_.List (pair _root_.String infer))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String infer)), SpecTecCall.«$resolve_constraint:case_2:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$resolve_constraint:case_2:pattern-iter:5» (arg0 : (_root_.List (pair _root_.String typeIR))) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List typeIR) × (_root_.List typeId)), SpecTecCall.«$resolve_constraint:case_2:pattern-iter:5» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$resolve_constraint:case_2:iter:7» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$resolve_constraint:case_2:iter:7» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$resolve_constraint:case_2:iter:8» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeId)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$resolve_constraint:case_2:iter:8» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$resolve_constraint:case_3:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String infer))) (arg1 : (_root_.List infer)) (arg2 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List infer) × (_root_.List typeId)), SpecTecCall.«$resolve_constraint:case_3:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$resolve_constraint:case_3:iter:3» (arg0 : (_root_.List infer)) (arg1 : (_root_.List typeId)) (arg2 : (_root_.List (pair _root_.String infer))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String infer)), SpecTecCall.«$resolve_constraint:case_3:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$resolve_constraint:case_3:pattern-iter:6» (arg0 : (_root_.List (pair _root_.String typeIR))) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List typeIR) × (_root_.List typeId)), SpecTecCall.«$resolve_constraint:case_3:pattern-iter:6» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$resolve_constraint:case_3:iter:8» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$resolve_constraint:case_3:iter:8» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$resolve_constraint:case_3:iter:9» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeId)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$resolve_constraint:case_3:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$callableId_IR:case_1:iter:0» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«$callableId_IR:case_1:iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$callableId_IR» (arg0 : nameIR) (arg1 : parameterListIR) (arg2 : callableId) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callableId, SpecTecCall.«$callableId_IR» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$parameterListIR_of_actionDef» (arg0 : actionDef) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_actionDef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_definedFunctionDef» (arg0 : definedFunctionDef) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_definedFunctionDef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_externFunctionDef» (arg0 : externFunctionDef) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_externFunctionDef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_tableApplyMethodDef» (arg0 : tableApplyMethodDef) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_tableApplyMethodDef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_controlApplyMethodDef» (arg0 : controlApplyMethodDef) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_controlApplyMethodDef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$empty_frame» (arg0 : frame) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨frame, SpecTecCall.«$empty_frame» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$parameterListIR_of_parserApplyMethodDef» (arg0 : parserApplyMethodDef) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_parserApplyMethodDef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$empty_stateEnv» (arg0 : stateEnv) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨stateEnv, SpecTecCall.«$empty_stateEnv» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$empty_callableDefEnv» (arg0 : callableDefEnv) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callableDefEnv, SpecTecCall.«$empty_callableDefEnv» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$empty_constructorDefEnv» (arg0 : constructorDefEnv) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constructorDefEnv, SpecTecCall.«$empty_constructorDefEnv» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$empty_store» (arg0 : store) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨store, SpecTecCall.«$empty_store» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$add_store» (arg0 : store) (arg1 : objectId) (arg2 : object) (arg3 : store) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨store, SpecTecCall.«$add_store» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_store» (arg0 : store) (arg1 : objectId) (arg2 : object) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨object, SpecTecCall.«$find_store» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$empty_instContext» (arg0 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$empty_instContext» ⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$enter_i» (arg0 : instContext) (arg1 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$enter_i» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$exit_i» (arg0 : instContext) (arg1 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$exit_i» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$enter_path_i» (arg0 : instContext) (arg1 : id) (arg2 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$enter_path_i» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$add_parserState_i» (arg0 : instContext) (arg1 : nameIR) (arg2 : parserStateIR) (arg3 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$add_parserState_i» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$add_callableDef_non_overload_i:case_1:pattern-iter:1» (arg0 : (_root_.List callTargetId)) (arg1 : (_root_.List (_root_.List id))) (arg2 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List (_root_.List id)) × (_root_.List id)), SpecTecCall.«$add_callableDef_non_overload_i:case_1:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply

end SpecTec
