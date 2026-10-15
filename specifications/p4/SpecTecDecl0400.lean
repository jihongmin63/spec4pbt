import SpecTecDecl0399

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Decl_inst:packageTypeDeclarationIR:iter:1» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«Decl_inst:packageTypeDeclarationIR:iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Constructor_call:externConstructorDef:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Constructor_call:externConstructorDef:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Constructor_call:externConstructorDef:iter:5» (arg0 : (_root_.List constructorParameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«Constructor_call:externConstructorDef:iter:5» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Constructor_call:externConstructorDef:pattern-iter:6» (arg0 : (_root_.List (pair callTargetId callableDef))) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List callableDef)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List callableId) × (_root_.List callableDef)), SpecTecCall.«Constructor_call:externConstructorDef:pattern-iter:6» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Constructor_call:externConstructorDef:iter:9» (arg0 : (_root_.List callableDef)) (arg1 : (_root_.List externMethodDef)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List externMethodDef), SpecTecCall.«Constructor_call:externConstructorDef:iter:9» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Constructor_call:externConstructorDef:iter:11» (arg0 : (_root_.List constructorParameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«Constructor_call:externConstructorDef:iter:11» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Constructor_call:externConstructorDef:iter:12» (arg0 : (_root_.List id)) (arg1 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Constructor_call:externConstructorDef:iter:12» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Constructor_call:externConstructorDef:iter:13» (arg0 : instContext) (arg1 : (_root_.List id)) (arg2 : (_root_.List (_root_.Option value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option value)), SpecTecCall.«Constructor_call:externConstructorDef:iter:13» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Constructor_call:externConstructorDef:iter:15» (arg0 : (_root_.List (_root_.Option value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Constructor_call:externConstructorDef:iter:15» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Constructor_call:externConstructorDef:iter:16» (arg0 : (_root_.List (_root_.Option value))) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Constructor_call:externConstructorDef:iter:16» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Constructor_call:externConstructorDef:iter:18» (arg0 : (_root_.List callableId)) (arg1 : (_root_.List externMethodDef)) (arg2 : (_root_.List (pair callTargetId externMethodDef))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId externMethodDef)), SpecTecCall.«Constructor_call:externConstructorDef:iter:18» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Constructor_call:parserConstructorDef:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Constructor_call:parserConstructorDef:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Constructor_call:parserConstructorDef:iter:5» (arg0 : (_root_.List constructorParameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«Constructor_call:parserConstructorDef:iter:5» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Constructor_call:controlConstructorDef:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Constructor_call:controlConstructorDef:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Constructor_call:controlConstructorDef:iter:5» (arg0 : (_root_.List constructorParameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«Constructor_call:controlConstructorDef:iter:5» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Constructor_call:controlConstructorDef:pattern-iter:6» (arg0 : (_root_.List (pair callTargetId callableDef))) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List callableDef)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List callableId) × (_root_.List callableDef)), SpecTecCall.«Constructor_call:controlConstructorDef:pattern-iter:6» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Constructor_call:controlConstructorDef:iter:9» (arg0 : (_root_.List callableDef)) (arg1 : (_root_.List actionDef)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List actionDef), SpecTecCall.«Constructor_call:controlConstructorDef:iter:9» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Constructor_call:controlConstructorDef:iter:11» (arg0 : (_root_.List actionDef)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId actionDef))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId actionDef)), SpecTecCall.«Constructor_call:controlConstructorDef:iter:11» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Constructor_call:controlConstructorDef:iter:13» (arg0 : (_root_.List actionDef)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId actionDef))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId actionDef)), SpecTecCall.«Constructor_call:controlConstructorDef:iter:13» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Constructor_call:packageConstructorDef:iter:2» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeParameterIR)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Constructor_call:packageConstructorDef:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Constructor_call:packageConstructorDef:iter:5» (arg0 : (_root_.List constructorParameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«Constructor_call:packageConstructorDef:iter:5» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$merge_frames:case_1:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String value))) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«$merge_frames:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$merge_frames» (arg0 : frame) (arg1 : frame) (arg2 : frame) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨frame, SpecTecCall.«$merge_frames» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$merge_externMethodDefEnvs:case_2:pattern-iter:0» (arg0 : (_root_.List (pair callTargetId callableDef))) (arg1 : (_root_.List callableDef)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List callableDef) × (_root_.List callableId)), SpecTecCall.«$merge_externMethodDefEnvs:case_2:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$merge_externMethodDefEnvs:case_2:iter:4» (arg0 : (_root_.List callableDef)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId callableDef))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId callableDef)), SpecTecCall.«$merge_externMethodDefEnvs:case_2:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$callableId_of_externConstructorPrototypeIR» (arg0 : externConstructorPrototypeIR) (arg1 : callableId) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callableId, SpecTecCall.«$callableId_of_externConstructorPrototypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_inst:constructor:iter:8» (arg0 : (_root_.List externConstructorPrototypeIR)) (arg1 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List callableId), SpecTecCall.«Decl_inst:constructor:iter:8» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$constructor_of_externConstructorPrototypeIR» (arg0 : typeParameterListIR) (arg1 : externMethodPrototypeListIR) (arg2 : externConstructorPrototypeIR) (arg3 : constructorDef) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constructorDef, SpecTecCall.«$constructor_of_externConstructorPrototypeIR» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_inst:constructor:iter:10» (arg0 : typeParameterListIR) (arg1 : (_root_.List externMethodPrototypeIR)) (arg2 : (_root_.List externConstructorPrototypeIR)) (arg3 : (_root_.List constructorDef)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List constructorDef), SpecTecCall.«Decl_inst:constructor:iter:10» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$enter_e» (arg0 : evalContext) (arg1 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.«$enter_e» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$exit_e» (arg0 : evalContext) (arg1 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.«$exit_e» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_parserState_e» (arg0 : evalContext) (arg1 : nameIR) (arg2 : (_root_.Option parserStateIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option parserStateIR), SpecTecCall.«$find_parserState_e» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
