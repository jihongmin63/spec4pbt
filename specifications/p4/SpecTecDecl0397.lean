import SpecTecDecl0396

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$compat_array_index» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_array_index» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$compat_bitslice_base» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_bitslice_base» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$compat_bitslice_range_index» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_bitslice_range_index» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$compat_bitslice_offset_index» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_bitslice_offset_index» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$compat_bitslice_offset_width» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_bitslice_offset_width» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_concrete_extern_object':case_2:pattern-iter:1» (arg0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List callableId) × (_root_.List externMethodTypeDefIR)), SpecTecCall.«$is_concrete_extern_object':case_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$compat_range» (arg0 : typeIR) (arg1 : typeIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_range» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$check_switchLabelIR_default» (arg0 : (_root_.List switchLabelIR)) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$check_switchLabelIR_default» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$compat_switch» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_switch» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «InstDecl_non_objectInitializer_ok:rule:iter:1» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«InstDecl_non_objectInitializer_ok:rule:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subst_externMethodTypeDefEnv:case_2:pattern-iter:0» (arg0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List callableId) × (_root_.List externMethodTypeDefIR)), SpecTecCall.«$subst_externMethodTypeDefEnv:case_2:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$subst_externMethodTypeDefEnv:case_2:iter:4» (arg0 : (_root_.List callableId)) (arg1 : (_root_.List externMethodTypeDefIR)) (arg2 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId externMethodTypeDefIR)), SpecTecCall.«$subst_externMethodTypeDefEnv:case_2:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «InstDecl_objectInitializer_ok:rule:iter:1» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«InstDecl_objectInitializer_ok:rule:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$constructorTypeDef_of_externConstructorPrototypeIR» (arg0 : typeParameterListIR) (arg1 : typeIR) (arg2 : externConstructorPrototypeIR) (arg3 : constructorTypeDefIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constructorTypeDefIR, SpecTecCall.«$constructorTypeDef_of_externConstructorPrototypeIR» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_ok:externObjectDeclaration:iter:17» (arg0 : (_root_.List typeId)) (arg1 : typeIR) (arg2 : (_root_.List externConstructorPrototypeIR)) (arg3 : (_root_.List constructorTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List constructorTypeDefIR), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:17» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$compat_mask» (arg0 : typeIR) (arg1 : typeIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_mask» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$compat_table_exact_optional_key» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_table_exact_optional_key» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$compat_table_lpm_ternary_range_key» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_table_lpm_ternary_range_key» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$compat_table_key» (arg0 : nameIR) (arg1 : typeIR) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$compat_table_key» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$insert_NoAction_tablePropertyIR:case_2:iter:1» (arg0 : (_root_.List tableActionIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List parameterListIR)) (arg3 : (_root_.List parameterListIR)) (arg4 : (_root_.List tableActionReferenceIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List tableActionReferenceIR)))), SpecTecCall.«$insert_NoAction_tablePropertyIR:case_2:iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, arg4)))))) finalSupply


noncomputable def «$insert_NoAction_tablePropertyIR:case_3:iter:1» (arg0 : (_root_.List tableActionIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List parameterListIR)) (arg3 : (_root_.List parameterListIR)) (arg4 : (_root_.List tableActionReferenceIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List tableActionReferenceIR)))), SpecTecCall.«$insert_NoAction_tablePropertyIR:case_3:iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, arg4)))))) finalSupply


noncomputable def «$empty_strictness:case_1:iter:0» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List (pair _root_.String strict))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String strict)), SpecTecCall.«$empty_strictness:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$empty_strictness» (arg0 : (_root_.List typeId)) (arg1 : strictness) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨strictness, SpecTecCall.«$empty_strictness» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$empty_constraint:case_1:iter:0» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List (pair _root_.String infer))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String infer)), SpecTecCall.«$empty_constraint:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$empty_constraint» (arg0 : (_root_.List typeId)) (arg1 : constraint) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constraint, SpecTecCall.«$empty_constraint» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$resolve_inference:case_1:pattern-iter:0» (arg0 : (_root_.List (pair _root_.String typeIR))) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List typeIR) × (_root_.List typeId)), SpecTecCall.«$resolve_inference:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$resolve_inference:case_1:iter:4» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeId)) (arg2 : (_root_.List (pair _root_.String typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$resolve_inference:case_1:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$gen_constraint_pair:case_13:iter:2» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List direction)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR))))), SpecTecCall.«$gen_constraint_pair:case_13:iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$gen_constraint_pair:case_13:iter:3» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List direction)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR))))), SpecTecCall.«$gen_constraint_pair:case_13:iter:3» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$gen_constraint_pair:case_13:iter:4» (arg0 : (_root_.List direction)) (arg1 : (_root_.List direction)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«$gen_constraint_pair:case_13:iter:4» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$gen_constraint_pair:case_14:iter:2» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List direction)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR))))), SpecTecCall.«$gen_constraint_pair:case_14:iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «$gen_constraint_pair:case_14:iter:3» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List id)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List direction)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR))))), SpecTecCall.«$gen_constraint_pair:case_14:iter:3» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply

end SpecTec
