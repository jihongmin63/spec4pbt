import SpecTecDecl0387

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$nestable_controlApplyMethod» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_controlApplyMethod» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «CallableType_wf:controlApplyMethodTypeIR:iter:5» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:controlApplyMethodTypeIR:iter:5» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_constructor_extern» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_constructor_extern» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «ConstructorType_wf:externObjectTypeIR:iter:4» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:externObjectTypeIR:iter:4» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_constructor_parser» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_constructor_parser» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «ConstructorType_wf:parserObjectTypeIR:iter:6» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:parserObjectTypeIR:iter:6» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_constructor_control» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_constructor_control» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «ConstructorType_wf:controlObjectTypeIR:iter:6» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:controlObjectTypeIR:iter:6» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_constructor_package» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_constructor_package» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «ConstructorType_wf:packageObjectTypeIR:iter:4» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:packageObjectTypeIR:iter:4» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$definable_constructor» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$definable_constructor» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Expr_eval_lctk:non-default_2:pattern-iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List typedExpressionIR)), SpecTecCall.«Expr_eval_lctk:non-default_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval_lctk:non-default_2:iter:4» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_eval_lctk:non-default_2:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_eval_lctk:default_2:pattern-iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List typedExpressionIR)), SpecTecCall.«Expr_eval_lctk:default_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval_lctk:default_2:iter:4» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_eval_lctk:default_2:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_eval_lctk:serenum:pattern-iter:6» (arg0 : (_root_.List valueFieldIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Expr_eval_lctk:serenum:pattern-iter:6» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval_lctk:serenum:iter:8» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval_lctk:serenum:iter:8» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_eval_lctk:struct:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Expr_eval_lctk:struct:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval_lctk:struct:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval_lctk:struct:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_eval_lctk:header:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Expr_eval_lctk:header:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval_lctk:header:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval_lctk:header:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_eval_lctk:header-union:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Expr_eval_lctk:header-union:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval_lctk:header-union:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval_lctk:header-union:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_eval_lctk:static_assert:iter:4» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List parameterInitializerOptIR)) (arg4 : (_root_.List typeIR)) (arg5 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))), SpecTecCall.«Expr_eval_lctk:static_assert:iter:4» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Expr_eval_lctk:static_assert:iter:8» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List parameterInitializerOptIR)) (arg3 : (_root_.List direction)) (arg4 : (_root_.List nameIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × ((_root_.List nameIR) × (_root_.List typeIR))))), SpecTecCall.«Expr_eval_lctk:static_assert:iter:8» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «Expr_eval_lctk:static_assert:iter:9» (arg0 : (_root_.List direction)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List value)) (arg3 : (_root_.List varTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List varTypeIR), SpecTecCall.«Expr_eval_lctk:static_assert:iter:9» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «TypeParameterListOpt_ok:rule:iter:1» (arg0 : (_root_.List typeParameter)) (arg1 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeId), SpecTecCall.«TypeParameterListOpt_ok:rule:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:listTypeIR:iter:4» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:listTypeIR:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:tupleTypeIR:iter:4» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:tupleTypeIR:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:arrayTypeIR:iter:4» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:arrayTypeIR:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:headerStackTypeIR:iter:4» (arg0 : (_root_.List castResult)) (arg1 : (_root_.List (_root_.List typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:headerStackTypeIR:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Cast_expl_neq:structTypeIR:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply

end SpecTec
