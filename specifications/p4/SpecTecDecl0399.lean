import SpecTecDecl0398

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$add_callableDef_non_overload_i:case_2:pattern-iter:1» (arg0 : (_root_.List callTargetId)) (arg1 : (_root_.List (_root_.List id))) (arg2 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List (_root_.List id)) × (_root_.List id)), SpecTecCall.«$add_callableDef_non_overload_i:case_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$add_constructorDef_i» (arg0 : instContext) (arg1 : callableId) (arg2 : constructorDef) (arg3 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$add_constructorDef_i» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$add_constructorDefs_i» (arg0 : instContext) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List constructorDef)) (arg3 : instContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instContext, SpecTecCall.«$add_constructorDefs_i» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Expr_inst:non-default_2:pattern-iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List typedExpressionIR)), SpecTecCall.«Expr_inst:non-default_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_inst:non-default_2:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_inst:non-default_2:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_inst:default_2:pattern-iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List typedExpressionIR)), SpecTecCall.«Expr_inst:default_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_inst:default_2:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_inst:default_2:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_inst:serenum:pattern-iter:5» (arg0 : (_root_.List valueFieldIR)) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_inst:serenum:pattern-iter:5» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_inst:serenum:iter:7» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_inst:serenum:iter:7» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_inst:struct:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_inst:struct:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_inst:struct:iter:5» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_inst:struct:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_inst:header:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_inst:header:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_inst:header:iter:5» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_inst:header:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_inst:header-union:pattern-iter:3» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_inst:header-union:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_inst:header-union:iter:5» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_inst:header-union:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_inst:errorDeclarationIR:iter:1» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_inst:errorDeclarationIR:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_inst:errorDeclarationIR:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Decl_inst:errorDeclarationIR:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_inst:matchKindDeclarationIR:iter:1» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Decl_inst:matchKindDeclarationIR:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_inst:non-constructor:iter:5» (arg0 : (_root_.List callableId)) (arg1 : (_root_.List externMethodTypeDefIR)) (arg2 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId externMethodTypeDefIR)), SpecTecCall.«Decl_inst:non-constructor:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_inst:constructor:iter:5» (arg0 : (_root_.List callableId)) (arg1 : (_root_.List externMethodTypeDefIR)) (arg2 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId externMethodTypeDefIR)), SpecTecCall.«Decl_inst:constructor:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_inst:enumTypeDeclarationIR-non-serializable:iter:1» (arg0 : nameIR) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-non-serializable:iter:1» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_inst:enumTypeDeclarationIR-non-serializable:iter:2» (arg0 : nameIR) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-non-serializable:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:pattern-iter:1» (arg0 : (_root_.List namedValueIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-serializable:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:3» (arg0 : nameIR) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-serializable:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:4» (arg0 : nameIR) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) (arg3 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-serializable:iter:4» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:6» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List valueFieldIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List valueFieldIR), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-serializable:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_inst:structTypeDeclarationIR:iter:1» (arg0 : (_root_.List typeFieldIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Decl_inst:structTypeDeclarationIR:iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Decl_inst:structTypeDeclarationIR:iter:2» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_inst:structTypeDeclarationIR:iter:2» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_inst:headerTypeDeclarationIR:iter:1» (arg0 : (_root_.List typeFieldIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Decl_inst:headerTypeDeclarationIR:iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Decl_inst:headerTypeDeclarationIR:iter:2» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_inst:headerTypeDeclarationIR:iter:2» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_inst:headerUnionTypeDeclarationIR:iter:1» (arg0 : (_root_.List typeFieldIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Decl_inst:headerUnionTypeDeclarationIR:iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Decl_inst:headerUnionTypeDeclarationIR:iter:2» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_inst:headerUnionTypeDeclarationIR:iter:2» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

end SpecTec
