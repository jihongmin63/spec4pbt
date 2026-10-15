import SpecTecDecl0393

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Expr_ok:multiple-default:iter:9» (arg0 : (_root_.List typedExpressionIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:multiple-default:iter:9» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Expr_ok:multiple-default:iter:11» (arg0 : (_root_.List typedExpressionIR)) (arg1 : (_root_.List ctk)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List ctk), SpecTecCall.«Expr_ok:multiple-default:iter:11» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Expr_ok:multiple-default:iter:13» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Expr_ok:multiple-default:iter:13» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_ok:multiple-default:iter:16» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List typedExpressionIR)) (arg2 : (_root_.List namedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List namedExpressionIR), SpecTecCall.«Expr_ok:multiple-default:iter:16» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_ok:serenum:pattern-iter:8» (arg0 : (_root_.List valueFieldIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List value) × (_root_.List nameIR)), SpecTecCall.«Expr_ok:serenum:pattern-iter:8» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_ok:struct:pattern-iter:6» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Expr_ok:struct:pattern-iter:6» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Expr_ok:struct:iter:9» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (_root_.String × typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Expr_ok:struct:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_ok:header:pattern-iter:6» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Expr_ok:header:pattern-iter:6» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Expr_ok:header:iter:9» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (_root_.String × typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Expr_ok:header:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_ok:header-union:pattern-iter:6» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Expr_ok:header-union:pattern-iter:6» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Expr_ok:header-union:iter:9» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (_root_.String × typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Expr_ok:header-union:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_ok:non-typeArgumentList-static_assert:iter:2» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:non-typeArgumentList-static_assert:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Expr_ok:non-typeArgumentList:iter:2» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:non-typeArgumentList:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Expr_ok:typeArgumentList:iter:2» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:typeArgumentList:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Expr_ok:prefixedTypeName:iter:3» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:prefixedTypeName:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Expr_ok:specializedType:iter:3» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:specializedType:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Lvalue_ok:structTypeIR:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Lvalue_ok:structTypeIR:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Lvalue_ok:structTypeIR:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (_root_.String × typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Lvalue_ok:structTypeIR:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Lvalue_ok:headerTypeIR:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Lvalue_ok:headerTypeIR:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Lvalue_ok:headerTypeIR:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (_root_.String × typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Lvalue_ok:headerTypeIR:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Lvalue_ok:headerUnionTypeIR:pattern-iter:2» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Lvalue_ok:headerUnionTypeIR:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Lvalue_ok:headerUnionTypeIR:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List (_root_.String × typeIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Lvalue_ok:headerUnionTypeIR:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Stmt_ok:callStatement-no-typeArgumentList-static_assert:iter:1» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Stmt_ok:callStatement-no-typeArgumentList-static_assert:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Stmt_ok:callStatement-no-typeArgumentList:iter:1» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Stmt_ok:callStatement-no-typeArgumentList:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Stmt_ok:callStatement-typeArgumentList:iter:1» (arg0 : (_root_.List typeId)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«Stmt_ok:callStatement-typeArgumentList:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «ParserSelect_ok:rule:iter:4» (arg0 : (_root_.List typedExpressionIR)) (arg1 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeIR), SpecTecCall.«ParserSelect_ok:rule:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «ParserStateList_ok:rule:iter:1» (arg0 : (_root_.List parserState)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List parserBlockElementStatementList)) (arg3 : (_root_.List transitionStatement)) (arg4 : (_root_.List name)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List parserBlockElementStatementList) × ((_root_.List transitionStatement) × (_root_.List name)))), SpecTecCall.«ParserStateList_ok:rule:iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, arg4)))))) finalSupply


noncomputable def «ParserStateList_ok:rule:iter:2» (arg0 : (_root_.List name)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«ParserStateList_ok:rule:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «TableDefaultAction_ok:prefixedNonTypeName-argumentList:iter:4» (arg0 : (_root_.List argumentIR)) (arg1 : (_root_.List argumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«TableDefaultAction_ok:prefixedNonTypeName-argumentList:iter:4» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «TableEntry_action_ok:prefixedNonTypeName-argumentList:iter:2» (arg0 : (_root_.List argumentIR)) (arg1 : (_root_.List argumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«TableEntry_action_ok:prefixedNonTypeName-argumentList:iter:2» arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «TableType_ok:rule:pattern-iter:1» (arg0 : (_root_.List matchAction)) (arg1 : (_root_.List argumentListIR)) (arg2 : (_root_.List (_root_.List parameterIR))) (arg3 : (_root_.List prefixedNameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List argumentListIR) × ((_root_.List (_root_.List parameterIR)) × (_root_.List prefixedNameIR))), SpecTecCall.«TableType_ok:rule:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «TableType_ok:rule:iter:5» (arg0 : typeId) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«TableType_ok:rule:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
