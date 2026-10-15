import SpecTecDecl0424

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_indexAccessExpressionIR» (arg0 : indexAccessExpressionIR) (arg1 : indexAccessExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨indexAccessExpression, SpecTecCall.«$lift_indexAccessExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_sliceAccessExpressionIR» (arg0 : sliceAccessExpressionIR) (arg1 : sliceAccessExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨sliceAccessExpression, SpecTecCall.«$lift_sliceAccessExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_accessExpressionIR» (arg0 : accessExpressionIR) (arg1 : accessExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨accessExpression, SpecTecCall.«$lift_accessExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_argumentListIR» (arg0 : (_root_.List argumentIR)) (arg1 : argumentList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentList, SpecTecCall.«$lift_argumentListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_argumentListIR:case_1:iter:0» (arg0 : (_root_.List argumentIR)) (arg1 : (_root_.List argument)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List argument), SpecTecCall.«$lift_argumentListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_callableTargetIR_as_expression» (arg0 : callableTargetIR) (arg1 : expression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expression, SpecTecCall.«$lift_callableTargetIR_as_expression» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_callExpressionIR» (arg0 : callExpressionIR) (arg1 : callExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callExpression, SpecTecCall.«$lift_callExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parenthesizedExpressionIR» (arg0 : parenthesizedExpressionIR) (arg1 : parenthesizedExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parenthesizedExpression, SpecTecCall.«$lift_parenthesizedExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_expressionIR» (arg0 : expressionIR) (arg1 : expression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expression, SpecTecCall.«$lift_expressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_argumentIR» (arg0 : argumentIR) (arg1 : argument) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argument, SpecTecCall.«$lift_argumentIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_initializerIR» (arg0 : initializerIR) (arg1 : initializer) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨initializer, SpecTecCall.«$lift_initializerIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_initializerOptIR» (arg0 : (_root_.Option initializerIR)) (arg1 : initializerOpt) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨initializerOpt, SpecTecCall.«$lift_initializerOptIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_namedExpressionListIR:case_1:iter:0» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List namedExpression)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List namedExpression), SpecTecCall.«$lift_namedExpressionListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_namedExpressionListIR» (arg0 : (_root_.List namedExpressionIR)) (arg1 : namedExpressionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨namedExpressionList, SpecTecCall.«$lift_namedExpressionListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_simpleKeysetExpressionIR» (arg0 : simpleKeysetExpressionIR) (arg1 : simpleKeysetExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨simpleKeysetExpression, SpecTecCall.«$lift_simpleKeysetExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_simpleKeysetExpressionListIR:case_1:iter:0» (arg0 : (_root_.List simpleKeysetExpressionIR)) (arg1 : (_root_.List simpleKeysetExpression)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List simpleKeysetExpression), SpecTecCall.«$lift_simpleKeysetExpressionListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_simpleKeysetExpressionListIR» (arg0 : (_root_.List simpleKeysetExpressionIR)) (arg1 : simpleKeysetExpressionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨simpleKeysetExpressionList, SpecTecCall.«$lift_simpleKeysetExpressionListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tupleKeysetExpressionIR» (arg0 : tupleKeysetExpressionIR) (arg1 : tupleKeysetExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tupleKeysetExpression, SpecTecCall.«$lift_tupleKeysetExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_keysetExpressionIR» (arg0 : keysetExpressionIR) (arg1 : keysetExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨keysetExpression, SpecTecCall.«$lift_keysetExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typedLvalueIR» (arg0 : typedLvalueIR) (arg1 : lvalue) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨lvalue, SpecTecCall.«$lift_typedLvalueIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_assignmentStatementIR» (arg0 : assignmentStatementIR) (arg1 : assignmentStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨assignmentStatement, SpecTecCall.«$lift_assignmentStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_callableTargetIR_as_lvalue» (arg0 : callableTargetIR) (arg1 : lvalue) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨lvalue, SpecTecCall.«$lift_callableTargetIR_as_lvalue» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_callStatementIR» (arg0 : callStatementIR) (arg1 : callStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callStatement, SpecTecCall.«$lift_callStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_directApplicationStatementIR» (arg0 : directApplicationStatementIR) (arg1 : directApplicationStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨directApplicationStatement, SpecTecCall.«$lift_directApplicationStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_returnStatementIR» (arg0 : returnStatementIR) (arg1 : returnStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨returnStatement, SpecTecCall.«$lift_returnStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_constantDeclarationIR» (arg0 : constantDeclarationIR) (arg1 : constantDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constantDeclaration, SpecTecCall.«$lift_constantDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_variableDeclarationIR» (arg0 : variableDeclarationIR) (arg1 : variableDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨variableDeclaration, SpecTecCall.«$lift_variableDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_switchLabelIR» (arg0 : switchLabelIR) (arg1 : switchLabel) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨switchLabel, SpecTecCall.«$lift_switchLabelIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_statementIR» (arg0 : statementIR) (arg1 : statement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨statement, SpecTecCall.«$lift_statementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_blockElementStatementIR» (arg0 : blockElementStatementIR) (arg1 : blockElementStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨blockElementStatement, SpecTecCall.«$lift_blockElementStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_blockStatementIR» (arg0 : blockStatementIR) (arg1 : blockStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨blockStatement, SpecTecCall.«$lift_blockStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_blockStatementIR:case_1:iter:0» (arg0 : (_root_.List blockElementStatementIR)) (arg1 : (_root_.List blockElementStatement)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List blockElementStatement), SpecTecCall.«$lift_blockStatementIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
