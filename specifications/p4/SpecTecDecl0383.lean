import SpecTecDecl0382

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$find_non_overloadeds:case_2:iter:7» (V : Type) (arg0 : (_root_.List V)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (callTargetId × V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (callTargetId × V)), SpecTecCall.«$find_non_overloadeds:case_2:iter:7» V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_non_overloadeds:case_3:pattern-iter:0» (V : Type) (arg0 : (_root_.List (pair callTargetId V))) (arg1 : (_root_.List V)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_3:pattern-iter:0» V arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_non_overloadeds:case_3:iter:2» (V : Type) (arg0 : (_root_.List V)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_non_overloadeds:case_3:iter:2» V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_non_overloadeds:case_3:pattern-iter:5» (V : Type) (arg0 : (_root_.List (callTargetId × V))) (arg1 : (_root_.List V)) (arg2 : (_root_.List callableId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_3:pattern-iter:5» V arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_non_overloadeds:case_3:iter:7» (V : Type) (arg0 : (_root_.List V)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (callTargetId × V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (callTargetId × V)), SpecTecCall.«$find_non_overloadeds:case_3:iter:7» V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_non_overloadeds» (V : Type) (arg0 : (map callableId V)) (arg1 : nameIR) (arg2 : (_root_.List (callableId × V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (callableId × V)), SpecTecCall.«$find_non_overloadeds» V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_non_overloaded» (V_T : Type) (arg0 : (map callableId V_T)) (arg1 : nameIR) (arg2 : (_root_.Option (callableId × V_T))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (callableId × V_T)), SpecTecCall.«$find_non_overloaded» V_T arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$name_annotation:case_1:iter:3» (arg0 : (_root_.List (_root_.Option nameIR))) (arg1 : (_root_.List (_root_.List _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List _root_.String)), SpecTecCall.«$name_annotation:case_1:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subexpressions_of_expressionIR:case_7:pattern-iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List typedExpressionIR)), SpecTecCall.«$subexpressions_of_expressionIR:case_7:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$subexpressions_of_expressionIR:case_8:pattern-iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List typedExpressionIR)), SpecTecCall.«$subexpressions_of_expressionIR:case_8:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$sink» (T : Type) (arg0 : T) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨T, SpecTecCall.«$sink» T⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$lift_nameIR_as_identifier» (arg0 : nameIR) (arg1 : identifier) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨identifier, SpecTecCall.«$lift_nameIR_as_identifier» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_nameIR_as_typeIdentifier» (arg0 : nameIR) (arg1 : typeIdentifier) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIdentifier, SpecTecCall.«$lift_nameIR_as_typeIdentifier» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_nameIR_as_nonTypeName» (arg0 : nameIR) (arg1 : nonTypeName) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_nameIR_as_typeName» (arg0 : nameIR) (arg1 : typeName) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeName, SpecTecCall.«$lift_nameIR_as_typeName» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_nameList'» (arg0 : nameList) (arg1 : (_root_.List name)) (arg2 : nameList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨nameList, SpecTecCall.«$unflatten_nameList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$lift_value» (arg0 : value) (arg1 : expression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expression, SpecTecCall.«$lift_value» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_typeParameterList'» (arg0 : typeParameterList) (arg1 : (_root_.List typeParameter)) (arg2 : typeParameterList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeParameterList, SpecTecCall.«$unflatten_typeParameterList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_nonEmptyParameterList'» (arg0 : nonEmptyParameterList) (arg1 : (_root_.List parameter)) (arg2 : nonEmptyParameterList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨nonEmptyParameterList, SpecTecCall.«$unflatten_nonEmptyParameterList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$lift_constantInitializerIR_as_initializer» (arg0 : constantInitializerIR) (arg1 : initializer) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨initializer, SpecTecCall.«$lift_constantInitializerIR_as_initializer» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_namedExpressionList'» (arg0 : namedExpressionList) (arg1 : (_root_.List namedExpression)) (arg2 : namedExpressionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨namedExpressionList, SpecTecCall.«$unflatten_namedExpressionList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$lift_literalExpressionIR» (arg0 : literalExpressionIR) (arg1 : literalExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨literalExpression, SpecTecCall.«$lift_literalExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_defaultExpressionIR» (arg0 : defaultExpressionIR) (arg1 : defaultExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨defaultExpression, SpecTecCall.«$lift_defaultExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_expressionList'» (arg0 : expressionList) (arg1 : (_root_.List expression)) (arg2 : expressionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expressionList, SpecTecCall.«$unflatten_expressionList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_simpleKeysetExpressionList'» (arg0 : simpleKeysetExpressionList) (arg1 : (_root_.List simpleKeysetExpression)) (arg2 : simpleKeysetExpressionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨simpleKeysetExpressionList, SpecTecCall.«$unflatten_simpleKeysetExpressionList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_realTypeArgumentList'» (arg0 : realTypeArgumentList) (arg1 : (_root_.List realTypeArgument)) (arg2 : realTypeArgumentList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨realTypeArgumentList, SpecTecCall.«$unflatten_realTypeArgumentList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_typeArgumentList'» (arg0 : typeArgumentList) (arg1 : (_root_.List typeArgument)) (arg2 : typeArgumentList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeArgumentList, SpecTecCall.«$unflatten_typeArgumentList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_argumentListNonEmpty'» (arg0 : argumentListNonEmpty) (arg1 : (_root_.List argument)) (arg2 : argumentListNonEmpty) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentListNonEmpty, SpecTecCall.«$unflatten_argumentListNonEmpty'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$lift_emptyStatementIR» (arg0 : emptyStatementIR) (arg1 : emptyStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨emptyStatement, SpecTecCall.«$lift_emptyStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_exitStatementIR» (arg0 : exitStatementIR) (arg1 : exitStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨exitStatement, SpecTecCall.«$lift_exitStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_blockElementStatementList'» (arg0 : blockElementStatementList) (arg1 : (_root_.List blockElementStatement)) (arg2 : blockElementStatementList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨blockElementStatementList, SpecTecCall.«$unflatten_blockElementStatementList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_blockElementStatementList» (arg0 : (_root_.List blockElementStatement)) (arg1 : blockElementStatementList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨blockElementStatementList, SpecTecCall.«$unflatten_blockElementStatementList» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
