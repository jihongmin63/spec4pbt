import SpecTecDecl0404

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Call_eval:controlApplyMethodCallee-cont:iter:4» (arg0 : (_root_.List actionDef)) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List (pair callTargetId callableDef))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId callableDef)), SpecTecCall.«Call_eval:controlApplyMethodCallee-cont:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_argumentListNonEmpty» (arg0 : (_root_.List argument)) (arg1 : argumentListNonEmpty) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentListNonEmpty, SpecTecCall.«$unflatten_argumentListNonEmpty» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_argumentList» (arg0 : (_root_.List argument)) (arg1 : argumentList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentList, SpecTecCall.«$unflatten_argumentList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:9» (arg0 : enumTypeDefIR) (arg1 : (_root_.List value)) (arg2 : (_root_.List varTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List varTypeIR), SpecTecCall.«Decl_ok:enumTypeDeclaration-non-serializable:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:7» (arg0 : enumTypeDefIR) (arg1 : (_root_.List value)) (arg2 : (_root_.List varTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List varTypeIR), SpecTecCall.«Decl_ok:enumTypeDeclaration-serializable:iter:7» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_expressionList» (arg0 : (_root_.List expression)) (arg1 : expressionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expressionList, SpecTecCall.«$unflatten_expressionList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_nameIR_as_tableCustomName» (arg0 : nameIR) (arg1 : tableCustomName) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableCustomName, SpecTecCall.«$lift_nameIR_as_tableCustomName» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_constantInitializerOptIR_as_initializerOpt» (arg0 : (_root_.Option constantInitializerIR)) (arg1 : initializerOpt) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨initializerOpt, SpecTecCall.«$lift_constantInitializerOptIR_as_initializerOpt» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_nameList» (arg0 : (_root_.List name)) (arg1 : nameList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨nameList, SpecTecCall.«$unflatten_nameList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_typeParameterList» (arg0 : (_root_.List typeParameter)) (arg1 : typeParameterList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeParameterList, SpecTecCall.«$unflatten_typeParameterList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_typeParameterListOpt» (arg0 : (_root_.List typeParameter)) (arg1 : typeParameterListOpt) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeParameterListOpt, SpecTecCall.«$unflatten_typeParameterListOpt» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_namedExpressionList» (arg0 : (_root_.List namedExpression)) (arg1 : namedExpressionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨namedExpressionList, SpecTecCall.«$unflatten_namedExpressionList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_recordElementExpression» (arg0 : (_root_.List namedExpression)) (arg1 : recordElementExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨recordElementExpression, SpecTecCall.«$unflatten_recordElementExpression» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_recordElementExpression_with_default» (arg0 : (_root_.List namedExpression)) (arg1 : recordElementExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨recordElementExpression, SpecTecCall.«$unflatten_recordElementExpression_with_default» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_nameListIR_as_nonTypeNameList:case_1:iter:0» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List name)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List name), SpecTecCall.«$lift_nameListIR_as_nonTypeNameList:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_nameListIR_as_nonTypeNameList» (arg0 : (_root_.List nameIR)) (arg1 : nameList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨nameList, SpecTecCall.«$lift_nameListIR_as_nonTypeNameList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_nameIR_as_member» (arg0 : nameIR) (arg1 : member) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨member, SpecTecCall.«$lift_nameIR_as_member» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_namedValueIR» (arg0 : namedValueIR) (arg1 : namedExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨namedExpression, SpecTecCall.«$lift_namedValueIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_namedValueListIR:case_1:iter:0» (arg0 : (_root_.List namedValueIR)) (arg1 : (_root_.List namedExpression)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List namedExpression), SpecTecCall.«$lift_namedValueListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_namedValueListIR» (arg0 : (_root_.List namedValueIR)) (arg1 : namedExpressionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨namedExpressionList, SpecTecCall.«$lift_namedValueListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_errorAccessExpressionIR» (arg0 : errorAccessExpressionIR) (arg1 : errorAccessExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨errorAccessExpression, SpecTecCall.«$lift_errorAccessExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_errorDeclarationIR» (arg0 : errorDeclarationIR) (arg1 : errorDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨errorDeclaration, SpecTecCall.«$lift_errorDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_matchKindDeclarationIR» (arg0 : matchKindDeclarationIR) (arg1 : matchKindDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨matchKindDeclaration, SpecTecCall.«$lift_matchKindDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_nonEmptyParameterList» (arg0 : (_root_.List parameter)) (arg1 : nonEmptyParameterList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨nonEmptyParameterList, SpecTecCall.«$unflatten_nonEmptyParameterList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_parameterList» (arg0 : (_root_.List parameter)) (arg1 : parameterList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parameterList, SpecTecCall.«$unflatten_parameterList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_constructorParameterList» (arg0 : (_root_.List constructorParameter)) (arg1 : constructorParameterListOpt) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constructorParameterListOpt, SpecTecCall.«$unflatten_constructorParameterList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_parserStateList» (arg0 : (_root_.List parserState)) (arg1 : parserStateList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserStateList, SpecTecCall.«$unflatten_parserStateList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_realTypeArgumentList» (arg0 : (_root_.List realTypeArgument)) (arg1 : realTypeArgumentList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨realTypeArgumentList, SpecTecCall.«$unflatten_realTypeArgumentList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_simpleKeysetExpressionList» (arg0 : (_root_.List simpleKeysetExpression)) (arg1 : simpleKeysetExpressionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨simpleKeysetExpressionList, SpecTecCall.«$unflatten_simpleKeysetExpressionList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «TableType_ok:rule:iter:6» (arg0 : tableMetadataEnumTypeIR) (arg1 : (_root_.List value)) (arg2 : (_root_.List varTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List varTypeIR), SpecTecCall.«TableType_ok:rule:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_typeArgumentList» (arg0 : (_root_.List typeArgument)) (arg1 : typeArgumentList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeArgumentList, SpecTecCall.«$unflatten_typeArgumentList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeParameterIR» (arg0 : typeParameterIR) (arg1 : typeParameter) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeParameter, SpecTecCall.«$lift_typeParameterIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
