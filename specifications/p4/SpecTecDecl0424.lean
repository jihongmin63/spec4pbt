import SpecTecDecl0423

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$sizeof_maxSizeInBits» (arg0 : typeIR) (arg1 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$sizeof_maxSizeInBits» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof_maxSizeInBytes» (arg0 : typeIR) (arg1 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$sizeof_maxSizeInBytes» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$sizeof» (arg0 : typeIR) (arg1 : id) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$sizeof» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$lift_typeIR» (arg0 : typeIR) (arg1 : type) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨type, SpecTecCall.«$lift_typeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeArgumentListIR» (arg0 : (_root_.List typeArgumentIR)) (arg1 : typeArgumentList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeArgumentList, SpecTecCall.«$lift_typeArgumentListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeArgumentListIR:case_1:iter:0» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List typeArgument)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgument), SpecTecCall.«$lift_typeArgumentListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeArgumentIR» (arg0 : typeArgumentIR) (arg1 : typeArgument) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeArgument, SpecTecCall.«$lift_typeArgumentIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_dataTypeIR» (arg0 : dataTypeIR) (arg1 : type) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨type, SpecTecCall.«$lift_dataTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeArgumentIR_as_realTypeArgument» (arg0 : typeArgumentIR) (arg1 : realTypeArgument) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨realTypeArgument, SpecTecCall.«$lift_typeArgumentIR_as_realTypeArgument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeIR_as_typeOrVoid» (arg0 : typeIR) (arg1 : typeOrVoid) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeOrVoid, SpecTecCall.«$lift_typeIR_as_typeOrVoid» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parameterIR» (arg0 : parameterIR) (arg1 : parameter) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parameter, SpecTecCall.«$lift_parameterIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parameterListIR:case_1:iter:0» (arg0 : (_root_.List parameterIR)) (arg1 : (_root_.List parameter)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameter), SpecTecCall.«$lift_parameterListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parameterListIR» (arg0 : (_root_.List parameterIR)) (arg1 : parameterList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parameterList, SpecTecCall.«$lift_parameterListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_constructorParameterIR» (arg0 : constructorParameterIR) (arg1 : constructorParameter) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constructorParameter, SpecTecCall.«$lift_constructorParameterIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_constructorParameterListIR:case_1:iter:0» (arg0 : (_root_.List constructorParameterIR)) (arg1 : (_root_.List constructorParameter)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List constructorParameter), SpecTecCall.«$lift_constructorParameterListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_constructorParameterListIR» (arg0 : (_root_.List constructorParameterIR)) (arg1 : constructorParameterListOpt) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constructorParameterListOpt, SpecTecCall.«$lift_constructorParameterListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeArgumentListIR_as_realTypeArgumentList:case_1:iter:0» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List realTypeArgument)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List realTypeArgument), SpecTecCall.«$lift_typeArgumentListIR_as_realTypeArgumentList:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeArgumentListIR_as_realTypeArgumentList» (arg0 : (_root_.List typeArgumentIR)) (arg1 : realTypeArgumentList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨realTypeArgumentList, SpecTecCall.«$lift_typeArgumentListIR_as_realTypeArgumentList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typedExpressionIR» (arg0 : typedExpressionIR) (arg1 : expression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_namedExpressionIR» (arg0 : namedExpressionIR) (arg1 : namedExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨namedExpression, SpecTecCall.«$lift_namedExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typedExpressionListIR» (arg0 : (_root_.List typedExpressionIR)) (arg1 : expressionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expressionList, SpecTecCall.«$lift_typedExpressionListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typedExpressionListIR:case_1:iter:0» (arg0 : (_root_.List typedExpressionIR)) (arg1 : (_root_.List expression)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List expression), SpecTecCall.«$lift_typedExpressionListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_unaryExpressionIR» (arg0 : unaryExpressionIR) (arg1 : unaryExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨unaryExpression, SpecTecCall.«$lift_unaryExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_binaryExpressionIR» (arg0 : binaryExpressionIR) (arg1 : binaryExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨binaryExpression, SpecTecCall.«$lift_binaryExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_ternaryExpressionIR» (arg0 : ternaryExpressionIR) (arg1 : ternaryExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨ternaryExpression, SpecTecCall.«$lift_ternaryExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_castExpressionIR» (arg0 : castExpressionIR) (arg1 : expression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expression, SpecTecCall.«$lift_castExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_dataExpressionIR» (arg0 : dataExpressionIR) (arg1 : dataExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨dataExpression, SpecTecCall.«$lift_dataExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_dataExpressionIR:case_3:iter:1» (arg0 : (_root_.List typedExpressionIR)) (arg1 : (_root_.List expression)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List expression), SpecTecCall.«$lift_dataExpressionIR:case_3:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_dataExpressionIR:case_4:iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List namedExpression)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List namedExpression), SpecTecCall.«$lift_dataExpressionIR:case_4:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_dataExpressionIR:case_5:iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List namedExpression)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List namedExpression), SpecTecCall.«$lift_dataExpressionIR:case_5:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_memberAccessBaseIR» (arg0 : memberAccessBaseIR) (arg1 : memberAccessBase) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨memberAccessBase, SpecTecCall.«$lift_memberAccessBaseIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_memberAccessExpressionIR» (arg0 : memberAccessExpressionIR) (arg1 : memberAccessExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨memberAccessExpression, SpecTecCall.«$lift_memberAccessExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
