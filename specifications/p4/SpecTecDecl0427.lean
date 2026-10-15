import SpecTecDecl0426

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_selectExpressionIR» (arg0 : selectExpressionIR) (arg1 : selectExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨selectExpression, SpecTecCall.«$lift_selectExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_stateExpressionIR» (arg0 : stateExpressionIR) (arg1 : stateExpression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨stateExpression, SpecTecCall.«$lift_stateExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_transitionStatementIR» (arg0 : transitionStatementIR) (arg1 : transitionStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨transitionStatement, SpecTecCall.«$lift_transitionStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeIR_as_valueSetType» (arg0 : typeIR) (arg1 : valueSetType) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨valueSetType, SpecTecCall.«$lift_typeIR_as_valueSetType» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_valueSetDeclarationIR» (arg0 : valueSetDeclarationIR) (arg1 : valueSetDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨valueSetDeclaration, SpecTecCall.«$lift_valueSetDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserTypeDeclarationIR» (arg0 : parserTypeDeclarationIR) (arg1 : parserTypeDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserTypeDeclaration, SpecTecCall.«$lift_parserTypeDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserStatementIR» (arg0 : parserStatementIR) (arg1 : parserStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserStatement, SpecTecCall.«$lift_parserStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserBlockElementStatementIR» (arg0 : parserBlockElementStatementIR) (arg1 : parserBlockElementStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserBlockElementStatement, SpecTecCall.«$lift_parserBlockElementStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserBlockElementStatementListIR» (arg0 : (_root_.List parserBlockElementStatementIR)) (arg1 : parserBlockElementStatementList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserBlockElementStatementList, SpecTecCall.«$lift_parserBlockElementStatementListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserBlockElementStatementListIR:case_1:iter:0» (arg0 : (_root_.List parserBlockElementStatementIR)) (arg1 : (_root_.List parserBlockElementStatement)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parserBlockElementStatement), SpecTecCall.«$lift_parserBlockElementStatementListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserBlockStatementIR» (arg0 : parserBlockStatementIR) (arg1 : parserBlockStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserBlockStatement, SpecTecCall.«$lift_parserBlockStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserConditionalStatementIR» (arg0 : parserConditionalStatementIR) (arg1 : parserConditionalStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserConditionalStatement, SpecTecCall.«$lift_parserConditionalStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserStateIR» (arg0 : parserStateIR) (arg1 : parserState) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserState, SpecTecCall.«$lift_parserStateIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserStateListIR:case_1:iter:0» (arg0 : (_root_.List parserStateIR)) (arg1 : (_root_.List parserState)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parserState), SpecTecCall.«$lift_parserStateListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserStateListIR» (arg0 : (_root_.List parserStateIR)) (arg1 : parserStateList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserStateList, SpecTecCall.«$lift_parserStateListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserLocalDeclarationIR» (arg0 : parserLocalDeclarationIR) (arg1 : parserLocalDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserLocalDeclaration, SpecTecCall.«$lift_parserLocalDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserLocalDeclarationListIR:case_1:iter:0» (arg0 : (_root_.List parserLocalDeclarationIR)) (arg1 : (_root_.List parserLocalDeclaration)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parserLocalDeclaration), SpecTecCall.«$lift_parserLocalDeclarationListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserLocalDeclarationListIR» (arg0 : (_root_.List parserLocalDeclarationIR)) (arg1 : parserLocalDeclarationList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserLocalDeclarationList, SpecTecCall.«$lift_parserLocalDeclarationListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_parserDeclarationIR» (arg0 : parserDeclarationIR) (arg1 : parserDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserDeclaration, SpecTecCall.«$lift_parserDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableKeyIR» (arg0 : tableKeyIR) (arg1 : tableKey) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableKey, SpecTecCall.«$lift_tableKeyIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableKeyListIR:case_1:iter:0» (arg0 : (_root_.List tableKeyIR)) (arg1 : (_root_.List tableKey)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List tableKey), SpecTecCall.«$lift_tableKeyListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableKeyListIR» (arg0 : (_root_.List tableKeyIR)) (arg1 : tableKeyList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableKeyList, SpecTecCall.«$lift_tableKeyListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableActionReferenceIR» (arg0 : tableActionReferenceIR) (arg1 : tableActionReference) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableActionReference, SpecTecCall.«$lift_tableActionReferenceIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableActionReferenceIR_as_expression» (arg0 : tableActionReferenceIR) (arg1 : expression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expression, SpecTecCall.«$lift_tableActionReferenceIR_as_expression» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableActionIR» (arg0 : tableActionIR) (arg1 : tableAction) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableAction, SpecTecCall.«$lift_tableActionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableActionListIR:case_1:iter:0» (arg0 : (_root_.List tableActionIR)) (arg1 : (_root_.List tableAction)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List tableAction), SpecTecCall.«$lift_tableActionListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableActionListIR» (arg0 : (_root_.List tableActionIR)) (arg1 : tableActionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableActionList, SpecTecCall.«$lift_tableActionListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableEntryIR» (arg0 : tableEntryIR) (arg1 : tableEntry) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntry, SpecTecCall.«$lift_tableEntryIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableEntryListIR:case_1:iter:0» (arg0 : (_root_.List tableEntryIR)) (arg1 : (_root_.List tableEntry)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List tableEntry), SpecTecCall.«$lift_tableEntryListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableEntryListIR» (arg0 : (_root_.List tableEntryIR)) (arg1 : tableEntryList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntryList, SpecTecCall.«$lift_tableEntryListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableCustomPropertyIR» (arg0 : tableCustomPropertyIR) (arg1 : tableProperty) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableProperty, SpecTecCall.«$lift_tableCustomPropertyIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableKeysPropertyIR» (arg0 : tableKeysPropertyIR) (arg1 : tableProperty) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableProperty, SpecTecCall.«$lift_tableKeysPropertyIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
