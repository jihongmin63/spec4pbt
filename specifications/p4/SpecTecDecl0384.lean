import SpecTecDecl0383

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$unflatten_switchCaseList'» (arg0 : switchCaseList) (arg1 : (_root_.List switchCase)) (arg2 : switchCaseList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨switchCaseList, SpecTecCall.«$unflatten_switchCaseList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_switchCaseList» (arg0 : (_root_.List switchCase)) (arg1 : switchCaseList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨switchCaseList, SpecTecCall.«$unflatten_switchCaseList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_breakStatementIR» (arg0 : breakStatementIR) (arg1 : breakStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨breakStatement, SpecTecCall.«$lift_breakStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_continueStatementIR» (arg0 : continueStatementIR) (arg1 : continueStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨continueStatement, SpecTecCall.«$lift_continueStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_objectDeclarationList'» (arg0 : objectDeclarationList) (arg1 : (_root_.List objectDeclaration)) (arg2 : objectDeclarationList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨objectDeclarationList, SpecTecCall.«$unflatten_objectDeclarationList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_objectDeclarationList» (arg0 : (_root_.List objectDeclaration)) (arg1 : objectDeclarationList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨objectDeclarationList, SpecTecCall.«$unflatten_objectDeclarationList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_typeFieldList'» (arg0 : typeFieldList) (arg1 : (_root_.List typeField)) (arg2 : typeFieldList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeFieldList, SpecTecCall.«$unflatten_typeFieldList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_typeFieldList» (arg0 : (_root_.List typeField)) (arg1 : typeFieldList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeFieldList, SpecTecCall.«$unflatten_typeFieldList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_externConstructorOrMethodPrototypeList'» (arg0 : externConstructorOrMethodPrototypeList) (arg1 : (_root_.List externConstructorOrMethodPrototype)) (arg2 : externConstructorOrMethodPrototypeList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externConstructorOrMethodPrototypeList, SpecTecCall.«$unflatten_externConstructorOrMethodPrototypeList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_externConstructorOrMethodPrototypeList» (arg0 : (_root_.List externConstructorOrMethodPrototype)) (arg1 : externConstructorOrMethodPrototypeList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externConstructorOrMethodPrototypeList, SpecTecCall.«$unflatten_externConstructorOrMethodPrototypeList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_selectCaseList'» (arg0 : selectCaseList) (arg1 : (_root_.List selectCase)) (arg2 : selectCaseList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨selectCaseList, SpecTecCall.«$unflatten_selectCaseList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_selectCaseList» (arg0 : (_root_.List selectCase)) (arg1 : selectCaseList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨selectCaseList, SpecTecCall.«$unflatten_selectCaseList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_parserBlockElementStatementList'» (arg0 : parserBlockElementStatementList) (arg1 : (_root_.List parserBlockElementStatement)) (arg2 : parserBlockElementStatementList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserBlockElementStatementList, SpecTecCall.«$unflatten_parserBlockElementStatementList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_parserBlockElementStatementList» (arg0 : (_root_.List parserBlockElementStatement)) (arg1 : parserBlockElementStatementList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserBlockElementStatementList, SpecTecCall.«$unflatten_parserBlockElementStatementList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_parserStateList'» (arg0 : parserStateList) (arg1 : (_root_.List parserState)) (arg2 : parserStateList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserStateList, SpecTecCall.«$unflatten_parserStateList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_parserLocalDeclarationList'» (arg0 : parserLocalDeclarationList) (arg1 : (_root_.List parserLocalDeclaration)) (arg2 : parserLocalDeclarationList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserLocalDeclarationList, SpecTecCall.«$unflatten_parserLocalDeclarationList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_parserLocalDeclarationList» (arg0 : (_root_.List parserLocalDeclaration)) (arg1 : parserLocalDeclarationList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserLocalDeclarationList, SpecTecCall.«$unflatten_parserLocalDeclarationList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_constOptIR» (arg0 : constOptIR) (arg1 : constOpt) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨constOpt, SpecTecCall.«$lift_constOptIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_tableKeyList'» (arg0 : tableKeyList) (arg1 : (_root_.List tableKey)) (arg2 : tableKeyList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableKeyList, SpecTecCall.«$unflatten_tableKeyList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_tableKeyList» (arg0 : (_root_.List tableKey)) (arg1 : tableKeyList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableKeyList, SpecTecCall.«$unflatten_tableKeyList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_tableActionList'» (arg0 : tableActionList) (arg1 : (_root_.List tableAction)) (arg2 : tableActionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableActionList, SpecTecCall.«$unflatten_tableActionList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_tableActionList» (arg0 : (_root_.List tableAction)) (arg1 : tableActionList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableActionList, SpecTecCall.«$unflatten_tableActionList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_tableEntryPriorityIR» (arg0 : tableEntryPriorityIR) (arg1 : tableEntryPriority) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntryPriority, SpecTecCall.«$lift_tableEntryPriorityIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_tableEntryList'» (arg0 : tableEntryList) (arg1 : (_root_.List tableEntry)) (arg2 : tableEntryList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntryList, SpecTecCall.«$unflatten_tableEntryList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_tableEntryList» (arg0 : (_root_.List tableEntry)) (arg1 : tableEntryList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntryList, SpecTecCall.«$unflatten_tableEntryList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_tablePropertyList'» (arg0 : tablePropertyList) (arg1 : (_root_.List tableProperty)) (arg2 : tablePropertyList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tablePropertyList, SpecTecCall.«$unflatten_tablePropertyList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_tablePropertyList» (arg0 : (_root_.List tableProperty)) (arg1 : tablePropertyList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tablePropertyList, SpecTecCall.«$unflatten_tablePropertyList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_controlLocalDeclarationList'» (arg0 : controlLocalDeclarationList) (arg1 : (_root_.List controlLocalDeclaration)) (arg2 : controlLocalDeclarationList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨controlLocalDeclarationList, SpecTecCall.«$unflatten_controlLocalDeclarationList'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_controlLocalDeclarationList» (arg0 : (_root_.List controlLocalDeclaration)) (arg1 : controlLocalDeclarationList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨controlLocalDeclarationList, SpecTecCall.«$unflatten_controlLocalDeclarationList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unflatten_p4program'» (arg0 : p4program) (arg1 : (_root_.List declaration)) (arg2 : p4program) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨p4program, SpecTecCall.«$unflatten_p4program'» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unflatten_p4program» (arg0 : (_root_.List declaration)) (arg1 : p4program) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨p4program, SpecTecCall.«$unflatten_p4program» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$empty_typeFrame» (arg0 : typeFrame) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeFrame, SpecTecCall.«$empty_typeFrame» ⟩) 0 (.success (.of (arg0))) finalSupply

end SpecTec
