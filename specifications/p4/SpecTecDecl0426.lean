import SpecTecDecl0425

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_conditionalStatementIR» (arg0 : conditionalStatementIR) (arg1 : conditionalStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨conditionalStatement, SpecTecCall.«$lift_conditionalStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_switchCaseIR» (arg0 : switchCaseIR) (arg1 : switchCase) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨switchCase, SpecTecCall.«$lift_switchCaseIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_switchCaseListIR» (arg0 : (_root_.List switchCaseIR)) (arg1 : switchCaseList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨switchCaseList, SpecTecCall.«$lift_switchCaseListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_switchCaseListIR:case_1:iter:0» (arg0 : (_root_.List switchCaseIR)) (arg1 : (_root_.List switchCase)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List switchCase), SpecTecCall.«$lift_switchCaseListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_switchStatementIR» (arg0 : switchStatementIR) (arg1 : switchStatement) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨switchStatement, SpecTecCall.«$lift_switchStatementIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_blockElementStatementListIR:case_1:iter:0» (arg0 : (_root_.List blockElementStatementIR)) (arg1 : (_root_.List blockElementStatement)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List blockElementStatement), SpecTecCall.«$lift_blockElementStatementListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_blockElementStatementListIR» (arg0 : (_root_.List blockElementStatementIR)) (arg1 : blockElementStatementList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨blockElementStatementList, SpecTecCall.«$lift_blockElementStatementListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_functionPrototypeIR» (arg0 : functionPrototypeIR) (arg1 : functionPrototype) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨functionPrototype, SpecTecCall.«$lift_functionPrototypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_functionDeclarationIR» (arg0 : functionDeclarationIR) (arg1 : functionDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨functionDeclaration, SpecTecCall.«$lift_functionDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_actionDeclarationIR» (arg0 : actionDeclarationIR) (arg1 : actionDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨actionDeclaration, SpecTecCall.«$lift_actionDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_objectDeclarationIR» (arg0 : objectDeclarationIR) (arg1 : objectDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨objectDeclaration, SpecTecCall.«$lift_objectDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_objectDeclarationListIR» (arg0 : (_root_.List objectDeclarationIR)) (arg1 : objectDeclarationList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨objectDeclarationList, SpecTecCall.«$lift_objectDeclarationListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_objectDeclarationListIR:case_1:iter:0» (arg0 : (_root_.List objectDeclarationIR)) (arg1 : (_root_.List objectDeclaration)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List objectDeclaration), SpecTecCall.«$lift_objectDeclarationListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_instantiationIR» (arg0 : instantiationIR) (arg1 : instantiation) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨instantiation, SpecTecCall.«$lift_instantiationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_enumTypeDeclarationIR» (arg0 : enumTypeDeclarationIR) (arg1 : enumTypeDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨enumTypeDeclaration, SpecTecCall.«$lift_enumTypeDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeFieldIR» (arg0 : typeFieldIR) (arg1 : typeField) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeField, SpecTecCall.«$lift_typeFieldIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeFieldListIR:case_1:iter:0» (arg0 : (_root_.List typeFieldIR)) (arg1 : (_root_.List typeField)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeField), SpecTecCall.«$lift_typeFieldListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeFieldListIR» (arg0 : (_root_.List typeFieldIR)) (arg1 : typeFieldList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeFieldList, SpecTecCall.«$lift_typeFieldListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_structTypeDeclarationIR» (arg0 : structTypeDeclarationIR) (arg1 : structTypeDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨structTypeDeclaration, SpecTecCall.«$lift_structTypeDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_headerTypeDeclarationIR» (arg0 : headerTypeDeclarationIR) (arg1 : headerTypeDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨headerTypeDeclaration, SpecTecCall.«$lift_headerTypeDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_headerUnionTypeDeclarationIR» (arg0 : headerUnionTypeDeclarationIR) (arg1 : headerUnionTypeDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨headerUnionTypeDeclaration, SpecTecCall.«$lift_headerUnionTypeDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_derivedTypeDeclarationIR» (arg0 : derivedTypeDeclarationIR) (arg1 : derivedTypeDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨derivedTypeDeclaration, SpecTecCall.«$lift_derivedTypeDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_externFunctionDeclarationIR» (arg0 : externFunctionDeclarationIR) (arg1 : externFunctionDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externFunctionDeclaration, SpecTecCall.«$lift_externFunctionDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_externConstructorPrototypeIR» (arg0 : externConstructorPrototypeIR) (arg1 : externConstructorPrototype) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externConstructorPrototype, SpecTecCall.«$lift_externConstructorPrototypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_externMethodPrototypeIR» (arg0 : externMethodPrototypeIR) (arg1 : externMethodPrototype) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externMethodPrototype, SpecTecCall.«$lift_externMethodPrototypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_externObjectDeclarationIR:case_1:iter:2» (arg0 : (_root_.List externConstructorPrototypeIR)) (arg1 : (_root_.List externConstructorPrototype)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List externConstructorPrototype), SpecTecCall.«$lift_externObjectDeclarationIR:case_1:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_externObjectDeclarationIR:case_1:iter:4» (arg0 : (_root_.List externMethodPrototypeIR)) (arg1 : (_root_.List externMethodPrototype)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List externMethodPrototype), SpecTecCall.«$lift_externObjectDeclarationIR:case_1:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_externObjectDeclarationIR» (arg0 : externObjectDeclarationIR) (arg1 : externObjectDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externObjectDeclaration, SpecTecCall.«$lift_externObjectDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_externDeclarationIR» (arg0 : externDeclarationIR) (arg1 : externDeclaration) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨externDeclaration, SpecTecCall.«$lift_externDeclarationIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_selectCaseIR» (arg0 : selectCaseIR) (arg1 : selectCase) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨selectCase, SpecTecCall.«$lift_selectCaseIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_selectCaseListIR:case_1:iter:0» (arg0 : (_root_.List selectCaseIR)) (arg1 : (_root_.List selectCase)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List selectCase), SpecTecCall.«$lift_selectCaseListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_selectCaseListIR» (arg0 : (_root_.List selectCaseIR)) (arg1 : selectCaseList) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨selectCaseList, SpecTecCall.«$lift_selectCaseListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
