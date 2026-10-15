import SpecTecDecl0164

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_emptyStatementIR_clauses» (input0 : emptyStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_emptyStatementIR:clause:0»  input0)]


noncomputable def «$lift_exitStatementIR:clause:0» (input0 : exitStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let exitStatement : SpecTec.exitStatement := input0; (.bind (.guard (((SpecTec.exitStatement.«EXIT ';'») : SpecTec.exitStatement) = exitStatement)) (fun (_ : Unit) => (.pure ((((SpecTec.exitStatement.«EXIT ';'») : SpecTec.exitStatement) : SpecTec.exitStatement))))))


noncomputable def «$lift_exitStatementIR_clauses» (input0 : exitStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_exitStatementIR:clause:0»  input0)]


noncomputable def «$unflatten_blockElementStatementList':clause:0» (input0 : SpecTec.blockElementStatementList) (input1 : (_root_.List blockElementStatement)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let blockElementStatementList : SpecTec.blockElementStatementList := input0; (let «blockElementStatement*» : (_root_.List blockElementStatement) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «blockElementStatement*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((blockElementStatementList : SpecTec.blockElementStatementList)))))))


noncomputable def «$unflatten_blockElementStatementList':clause:1» (input0 : SpecTec.blockElementStatementList) (input1 : (_root_.List blockElementStatement)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let blockElementStatementList : SpecTec.blockElementStatementList := input0; (let «blockElementStatement*» : (_root_.List blockElementStatement) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «blockElementStatement*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «blockElementStatement*» with | «exec:2» :: «exec:1» => (let blockElementStatement_h : blockElementStatement := «exec:2»; (let «blockElementStatement_t*» : (_root_.List blockElementStatement) := «exec:1»; (.bind (.call ⟨SpecTec.blockElementStatementList, SpecTecCall.«$unflatten_blockElementStatementList'» ((SpecTec.blockElementStatementList.«% %» blockElementStatementList blockElementStatement_h) : SpecTec.blockElementStatementList) «blockElementStatement_t*»⟩) (fun («exec:3» : SpecTec.blockElementStatementList) => (let «eval:0» : SpecTec.blockElementStatementList := «exec:3»; (.pure ((«eval:0» : SpecTec.blockElementStatementList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_blockElementStatementList'_clauses» (input0 : blockElementStatementList) (input1 : (_root_.List blockElementStatement)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_blockElementStatementList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_blockElementStatementList':clause:1»  input0 input1)]


noncomputable def «$unflatten_blockElementStatementList:clause:0» (input0 : (_root_.List blockElementStatement)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «blockElementStatement*» : (_root_.List blockElementStatement) := input0; (.bind (.call ⟨blockElementStatementList, SpecTecCall.«$unflatten_blockElementStatementList'» ((blockElementStatementList._EMPTY) : blockElementStatementList) «blockElementStatement*»⟩) (fun («exec:1» : blockElementStatementList) => (let «eval:0» : blockElementStatementList := «exec:1»; (.pure ((«eval:0» : blockElementStatementList)))))))


noncomputable def «$unflatten_blockElementStatementList_clauses» (input0 : (_root_.List blockElementStatement)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_blockElementStatementList:clause:0»  input0)]


noncomputable def «$unflatten_switchCaseList':clause:0» (input0 : SpecTec.switchCaseList) (input1 : (_root_.List switchCase)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchCaseList : SpecTec.switchCaseList := input0; (let «switchCase*» : (_root_.List switchCase) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «switchCase*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((switchCaseList : SpecTec.switchCaseList)))))))


noncomputable def «$unflatten_switchCaseList':clause:1» (input0 : SpecTec.switchCaseList) (input1 : (_root_.List switchCase)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchCaseList : SpecTec.switchCaseList := input0; (let «switchCase*» : (_root_.List switchCase) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «switchCase*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «switchCase*» with | «exec:2» :: «exec:1» => (let switchCase_h : switchCase := «exec:2»; (let «switchCase_t*» : (_root_.List switchCase) := «exec:1»; (.bind (.call ⟨SpecTec.switchCaseList, SpecTecCall.«$unflatten_switchCaseList'» ((SpecTec.switchCaseList.«% %» switchCaseList switchCase_h) : SpecTec.switchCaseList) «switchCase_t*»⟩) (fun («exec:3» : SpecTec.switchCaseList) => (let «eval:0» : SpecTec.switchCaseList := «exec:3»; (.pure ((«eval:0» : SpecTec.switchCaseList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_switchCaseList'_clauses» (input0 : switchCaseList) (input1 : (_root_.List switchCase)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_switchCaseList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_switchCaseList':clause:1»  input0 input1)]


noncomputable def «$unflatten_switchCaseList:clause:0» (input0 : (_root_.List switchCase)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «switchCase*» : (_root_.List switchCase) := input0; (.bind (.call ⟨switchCaseList, SpecTecCall.«$unflatten_switchCaseList'» ((switchCaseList._EMPTY) : switchCaseList) «switchCase*»⟩) (fun («exec:1» : switchCaseList) => (let «eval:0» : switchCaseList := «exec:1»; (.pure ((«eval:0» : switchCaseList)))))))


noncomputable def «$unflatten_switchCaseList_clauses» (input0 : (_root_.List switchCase)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_switchCaseList:clause:0»  input0)]


noncomputable def «$lift_breakStatementIR:clause:0» (input0 : breakStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let breakStatement : SpecTec.breakStatement := input0; (.bind (.guard (((SpecTec.breakStatement.«BREAK ';'») : SpecTec.breakStatement) = breakStatement)) (fun (_ : Unit) => (.pure ((((SpecTec.breakStatement.«BREAK ';'») : SpecTec.breakStatement) : SpecTec.breakStatement))))))


noncomputable def «$lift_breakStatementIR_clauses» (input0 : breakStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_breakStatementIR:clause:0»  input0)]


noncomputable def «$lift_continueStatementIR:clause:0» (input0 : continueStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let continueStatement : SpecTec.continueStatement := input0; (.bind (.guard (((SpecTec.continueStatement.«CONTINUE ';'») : SpecTec.continueStatement) = continueStatement)) (fun (_ : Unit) => (.pure ((((SpecTec.continueStatement.«CONTINUE ';'») : SpecTec.continueStatement) : SpecTec.continueStatement))))))


noncomputable def «$lift_continueStatementIR_clauses» (input0 : continueStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_continueStatementIR:clause:0»  input0)]


noncomputable def «$unflatten_objectDeclarationList':clause:0» (input0 : SpecTec.objectDeclarationList) (input1 : (_root_.List objectDeclaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectDeclarationList : SpecTec.objectDeclarationList := input0; (let «objectDeclaration*» : (_root_.List objectDeclaration) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «objectDeclaration*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((objectDeclarationList : SpecTec.objectDeclarationList)))))))


noncomputable def «$unflatten_objectDeclarationList':clause:1» (input0 : SpecTec.objectDeclarationList) (input1 : (_root_.List objectDeclaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectDeclarationList : SpecTec.objectDeclarationList := input0; (let «objectDeclaration*» : (_root_.List objectDeclaration) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «objectDeclaration*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «objectDeclaration*» with | «exec:2» :: «exec:1» => (let objectDeclaration_h : objectDeclaration := «exec:2»; (let «objectDeclaration_t*» : (_root_.List objectDeclaration) := «exec:1»; (.bind (.call ⟨SpecTec.objectDeclarationList, SpecTecCall.«$unflatten_objectDeclarationList'» ((SpecTec.objectDeclarationList.«% %» objectDeclarationList objectDeclaration_h) : SpecTec.objectDeclarationList) «objectDeclaration_t*»⟩) (fun («exec:3» : SpecTec.objectDeclarationList) => (let «eval:0» : SpecTec.objectDeclarationList := «exec:3»; (.pure ((«eval:0» : SpecTec.objectDeclarationList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_objectDeclarationList'_clauses» (input0 : objectDeclarationList) (input1 : (_root_.List objectDeclaration)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_objectDeclarationList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_objectDeclarationList':clause:1»  input0 input1)]


noncomputable def «$unflatten_objectDeclarationList:clause:0» (input0 : (_root_.List objectDeclaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «objectDeclaration*» : (_root_.List objectDeclaration) := input0; (.bind (.call ⟨objectDeclarationList, SpecTecCall.«$unflatten_objectDeclarationList'» ((objectDeclarationList._EMPTY) : objectDeclarationList) «objectDeclaration*»⟩) (fun («exec:1» : objectDeclarationList) => (let «eval:0» : objectDeclarationList := «exec:1»; (.pure ((«eval:0» : objectDeclarationList)))))))


noncomputable def «$unflatten_objectDeclarationList_clauses» (input0 : (_root_.List objectDeclaration)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_objectDeclarationList:clause:0»  input0)]


noncomputable def «$unflatten_typeFieldList':clause:0» (input0 : SpecTec.typeFieldList) (input1 : (_root_.List typeField)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeFieldList : SpecTec.typeFieldList := input0; (let «typeField*» : (_root_.List typeField) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeField*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((typeFieldList : SpecTec.typeFieldList)))))))


noncomputable def «$unflatten_typeFieldList':clause:1» (input0 : SpecTec.typeFieldList) (input1 : (_root_.List typeField)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeFieldList : SpecTec.typeFieldList := input0; (let «typeField*» : (_root_.List typeField) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeField*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeField*» with | «exec:2» :: «exec:1» => (let typeField_h : typeField := «exec:2»; (let «typeField_t*» : (_root_.List typeField) := «exec:1»; (.bind (.call ⟨SpecTec.typeFieldList, SpecTecCall.«$unflatten_typeFieldList'» ((SpecTec.typeFieldList.«% %» typeFieldList typeField_h) : SpecTec.typeFieldList) «typeField_t*»⟩) (fun («exec:3» : SpecTec.typeFieldList) => (let «eval:0» : SpecTec.typeFieldList := «exec:3»; (.pure ((«eval:0» : SpecTec.typeFieldList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_typeFieldList'_clauses» (input0 : typeFieldList) (input1 : (_root_.List typeField)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_typeFieldList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_typeFieldList':clause:1»  input0 input1)]


noncomputable def «$unflatten_typeFieldList:clause:0» (input0 : (_root_.List typeField)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeField*» : (_root_.List typeField) := input0; (.bind (.call ⟨typeFieldList, SpecTecCall.«$unflatten_typeFieldList'» ((typeFieldList._EMPTY) : typeFieldList) «typeField*»⟩) (fun («exec:1» : typeFieldList) => (let «eval:0» : typeFieldList := «exec:1»; (.pure ((«eval:0» : typeFieldList)))))))


noncomputable def «$unflatten_typeFieldList_clauses» (input0 : (_root_.List typeField)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_typeFieldList:clause:0»  input0)]


noncomputable def «$unflatten_externConstructorOrMethodPrototypeList':clause:0» (input0 : SpecTec.externConstructorOrMethodPrototypeList) (input1 : (_root_.List externConstructorOrMethodPrototype)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externConstructorOrMethodPrototypeList : SpecTec.externConstructorOrMethodPrototypeList := input0; (let «externConstructorOrMethodPrototype*» : (_root_.List externConstructorOrMethodPrototype) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «externConstructorOrMethodPrototype*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((externConstructorOrMethodPrototypeList : SpecTec.externConstructorOrMethodPrototypeList)))))))


noncomputable def «$unflatten_externConstructorOrMethodPrototypeList':clause:1» (input0 : SpecTec.externConstructorOrMethodPrototypeList) (input1 : (_root_.List externConstructorOrMethodPrototype)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externConstructorOrMethodPrototypeList : SpecTec.externConstructorOrMethodPrototypeList := input0; (let «externConstructorOrMethodPrototype*» : (_root_.List externConstructorOrMethodPrototype) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «externConstructorOrMethodPrototype*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «externConstructorOrMethodPrototype*» with | «exec:2» :: «exec:1» => (let externConstructorOrMethodPrototype_h : externConstructorOrMethodPrototype := «exec:2»; (let «externConstructorOrMethodPrototype_t*» : (_root_.List externConstructorOrMethodPrototype) := «exec:1»; (.bind (.call ⟨SpecTec.externConstructorOrMethodPrototypeList, SpecTecCall.«$unflatten_externConstructorOrMethodPrototypeList'» ((SpecTec.externConstructorOrMethodPrototypeList.«% %» externConstructorOrMethodPrototypeList externConstructorOrMethodPrototype_h) : SpecTec.externConstructorOrMethodPrototypeList) «externConstructorOrMethodPrototype_t*»⟩) (fun («exec:3» : SpecTec.externConstructorOrMethodPrototypeList) => (let «eval:0» : SpecTec.externConstructorOrMethodPrototypeList := «exec:3»; (.pure ((«eval:0» : SpecTec.externConstructorOrMethodPrototypeList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_externConstructorOrMethodPrototypeList'_clauses» (input0 : externConstructorOrMethodPrototypeList) (input1 : (_root_.List externConstructorOrMethodPrototype)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_externConstructorOrMethodPrototypeList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_externConstructorOrMethodPrototypeList':clause:1»  input0 input1)]


noncomputable def «$unflatten_externConstructorOrMethodPrototypeList:clause:0» (input0 : (_root_.List externConstructorOrMethodPrototype)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «externConstructorOrMethodPrototype*» : (_root_.List externConstructorOrMethodPrototype) := input0; (.bind (.call ⟨externConstructorOrMethodPrototypeList, SpecTecCall.«$unflatten_externConstructorOrMethodPrototypeList'» ((externConstructorOrMethodPrototypeList._EMPTY) : externConstructorOrMethodPrototypeList) «externConstructorOrMethodPrototype*»⟩) (fun («exec:1» : externConstructorOrMethodPrototypeList) => (let «eval:0» : externConstructorOrMethodPrototypeList := «exec:1»; (.pure ((«eval:0» : externConstructorOrMethodPrototypeList)))))))


noncomputable def «$unflatten_externConstructorOrMethodPrototypeList_clauses» (input0 : (_root_.List externConstructorOrMethodPrototype)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_externConstructorOrMethodPrototypeList:clause:0»  input0)]

end SpecTec
