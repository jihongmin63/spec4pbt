import SpecTecDecl0165

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$unflatten_selectCaseList':clause:0» (input0 : SpecTec.selectCaseList) (input1 : (_root_.List selectCase)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let selectCaseList : SpecTec.selectCaseList := input0; (let «selectCase*» : (_root_.List selectCase) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «selectCase*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((selectCaseList : SpecTec.selectCaseList)))))))


noncomputable def «$unflatten_selectCaseList':clause:1» (input0 : SpecTec.selectCaseList) (input1 : (_root_.List selectCase)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let selectCaseList : SpecTec.selectCaseList := input0; (let «selectCase*» : (_root_.List selectCase) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «selectCase*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «selectCase*» with | «exec:2» :: «exec:1» => (let selectCase_h : selectCase := «exec:2»; (let «selectCase_t*» : (_root_.List selectCase) := «exec:1»; (.bind (.call ⟨SpecTec.selectCaseList, SpecTecCall.«$unflatten_selectCaseList'» ((SpecTec.selectCaseList.«% %» selectCaseList selectCase_h) : SpecTec.selectCaseList) «selectCase_t*»⟩) (fun («exec:3» : SpecTec.selectCaseList) => (let «eval:0» : SpecTec.selectCaseList := «exec:3»; (.pure ((«eval:0» : SpecTec.selectCaseList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_selectCaseList'_clauses» (input0 : selectCaseList) (input1 : (_root_.List selectCase)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_selectCaseList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_selectCaseList':clause:1»  input0 input1)]


noncomputable def «$unflatten_selectCaseList:clause:0» (input0 : (_root_.List selectCase)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «selectCase*» : (_root_.List selectCase) := input0; (.bind (.call ⟨selectCaseList, SpecTecCall.«$unflatten_selectCaseList'» ((selectCaseList._EMPTY) : selectCaseList) «selectCase*»⟩) (fun («exec:1» : selectCaseList) => (let «eval:0» : selectCaseList := «exec:1»; (.pure ((«eval:0» : selectCaseList)))))))


noncomputable def «$unflatten_selectCaseList_clauses» (input0 : (_root_.List selectCase)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_selectCaseList:clause:0»  input0)]


noncomputable def «$unflatten_parserBlockElementStatementList':clause:0» (input0 : SpecTec.parserBlockElementStatementList) (input1 : (_root_.List parserBlockElementStatement)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserBlockElementStatementList : SpecTec.parserBlockElementStatementList := input0; (let «parserBlockElementStatement*» : (_root_.List parserBlockElementStatement) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parserBlockElementStatement*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((parserBlockElementStatementList : SpecTec.parserBlockElementStatementList)))))))


noncomputable def «$unflatten_parserBlockElementStatementList':clause:1» (input0 : SpecTec.parserBlockElementStatementList) (input1 : (_root_.List parserBlockElementStatement)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserBlockElementStatementList : SpecTec.parserBlockElementStatementList := input0; (let «parserBlockElementStatement*» : (_root_.List parserBlockElementStatement) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parserBlockElementStatement*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parserBlockElementStatement*» with | «exec:2» :: «exec:1» => (let parserBlockElementStatement_h : parserBlockElementStatement := «exec:2»; (let «parserBlockElementStatement_t*» : (_root_.List parserBlockElementStatement) := «exec:1»; (.bind (.call ⟨SpecTec.parserBlockElementStatementList, SpecTecCall.«$unflatten_parserBlockElementStatementList'» ((SpecTec.parserBlockElementStatementList.«% %» parserBlockElementStatementList parserBlockElementStatement_h) : SpecTec.parserBlockElementStatementList) «parserBlockElementStatement_t*»⟩) (fun («exec:3» : SpecTec.parserBlockElementStatementList) => (let «eval:0» : SpecTec.parserBlockElementStatementList := «exec:3»; (.pure ((«eval:0» : SpecTec.parserBlockElementStatementList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_parserBlockElementStatementList'_clauses» (input0 : parserBlockElementStatementList) (input1 : (_root_.List parserBlockElementStatement)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_parserBlockElementStatementList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_parserBlockElementStatementList':clause:1»  input0 input1)]


noncomputable def «$unflatten_parserBlockElementStatementList:clause:0» (input0 : (_root_.List parserBlockElementStatement)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parserBlockElementStatement*» : (_root_.List parserBlockElementStatement) := input0; (.bind (.call ⟨parserBlockElementStatementList, SpecTecCall.«$unflatten_parserBlockElementStatementList'» ((parserBlockElementStatementList._EMPTY) : parserBlockElementStatementList) «parserBlockElementStatement*»⟩) (fun («exec:1» : parserBlockElementStatementList) => (let «eval:0» : parserBlockElementStatementList := «exec:1»; (.pure ((«eval:0» : parserBlockElementStatementList)))))))


noncomputable def «$unflatten_parserBlockElementStatementList_clauses» (input0 : (_root_.List parserBlockElementStatement)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_parserBlockElementStatementList:clause:0»  input0)]


noncomputable def «$unflatten_parserStateList':clause:0» (input0 : SpecTec.parserStateList) (input1 : (_root_.List parserState)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserStateList : SpecTec.parserStateList := input0; (let «parserState*» : (_root_.List parserState) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parserState*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((parserStateList : SpecTec.parserStateList)))))))


noncomputable def «$unflatten_parserStateList':clause:1» (input0 : SpecTec.parserStateList) (input1 : (_root_.List parserState)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserStateList : SpecTec.parserStateList := input0; (let «parserState*» : (_root_.List parserState) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parserState*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parserState*» with | «exec:2» :: «exec:1» => (let parserState_h : parserState := «exec:2»; (let «parserState_t*» : (_root_.List parserState) := «exec:1»; (.bind (.call ⟨SpecTec.parserStateList, SpecTecCall.«$unflatten_parserStateList'» ((SpecTec.parserStateList.«% %» parserStateList parserState_h) : SpecTec.parserStateList) «parserState_t*»⟩) (fun («exec:3» : SpecTec.parserStateList) => (let «eval:0» : SpecTec.parserStateList := «exec:3»; (.pure ((«eval:0» : SpecTec.parserStateList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_parserStateList'_clauses» (input0 : parserStateList) (input1 : (_root_.List parserState)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_parserStateList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_parserStateList':clause:1»  input0 input1)]


noncomputable def «$unflatten_parserLocalDeclarationList':clause:0» (input0 : SpecTec.parserLocalDeclarationList) (input1 : (_root_.List parserLocalDeclaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserLocalDeclarationList : SpecTec.parserLocalDeclarationList := input0; (let «parserLocalDeclaration*» : (_root_.List parserLocalDeclaration) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parserLocalDeclaration*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((parserLocalDeclarationList : SpecTec.parserLocalDeclarationList)))))))


noncomputable def «$unflatten_parserLocalDeclarationList':clause:1» (input0 : SpecTec.parserLocalDeclarationList) (input1 : (_root_.List parserLocalDeclaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserLocalDeclarationList : SpecTec.parserLocalDeclarationList := input0; (let «parserLocalDeclaration*» : (_root_.List parserLocalDeclaration) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parserLocalDeclaration*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parserLocalDeclaration*» with | «exec:2» :: «exec:1» => (let parserLocalDeclaration_h : parserLocalDeclaration := «exec:2»; (let «parserLocalDeclaration_t*» : (_root_.List parserLocalDeclaration) := «exec:1»; (.bind (.call ⟨SpecTec.parserLocalDeclarationList, SpecTecCall.«$unflatten_parserLocalDeclarationList'» ((SpecTec.parserLocalDeclarationList.«% %» parserLocalDeclarationList parserLocalDeclaration_h) : SpecTec.parserLocalDeclarationList) «parserLocalDeclaration_t*»⟩) (fun («exec:3» : SpecTec.parserLocalDeclarationList) => (let «eval:0» : SpecTec.parserLocalDeclarationList := «exec:3»; (.pure ((«eval:0» : SpecTec.parserLocalDeclarationList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_parserLocalDeclarationList'_clauses» (input0 : parserLocalDeclarationList) (input1 : (_root_.List parserLocalDeclaration)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_parserLocalDeclarationList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_parserLocalDeclarationList':clause:1»  input0 input1)]


noncomputable def «$unflatten_parserLocalDeclarationList:clause:0» (input0 : (_root_.List parserLocalDeclaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parserLocalDeclaration*» : (_root_.List parserLocalDeclaration) := input0; (.bind (.call ⟨parserLocalDeclarationList, SpecTecCall.«$unflatten_parserLocalDeclarationList'» ((parserLocalDeclarationList._EMPTY) : parserLocalDeclarationList) «parserLocalDeclaration*»⟩) (fun («exec:1» : parserLocalDeclarationList) => (let «eval:0» : parserLocalDeclarationList := «exec:1»; (.pure ((«eval:0» : parserLocalDeclarationList)))))))


noncomputable def «$unflatten_parserLocalDeclarationList_clauses» (input0 : (_root_.List parserLocalDeclaration)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_parserLocalDeclarationList:clause:0»  input0)]


noncomputable def «$lift_constOptIR:clause:0» (input0 : constOptIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constIR? : (_root_.Option constIR) := input0; (.bind (.guard (((_root_.Option.isNone constIR?) = true))) (fun (_ : Unit) => (.pure ((((constOpt._EMPTY) : constOpt) : constOpt))))))


noncomputable def «$lift_constOptIR:clause:1» (input0 : SpecTec.constOptIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constOptIR : SpecTec.constOptIR := input0; (.bind (.guard (((_root_.Option.isSome constOptIR) = true))) (fun (_ : Unit) => (.pure ((((constOpt.CONST) : constOpt) : constOpt))))))


noncomputable def «$lift_constOptIR_clauses» (input0 : constOptIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_constOptIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_constOptIR:clause:1»  input0)]


noncomputable def «$unflatten_tableKeyList':clause:0» (input0 : SpecTec.tableKeyList) (input1 : (_root_.List tableKey)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableKeyList : SpecTec.tableKeyList := input0; (let «tableKey*» : (_root_.List tableKey) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableKey*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((tableKeyList : SpecTec.tableKeyList)))))))


noncomputable def «$unflatten_tableKeyList':clause:1» (input0 : SpecTec.tableKeyList) (input1 : (_root_.List tableKey)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableKeyList : SpecTec.tableKeyList := input0; (let «tableKey*» : (_root_.List tableKey) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableKey*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableKey*» with | «exec:2» :: «exec:1» => (let tableKey_h : tableKey := «exec:2»; (let «tableKey_t*» : (_root_.List tableKey) := «exec:1»; (.bind (.call ⟨SpecTec.tableKeyList, SpecTecCall.«$unflatten_tableKeyList'» ((SpecTec.tableKeyList.«% %» tableKeyList tableKey_h) : SpecTec.tableKeyList) «tableKey_t*»⟩) (fun («exec:3» : SpecTec.tableKeyList) => (let «eval:0» : SpecTec.tableKeyList := «exec:3»; (.pure ((«eval:0» : SpecTec.tableKeyList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_tableKeyList'_clauses» (input0 : tableKeyList) (input1 : (_root_.List tableKey)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_tableKeyList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_tableKeyList':clause:1»  input0 input1)]


noncomputable def «$unflatten_tableKeyList:clause:0» (input0 : (_root_.List tableKey)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableKey*» : (_root_.List tableKey) := input0; (.bind (.call ⟨tableKeyList, SpecTecCall.«$unflatten_tableKeyList'» ((tableKeyList._EMPTY) : tableKeyList) «tableKey*»⟩) (fun («exec:1» : tableKeyList) => (let «eval:0» : tableKeyList := «exec:1»; (.pure ((«eval:0» : tableKeyList)))))))


noncomputable def «$unflatten_tableKeyList_clauses» (input0 : (_root_.List tableKey)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_tableKeyList:clause:0»  input0)]


noncomputable def «$unflatten_tableActionList':clause:0» (input0 : SpecTec.tableActionList) (input1 : (_root_.List tableAction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableActionList : SpecTec.tableActionList := input0; (let «tableAction*» : (_root_.List tableAction) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableAction*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((tableActionList : SpecTec.tableActionList)))))))


noncomputable def «$unflatten_tableActionList':clause:1» (input0 : SpecTec.tableActionList) (input1 : (_root_.List tableAction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableActionList : SpecTec.tableActionList := input0; (let «tableAction*» : (_root_.List tableAction) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableAction*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableAction*» with | «exec:2» :: «exec:1» => (let tableAction_h : tableAction := «exec:2»; (let «tableAction_t*» : (_root_.List tableAction) := «exec:1»; (.bind (.call ⟨SpecTec.tableActionList, SpecTecCall.«$unflatten_tableActionList'» ((SpecTec.tableActionList.«% %» tableActionList tableAction_h) : SpecTec.tableActionList) «tableAction_t*»⟩) (fun («exec:3» : SpecTec.tableActionList) => (let «eval:0» : SpecTec.tableActionList := «exec:3»; (.pure ((«eval:0» : SpecTec.tableActionList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_tableActionList'_clauses» (input0 : tableActionList) (input1 : (_root_.List tableAction)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_tableActionList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_tableActionList':clause:1»  input0 input1)]


noncomputable def «$unflatten_tableActionList:clause:0» (input0 : (_root_.List tableAction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableAction*» : (_root_.List tableAction) := input0; (.bind (.call ⟨tableActionList, SpecTecCall.«$unflatten_tableActionList'» ((tableActionList._EMPTY) : tableActionList) «tableAction*»⟩) (fun («exec:1» : tableActionList) => (let «eval:0» : tableActionList := «exec:1»; (.pure ((«eval:0» : tableActionList)))))))


noncomputable def «$unflatten_tableActionList_clauses» (input0 : (_root_.List tableAction)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_tableActionList:clause:0»  input0)]


noncomputable def «$lift_tableEntryPriorityIR:clause:0» (input0 : tableEntryPriorityIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«PRIORITY '=' % ':'» «exec:1» => (let integerLiteral : SpecTec.integerLiteral := «exec:1»; (.pure ((((tableEntryPriority.«PRIORITY '=' % ':'» integerLiteral) : tableEntryPriority) : tableEntryPriority)))))

end SpecTec
