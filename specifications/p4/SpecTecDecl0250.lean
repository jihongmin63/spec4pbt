import SpecTecDecl0249

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «SwitchCases_general_eval:cons-fallthrough-match:iter:2_clauses» (input0 : (_root_.List switchCaseIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («SwitchCases_general_eval:cons-fallthrough-match:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («SwitchCases_general_eval:cons-fallthrough-match:iter:2:clause:1»  input0)]


noncomputable def «SwitchCases_general_eval:cons-fallthrough-match-no-block:iter:2:clause:0» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «SwitchCases_general_eval:cons-fallthrough-match-no-block:iter:2:clause:1» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let switchCaseIR_t : switchCaseIR := «exec:2»; (let «tail:0» : (_root_.List switchCaseIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_non_fallthrough_switchCaseIR» switchCaseIR_t⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«SwitchCases_general_eval:cons-fallthrough-match-no-block:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:3» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «SwitchCases_general_eval:cons-fallthrough-match-no-block:iter:2_clauses» (input0 : (_root_.List switchCaseIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («SwitchCases_general_eval:cons-fallthrough-match-no-block:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («SwitchCases_general_eval:cons-fallthrough-match-no-block:iter:2:clause:1»  input0)]


noncomputable def «$flatten_switchCaseList:clause:0» (input0 : SpecTec.switchCaseList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchCaseList : SpecTec.switchCaseList := input0; (.bind (.guard (((«exec:match:switchCaseList:_EMPTY» switchCaseList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List switchCase)) : (_root_.List switchCase)))))))


noncomputable def «$flatten_switchCaseList:clause:1» (input0 : SpecTec.switchCaseList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchCaseList' : SpecTec.switchCaseList := input0; (.bind (.guard (((«exec:match:switchCaseList:% %» switchCaseList') = true))) (fun (_ : Unit) => (match switchCaseList' with | .«% %» «exec:1» «exec:2» => (let switchCaseList : SpecTec.switchCaseList := «exec:1»; (let switchCase : SpecTec.switchCase := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.switchCase), SpecTecCall.«$flatten_switchCaseList» switchCaseList⟩) (fun («exec:3» : (_root_.List SpecTec.switchCase)) => (let «eval:0» : (_root_.List SpecTec.switchCase) := «exec:3»; (.pure (((«eval:0» ++ ([switchCase] : (_root_.List SpecTec.switchCase))) : (_root_.List SpecTec.switchCase))))))))) | _ => .unmatch))))


noncomputable def «$flatten_switchCaseList_clauses» (input0 : switchCaseList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_switchCaseList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_switchCaseList:clause:1»  input0)]


noncomputable def «$flatten_tableActionList:clause:0» (input0 : SpecTec.tableActionList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableActionList : SpecTec.tableActionList := input0; (.bind (.guard (((«exec:match:tableActionList:_EMPTY» tableActionList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List tableAction)) : (_root_.List tableAction)))))))


noncomputable def «$flatten_tableActionList:clause:1» (input0 : SpecTec.tableActionList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableActionList' : SpecTec.tableActionList := input0; (.bind (.guard (((«exec:match:tableActionList:% %» tableActionList') = true))) (fun (_ : Unit) => (match tableActionList' with | .«% %» «exec:1» «exec:2» => (let tableActionList : SpecTec.tableActionList := «exec:1»; (let tableAction : SpecTec.tableAction := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.tableAction), SpecTecCall.«$flatten_tableActionList» tableActionList⟩) (fun («exec:3» : (_root_.List SpecTec.tableAction)) => (let «eval:0» : (_root_.List SpecTec.tableAction) := «exec:3»; (.pure (((«eval:0» ++ ([tableAction] : (_root_.List SpecTec.tableAction))) : (_root_.List SpecTec.tableAction))))))))) | _ => .unmatch))))


noncomputable def «$flatten_tableActionList_clauses» (input0 : tableActionList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_tableActionList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_tableActionList:clause:1»  input0)]


noncomputable def «$is_largest_priority_wins:clause:0» (input0 : SpecTec.tableCustomPropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableCustomPropertyIR : SpecTec.tableCustomPropertyIR := input0; (.bind (.guard (((«exec:match:tableCustomPropertyIR:% % CUSTOM_CONST % % ';'» tableCustomPropertyIR) = true))) (fun (_ : Unit) => (match tableCustomPropertyIR with | .«% % CUSTOM_CONST % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let _annotationList : annotationList := «exec:1»; (let _constOptIR : constOptIR := «exec:2»; (let t : _root_.String := «exec:3»; (let _constantInitializerIR : constantInitializerIR := «exec:4»; (.bind (.guard ("largest_priority_wins" = t)) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))) | _ => .unmatch))))


noncomputable def «$is_largest_priority_wins:clause:1» (input0 : tableCustomPropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _tableCustomPropertyIR : tableCustomPropertyIR := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_largest_priority_wins_clauses» (input0 : tableCustomPropertyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_largest_priority_wins:clause:0»  input0), fun (_ : _root_.Unit) => («$is_largest_priority_wins:clause:1»  input0)]


noncomputable def «$largest_priority_wins:case_1:iter:0:clause:0» (input0 : (_root_.List tableCustomPropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$largest_priority_wins:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableCustomPropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableCustomPropertyIR : SpecTec.tableCustomPropertyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableCustomPropertyIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_largest_priority_wins» tableCustomPropertyIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$largest_priority_wins:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:1» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$largest_priority_wins:case_1:iter:0_clauses» (input0 : (_root_.List tableCustomPropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$largest_priority_wins:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$largest_priority_wins:case_1:iter:0:clause:1»  input0)]


noncomputable def «$largest_priority_wins:case_2:iter:0:clause:0» (input0 : (_root_.List tableCustomPropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$largest_priority_wins:case_2:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableCustomPropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableCustomPropertyIR : SpecTec.tableCustomPropertyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableCustomPropertyIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_largest_priority_wins» tableCustomPropertyIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$largest_priority_wins:case_2:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:1» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$largest_priority_wins:case_2:iter:0_clauses» (input0 : (_root_.List tableCustomPropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$largest_priority_wins:case_2:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$largest_priority_wins:case_2:iter:0:clause:1»  input0)]


noncomputable def «$flatten_tableEntryList:clause:0» (input0 : SpecTec.tableEntryList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableEntryList : SpecTec.tableEntryList := input0; (.bind (.guard (((«exec:match:tableEntryList:_EMPTY» tableEntryList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List tableEntry)) : (_root_.List tableEntry)))))))


noncomputable def «$flatten_tableEntryList:clause:1» (input0 : SpecTec.tableEntryList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableEntryList' : SpecTec.tableEntryList := input0; (.bind (.guard (((«exec:match:tableEntryList:% %» tableEntryList') = true))) (fun (_ : Unit) => (match tableEntryList' with | .«% %» «exec:1» «exec:2» => (let tableEntryList : SpecTec.tableEntryList := «exec:1»; (let tableEntry : SpecTec.tableEntry := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.tableEntry), SpecTecCall.«$flatten_tableEntryList» tableEntryList⟩) (fun («exec:3» : (_root_.List SpecTec.tableEntry)) => (let «eval:0» : (_root_.List SpecTec.tableEntry) := «exec:3»; (.pure (((«eval:0» ++ ([tableEntry] : (_root_.List SpecTec.tableEntry))) : (_root_.List SpecTec.tableEntry))))))))) | _ => .unmatch))))


noncomputable def «$flatten_tableEntryList_clauses» (input0 : tableEntryList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_tableEntryList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_tableEntryList:clause:1»  input0)]


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:1:clause:0» (input0 : (_root_.List tableEntryState)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:1:clause:1» (input0 : (_root_.List tableEntryState)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let TBLS' : tableEntryState := «exec:2»; (let «tail:0» : (_root_.List tableEntryState) := «exec:1»; (.bind (.guard (((«exec:match:tableEntryState:LPM» TBLS') = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:1» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:1_clauses» (input0 : (_root_.List tableEntryState)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_2:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_2:iter:1:clause:1»  input0)]


noncomputable def «$join_tableEntryState:clause:0» (input0 : tableEntryState) (input1 : tableEntryState) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLS : tableEntryState := input0; (let TBLS' : tableEntryState := input1; (.bind (.guard (((«exec:match:tableEntryState:NON_LPM» TBLS) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:tableEntryState:LPM» TBLS') = true))) (fun (_ : Unit) => (match TBLS' with | .LPM «exec:1» => (let n : _root_.Nat := «exec:1»; (.pure ((((tableEntryState.LPM n) : tableEntryState) : tableEntryState)))) | _ => .unmatch)))))))


noncomputable def «$join_tableEntryState:clause:1» (input0 : tableEntryState) (input1 : tableEntryState) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLS : tableEntryState := input0; (let TBLS' : tableEntryState := input1; (.bind (.guard (((«exec:match:tableEntryState:LPM» TBLS) = true))) (fun (_ : Unit) => (match TBLS with | .LPM «exec:1» => (let n : _root_.Nat := «exec:1»; (.bind (.guard (((«exec:match:tableEntryState:NON_LPM» TBLS') = true))) (fun (_ : Unit) => (.pure ((((tableEntryState.LPM n) : tableEntryState) : tableEntryState)))))) | _ => .unmatch)))))


noncomputable def «$join_tableEntryState:clause:2» (input0 : tableEntryState) (input1 : tableEntryState) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLS : tableEntryState := input0; (let TBLS' : tableEntryState := input1; (.bind (.guard (((«exec:match:tableEntryState:NON_LPM» TBLS) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:tableEntryState:NON_LPM» TBLS') = true))) (fun (_ : Unit) => (.pure ((((tableEntryState.NON_LPM) : tableEntryState) : tableEntryState)))))))))


noncomputable def «$join_tableEntryState_clauses» (input0 : tableEntryState) (input1 : tableEntryState) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$join_tableEntryState:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$join_tableEntryState:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$join_tableEntryState:clause:2»  input0 input1)]


noncomputable def «$flatten_tableKeyList:clause:0» (input0 : SpecTec.tableKeyList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableKeyList : SpecTec.tableKeyList := input0; (.bind (.guard (((«exec:match:tableKeyList:_EMPTY» tableKeyList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List tableKey)) : (_root_.List tableKey)))))))


noncomputable def «$flatten_tableKeyList:clause:1» (input0 : SpecTec.tableKeyList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableKeyList' : SpecTec.tableKeyList := input0; (.bind (.guard (((«exec:match:tableKeyList:% %» tableKeyList') = true))) (fun (_ : Unit) => (match tableKeyList' with | .«% %» «exec:1» «exec:2» => (let tableKeyList : SpecTec.tableKeyList := «exec:1»; (let tableKey : SpecTec.tableKey := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.tableKey), SpecTecCall.«$flatten_tableKeyList» tableKeyList⟩) (fun («exec:3» : (_root_.List SpecTec.tableKey)) => (let «eval:0» : (_root_.List SpecTec.tableKey) := «exec:3»; (.pure (((«eval:0» ++ ([tableKey] : (_root_.List SpecTec.tableKey))) : (_root_.List SpecTec.tableKey))))))))) | _ => .unmatch))))


noncomputable def «$flatten_tableKeyList_clauses» (input0 : tableKeyList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_tableKeyList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_tableKeyList:clause:1»  input0)]

end SpecTec
