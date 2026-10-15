import SpecTecDecl0267

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «SwitchCases_table_eval:clause:4» (input0 : SpecTec.id) (input1 : switchCaseListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (let «switchCaseIR''''*» : (_root_.List switchCaseIR) := input1; (let «switchCaseIR'''''*» : (_root_.List switchCaseIR) := «switchCaseIR''''*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «switchCaseIR'''''*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «switchCaseIR'''''*» with | «exec:2» :: «exec:1» => (let switchCaseIR_h : switchCaseIR := «exec:2»; (let «switchCaseIR_t*» : (_root_.List switchCaseIR) := «exec:1»; (let switchCaseIR'''''' : switchCaseIR := switchCaseIR_h; (.bind (.guard (((«exec:match:switchCaseIR:% ':'» switchCaseIR'''''') = true))) (fun (_ : Unit) => (match switchCaseIR'''''' with | .«% ':'» «exec:3» => (let switchLabelIR_h : switchLabelIR := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$match_switchLabelIR_table» id switchLabelIR_h⟩) (fun («exec:4» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:4»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«SwitchCases_table_eval:cons-fallthrough-match-no-block:iter:1» «switchCaseIR_t*»⟩) (fun («exec:5» : (_root_.List _root_.Bool)) => (let «eval:3» : (_root_.List _root_.Bool) := «exec:5»; (.bind (.call ⟨(_root_.List switchCaseIR), SpecTecCall.«$filter_» switchCaseIR «switchCaseIR_t*» «eval:3»⟩) (fun («exec:6» : (_root_.List switchCaseIR)) => (let «eval:4» : (_root_.List switchCaseIR) := «exec:6»; (match «eval:4» with | [] => (.pure ((((_root_.Option.none) : (_root_.Option blockStatementIR)) : (_root_.Option blockStatementIR)))) | _ :: _ => .unmatch))))))))))))) | _ => .unmatch)))))) | [] => .unmatch))))))


noncomputable def «SwitchCases_table_eval:clause:5» (input0 : SpecTec.id) (input1 : switchCaseListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (let «switchCaseIR''''*» : (_root_.List switchCaseIR) := input1; (let «switchCaseIR'''''*» : (_root_.List switchCaseIR) := «switchCaseIR''''*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «switchCaseIR'''''*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «switchCaseIR'''''*» with | «exec:2» :: «exec:1» => (let switchCaseIR_h : switchCaseIR := «exec:2»; (let «switchCaseIR_t*» : (_root_.List switchCaseIR) := «exec:1»; (let switchCaseIR'''''' : switchCaseIR := switchCaseIR_h; (.bind (.guard (((«exec:match:switchCaseIR:% ':'» switchCaseIR'''''') = true))) (fun (_ : Unit) => (match switchCaseIR'''''' with | .«% ':'» «exec:3» => (let switchLabelIR_h : switchLabelIR := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$match_switchLabelIR_table» id switchLabelIR_h⟩) (fun («exec:4» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:4»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.Option blockStatementIR), SpecTecCall.SwitchCases_table_eval id «switchCaseIR_t*»⟩) (fun («exec:5» : (_root_.Option blockStatementIR)) => (let blockStatementIR? : (_root_.Option blockStatementIR) := «exec:5»; (.pure ((blockStatementIR? : (_root_.Option blockStatementIR))))))))))))) | _ => .unmatch)))))) | [] => .unmatch))))))


noncomputable def SwitchCases_table_eval_clauses (input0 : id) (input1 : switchCaseListIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («SwitchCases_table_eval:clause:0»  input0 input1), fun (_ : _root_.Unit) => («SwitchCases_table_eval:clause:1»  input0 input1), fun (_ : _root_.Unit) => («SwitchCases_table_eval:clause:2»  input0 input1), fun (_ : _root_.Unit) => («SwitchCases_table_eval:clause:3»  input0 input1), fun (_ : _root_.Unit) => («SwitchCases_table_eval:clause:4»  input0 input1), fun (_ : _root_.Unit) => («SwitchCases_table_eval:clause:5»  input0 input1)]


noncomputable def «$insert_NoAction_tablePropertyIR:clause:0» (input0 : tableContext) (input1 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let «tablePropertyIR*» : (_root_.List tablePropertyIR) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tablePropertyIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure (((TBLC, ([] : (_root_.List tablePropertyIR))) : (tableContext × (_root_.List tablePropertyIR)))))))))


noncomputable def «$insert_NoAction_tablePropertyIR:clause:1» (input0 : tableContext) (input1 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC_0 : tableContext := input0; (let «tablePropertyIR*» : (_root_.List tablePropertyIR) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tablePropertyIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tablePropertyIR*» with | «exec:2» :: «exec:1» => (let tablePropertyIR_h : tablePropertyIR := «exec:2»; (let «tablePropertyIR_t*» : (_root_.List tablePropertyIR) := «exec:1»; (let tablePropertyIR' : tablePropertyIR := tablePropertyIR_h; (.bind (.guard (((«sub:tablePropertyIR:tableActionsPropertyIR» tablePropertyIR') = true))) (fun (_ : Unit) => (match («$insert_NoAction_tablePropertyIR:case_2:downcast:0» tablePropertyIR') with | some «exec:3» => (let «eval:0» : tableActionsPropertyIR := «exec:3»; (match «eval:0» with | .«ACTIONS '=' `{ % `}» «exec:4» => (let «tableActionIR*» : (_root_.List tableActionIR) := «exec:4»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List tableActionReferenceIR)))), SpecTecCall.«$insert_NoAction_tablePropertyIR:case_2:iter:1» «tableActionIR*»⟩) (fun («exec:5» : ((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List tableActionReferenceIR))))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:5»).1; (let «_parameterListIR*» : (_root_.List parameterListIR) := ((«exec:5»).2).1; (let «_parameterListIR'*» : (_root_.List parameterListIR) := (((«exec:5»).2).2).1; (let «tableActionReferenceIR*» : (_root_.List tableActionReferenceIR) := (((«exec:5»).2).2).2; (let tableActionReferenceIR_NoAction : tableActionReferenceIR := ((tableActionReferenceIR.«% % `( % `)» ((prefixedNameIR.«'.' %» "NoAction") : prefixedNameIR) ((_root_.Option.none) : (_root_.Option nameIR)) ([] : (_root_.List argumentIR))) : tableActionReferenceIR); (.bind (.guard ((¬ (tableActionReferenceIR_NoAction ∈ «tableActionReferenceIR*»)))) (fun (_ : Unit) => (.bind (.call ⟨tableContext, SpecTecCall.«$add_action_tbl» TBLC_0 ((prefixedNameIR.«'.' %» "NoAction") : prefixedNameIR) ([] : (_root_.List parameterIR)) ([] : (_root_.List argumentIR))⟩) (fun («exec:6» : tableContext) => (let «eval:2» : tableContext := «exec:6»; (let TBLC_1 : tableContext := «eval:2»; (let tableActionIR_NoAction : tableActionIR := ((tableActionIR.«% % '#' `( % ',' % `) ';'» ((annotationList._EMPTY) : annotationList) tableActionReferenceIR_NoAction ([] : (_root_.List parameterIR)) ([] : (_root_.List parameterIR))) : tableActionIR); (let tablePropertyIR_h_updated : tablePropertyIR := ((tablePropertyIR.«ACTIONS '=' `{ % `}» («tableActionIR*» ++ ([tableActionIR_NoAction] : (_root_.List tableActionIR)))) : tablePropertyIR); (.pure (((TBLC_1, (tablePropertyIR_h_updated :: «tablePropertyIR_t*»)) : (tableContext × (_root_.List tablePropertyIR))))))))))))))))))))))) | none => .unmatch)))))) | [] => .unmatch)))))


noncomputable def «$insert_NoAction_tablePropertyIR:clause:2» (input0 : tableContext) (input1 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC_0 : tableContext := input0; (let «tablePropertyIR*» : (_root_.List tablePropertyIR) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tablePropertyIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tablePropertyIR*» with | «exec:2» :: «exec:1» => (let tablePropertyIR_h : tablePropertyIR := «exec:2»; (let «tablePropertyIR_t*» : (_root_.List tablePropertyIR) := «exec:1»; (let tablePropertyIR' : tablePropertyIR := tablePropertyIR_h; (.bind (.guard (((«sub:tablePropertyIR:tableActionsPropertyIR» tablePropertyIR') = true))) (fun (_ : Unit) => (match («$insert_NoAction_tablePropertyIR:case_3:downcast:0» tablePropertyIR') with | some «exec:3» => (let «eval:0» : tableActionsPropertyIR := «exec:3»; (match «eval:0» with | .«ACTIONS '=' `{ % `}» «exec:4» => (let «tableActionIR*» : (_root_.List tableActionIR) := «exec:4»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List tableActionReferenceIR)))), SpecTecCall.«$insert_NoAction_tablePropertyIR:case_3:iter:1» «tableActionIR*»⟩) (fun («exec:5» : ((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List tableActionReferenceIR))))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:5»).1; (let «_parameterListIR*» : (_root_.List parameterListIR) := ((«exec:5»).2).1; (let «_parameterListIR'*» : (_root_.List parameterListIR) := (((«exec:5»).2).2).1; (let «tableActionReferenceIR*» : (_root_.List tableActionReferenceIR) := (((«exec:5»).2).2).2; (let tableActionReferenceIR_NoAction : tableActionReferenceIR := ((tableActionReferenceIR.«% % `( % `)» ((prefixedNameIR.«'.' %» "NoAction") : prefixedNameIR) ((_root_.Option.none) : (_root_.Option nameIR)) ([] : (_root_.List argumentIR))) : tableActionReferenceIR); (.bind (.guard ((tableActionReferenceIR_NoAction ∈ «tableActionReferenceIR*»))) (fun (_ : Unit) => (.pure (((TBLC_0, (tablePropertyIR_h :: «tablePropertyIR_t*»)) : (tableContext × (_root_.List tablePropertyIR))))))))))))))))) | none => .unmatch)))))) | [] => .unmatch)))))


noncomputable def «$insert_NoAction_tablePropertyIR:clause:3» (input0 : tableContext) (input1 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC_0 : tableContext := input0; (let «tablePropertyIR*» : (_root_.List tablePropertyIR) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tablePropertyIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tablePropertyIR*» with | «exec:2» :: «exec:1» => (let tablePropertyIR_h : tablePropertyIR := «exec:2»; (let «tablePropertyIR_t*» : (_root_.List tablePropertyIR) := «exec:1»; (.bind (.guard ((¬ ((«sub:tablePropertyIR:tableActionsPropertyIR» tablePropertyIR_h) = true)))) (fun (_ : Unit) => (.bind (.call ⟨(tableContext × (_root_.List tablePropertyIR)), SpecTecCall.«$insert_NoAction_tablePropertyIR» TBLC_0 «tablePropertyIR_t*»⟩) (fun («exec:3» : (tableContext × (_root_.List tablePropertyIR))) => (let «eval:0» : (tableContext × (_root_.List tablePropertyIR)) := «exec:3»; (let TBLC_1 : tableContext := («eval:0»).1; (let «tablePropertyIR_t_updated*» : (_root_.List tablePropertyIR) := («eval:0»).2; (.pure (((TBLC_1, (tablePropertyIR_h :: «tablePropertyIR_t_updated*»)) : (tableContext × (_root_.List tablePropertyIR)))))))))))))) | [] => .unmatch)))))


noncomputable def «$insert_NoAction_tablePropertyIR_clauses» (input0 : tableContext) (input1 : (_root_.List tablePropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$insert_NoAction_tablePropertyIR:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$insert_NoAction_tablePropertyIR:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$insert_NoAction_tablePropertyIR:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$insert_NoAction_tablePropertyIR:clause:3»  input0 input1)]


noncomputable def «$init_table:case_1:iter:1:clause:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$init_table:case_1:iter:1:clause:1» (input0 : (_root_.List SpecTec.tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tablePropertyIR : SpecTec.tablePropertyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tablePropertyIR) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_table:case_1:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((«sub:tablePropertyIR:tableActionsPropertyIR» tablePropertyIR) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$init_table:case_1:iter:1_clauses» (input0 : (_root_.List tablePropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$init_table:case_1:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$init_table:case_1:iter:1:clause:1»  input0)]


noncomputable def «$init_table:case_1:iter:10:clause:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$init_table:case_1:iter:10:clause:1» (input0 : (_root_.List SpecTec.tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tablePropertyIR : SpecTec.tablePropertyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tablePropertyIR) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_table:case_1:iter:10» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((«sub:tablePropertyIR:tableCustomPropertyIR» tablePropertyIR) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$init_table:case_1:iter:10_clauses» (input0 : (_root_.List tablePropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$init_table:case_1:iter:10:clause:0»  input0), fun (_ : _root_.Unit) => («$init_table:case_1:iter:10:clause:1»  input0)]


noncomputable def «$init_table:case_1:iter:5:clause:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$init_table:case_1:iter:5:clause:1» (input0 : (_root_.List SpecTec.tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tablePropertyIR : SpecTec.tablePropertyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tablePropertyIR) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_table:case_1:iter:5» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((«sub:tablePropertyIR:tableDefaultActionPropertyIR» tablePropertyIR) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$init_table:case_1:iter:5_clauses» (input0 : (_root_.List tablePropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$init_table:case_1:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («$init_table:case_1:iter:5:clause:1»  input0)]


noncomputable def «$init_tableEntries:case_1:iter:0:clause:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$init_tableEntries:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tablePropertyIR : SpecTec.tablePropertyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tablePropertyIR) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_tableEntries:case_1:iter:0» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((«sub:tablePropertyIR:tableEntriesPropertyIR» tablePropertyIR) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$init_tableEntries:case_1:iter:0_clauses» (input0 : (_root_.List tablePropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$init_tableEntries:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$init_tableEntries:case_1:iter:0:clause:1»  input0)]


noncomputable def «$init_tableEntries:case_2:iter:0:clause:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$init_tableEntries:case_2:iter:0:clause:1» (input0 : (_root_.List SpecTec.tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tablePropertyIR : SpecTec.tablePropertyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tablePropertyIR) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_tableEntries:case_2:iter:0» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((«sub:tablePropertyIR:tableEntriesPropertyIR» tablePropertyIR) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$init_tableEntries:case_2:iter:0_clauses» (input0 : (_root_.List tablePropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$init_tableEntries:case_2:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$init_tableEntries:case_2:iter:0:clause:1»  input0)]


noncomputable def «$init_tableEntries:clause:0» (input0 : tablePropertyListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tablePropertyIR*» : (_root_.List tablePropertyIR) := input0; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_tableEntries:case_1:iter:0» «tablePropertyIR*»⟩) (fun («exec:1» : (_root_.List _root_.Bool)) => (let «eval:1» : (_root_.List _root_.Bool) := «exec:1»; (.bind (.call ⟨(_root_.List tablePropertyIR), SpecTecCall.«$filter_» tablePropertyIR «tablePropertyIR*» «eval:1»⟩) (fun («exec:2» : (_root_.List tablePropertyIR)) => (let «eval:2» : (_root_.List tablePropertyIR) := «exec:2»; (let «tablePropertyIR'*» : (_root_.List tablePropertyIR) := «eval:2»; (.bind (.guard (((_root_.List.all «tablePropertyIR'*» (fun («sub:item» : tablePropertyIR) => («sub:tablePropertyIR:tableEntriesPropertyIR» «sub:item»))) = true))) (fun (_ : Unit) => (match (_root_.List.mapM (fun («$init_tableEntries:case_1:downcast:3:item» : tablePropertyIR) => («$init_tableEntries:case_1:downcast:3:0» «$init_tableEntries:case_1:downcast:3:item»)) «tablePropertyIR'*») with | some «exec:3» => (let «eval:3» : (_root_.List SpecTec.tableEntriesPropertyIR) := «exec:3»; (let «tableEntriesPropertyIR'*» : (_root_.List SpecTec.tableEntriesPropertyIR) := «eval:3»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableEntriesPropertyIR'*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableEntriesPropertyIR'*» with | «exec:5» :: «exec:4» => (let tableEntriesPropertyIR : SpecTec.tableEntriesPropertyIR := «exec:5»; (match «exec:4» with | [] => (.pure ((tableEntriesPropertyIR : SpecTec.tableEntriesPropertyIR))) | _ :: _ => .unmatch)) | [] => .unmatch))))) | none => .unmatch)))))))))))


noncomputable def «$init_tableEntries:clause:1» (input0 : tablePropertyListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tablePropertyIR*» : (_root_.List tablePropertyIR) := input0; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_tableEntries:case_2:iter:0» «tablePropertyIR*»⟩) (fun («exec:1» : (_root_.List _root_.Bool)) => (let «eval:1» : (_root_.List _root_.Bool) := «exec:1»; (.bind (.call ⟨(_root_.List tablePropertyIR), SpecTecCall.«$filter_» tablePropertyIR «tablePropertyIR*» «eval:1»⟩) (fun («exec:2» : (_root_.List tablePropertyIR)) => (let «eval:2» : (_root_.List tablePropertyIR) := «exec:2»; (match «eval:2» with | [] => (.pure ((((tableEntriesPropertyIR.«% % ENTRIES '=' `{ % `}» ((annotationList._EMPTY) : annotationList) ((_root_.Option.none) : (_root_.Option constIR)) ([] : (_root_.List tableEntryIR))) : tableEntriesPropertyIR) : tableEntriesPropertyIR))) | _ :: _ => .unmatch))))))))


noncomputable def «$init_tableEntries_clauses» (input0 : tablePropertyListIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$init_tableEntries:clause:0»  input0), fun (_ : _root_.Unit) => («$init_tableEntries:clause:1»  input0)]


noncomputable def «$init_tableKeys:case_1:iter:0:clause:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$init_tableKeys:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tablePropertyIR : SpecTec.tablePropertyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tablePropertyIR) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_tableKeys:case_1:iter:0» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((«sub:tablePropertyIR:tableKeysPropertyIR» tablePropertyIR) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$init_tableKeys:case_1:iter:0_clauses» (input0 : (_root_.List tablePropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$init_tableKeys:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$init_tableKeys:case_1:iter:0:clause:1»  input0)]


noncomputable def «$init_tableKeys:case_2:iter:0:clause:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$init_tableKeys:case_2:iter:0:clause:1» (input0 : (_root_.List SpecTec.tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tablePropertyIR : SpecTec.tablePropertyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tablePropertyIR) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_tableKeys:case_2:iter:0» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((«sub:tablePropertyIR:tableKeysPropertyIR» tablePropertyIR) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$init_tableKeys:case_2:iter:0_clauses» (input0 : (_root_.List tablePropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$init_tableKeys:case_2:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$init_tableKeys:case_2:iter:0:clause:1»  input0)]

end SpecTec
