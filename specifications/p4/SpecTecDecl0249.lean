import SpecTecDecl0248

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$find_tableActionIR_qualified:clause:1» (input0 : (_root_.List tableActionIR)) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableActionIR*» : (_root_.List tableActionIR) := input0; (let nameIR : SpecTec.nameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableActionIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableActionIR*» with | «exec:2» :: «exec:1» => (let tableActionIR_h : tableActionIR := «exec:2»; (let «tableActionIR_t*» : (_root_.List tableActionIR) := «exec:1»; (match tableActionIR_h with | .«% % '#' `( % ',' % `) ';'» «exec:3» «exec:4» «exec:5» «exec:6» => (let annotationList : SpecTec.annotationList := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (let _parameterListIR : parameterListIR := «exec:5»; (let «parameterIR_control*» : (_root_.List parameterIR) := «exec:6»; (match tableActionReferenceIR with | .«% % `( % `)» «exec:7» «exec:8» «exec:9» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:7»; (let controlPlaneNameIR : SpecTec.controlPlaneNameIR := «exec:8»; (let «argumentIR_data*» : (_root_.List argumentIR) := «exec:9»; (.bind (.guard (((_root_.Option.some nameIR) ≠ controlPlaneNameIR))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.Option (SpecTec.nameIR × tableActionIR)), SpecTecCall.«$find_tableActionIR_qualified» «tableActionIR_t*» nameIR⟩) (fun («exec:10» : (_root_.Option (SpecTec.nameIR × tableActionIR))) => (let «eval:0» : (_root_.Option (SpecTec.nameIR × tableActionIR)) := «exec:10»; (.pure ((«eval:0» : (_root_.Option (SpecTec.nameIR × tableActionIR))))))))))))))))))))) | [] => .unmatch)))))


noncomputable def «$find_tableActionIR_qualified:clause:2» (input0 : (_root_.List tableActionIR)) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableActionIR*» : (_root_.List tableActionIR) := input0; (let nameIR : SpecTec.nameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableActionIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableActionIR*» with | «exec:2» :: «exec:1» => (let tableActionIR_h : tableActionIR := «exec:2»; (let «tableActionIR_t*» : (_root_.List tableActionIR) := «exec:1»; (match tableActionIR_h with | .«% % '#' `( % ',' % `) ';'» «exec:3» «exec:4» «exec:5» «exec:6» => (let annotationList : SpecTec.annotationList := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (let _parameterListIR : parameterListIR := «exec:5»; (let «parameterIR_control*» : (_root_.List parameterIR) := «exec:6»; (match tableActionReferenceIR with | .«% % `( % `)» «exec:7» «exec:8» «exec:9» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:7»; (let controlPlaneNameIR : SpecTec.controlPlaneNameIR := «exec:8»; (let «argumentIR_data*» : (_root_.List argumentIR) := «exec:9»; (match controlPlaneNameIR with | some «exec:10» => (.bind (.guard («exec:10» = nameIR)) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.nameIR, SpecTecCall.«$flatten_prefixedNameIR» prefixedNameIR⟩) (fun («exec:11» : SpecTec.nameIR) => (let «eval:0» : SpecTec.nameIR := «exec:11»; (let nameIR_action : SpecTec.nameIR := «eval:0»; (.pure (((_root_.Option.some (nameIR_action, tableActionIR_h)) : (_root_.Option (SpecTec.nameIR × tableActionIR))))))))))) | none => .unmatch)))))))))))) | [] => .unmatch)))))


noncomputable def «$find_tableActionIR_qualified_clauses» (input0 : (_root_.List tableActionIR)) (input1 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_tableActionIR_qualified:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$find_tableActionIR_qualified:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$find_tableActionIR_qualified:clause:2»  input0 input1)]


noncomputable def «$find_tableActionIR_unqualified':clause:0» (input0 : (_root_.List tableActionIR)) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableActionIR*» : (_root_.List tableActionIR) := input0; (let nameIR : SpecTec.nameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableActionIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((((_root_.Option.none) : (_root_.Option (SpecTec.nameIR × tableActionIR))) : (_root_.Option (SpecTec.nameIR × tableActionIR)))))))))


noncomputable def «$find_tableActionIR_unqualified':clause:1» (input0 : (_root_.List tableActionIR)) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableActionIR*» : (_root_.List tableActionIR) := input0; (let nameIR : SpecTec.nameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableActionIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableActionIR*» with | «exec:2» :: «exec:1» => (let tableActionIR_h : tableActionIR := «exec:2»; (let «tableActionIR_t*» : (_root_.List tableActionIR) := «exec:1»; (match tableActionIR_h with | .«% % '#' `( % ',' % `) ';'» «exec:3» «exec:4» «exec:5» «exec:6» => (let annotationList : SpecTec.annotationList := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (let _parameterListIR : parameterListIR := «exec:5»; (let «parameterIR_control*» : (_root_.List parameterIR) := «exec:6»; (match tableActionReferenceIR with | .«% % `( % `)» «exec:7» «exec:8» «exec:9» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:7»; (let controlPlaneNameIR : SpecTec.controlPlaneNameIR := «exec:8»; (let «argumentIR_data*» : (_root_.List argumentIR) := «exec:9»; (.bind (.guard (((_root_.Option.isSome controlPlaneNameIR) = true))) (fun (_ : Unit) => (match controlPlaneNameIR with | some «exec:10» => (let nameIR_controlPlane : SpecTec.nameIR := «exec:10»; (.bind (.call ⟨(_root_.List _root_.String), SpecTecCall.«$split_text» nameIR_controlPlane "."⟩) (fun («exec:11» : (_root_.List _root_.String)) => (let «eval:0» : (_root_.List _root_.String) := «exec:11»; (let «nameIR_split*» : (_root_.List SpecTec.nameIR) := «eval:0»; (let «nameIR'*» : (_root_.List SpecTec.nameIR) := («$rev_» (X := SpecTec.nameIR) «nameIR_split*»); (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «nameIR'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «nameIR'*» with | «exec:13» :: «exec:12» => (let nameIR_unqualified : SpecTec.nameIR := «exec:13»; (let «_nameIR*» : (_root_.List SpecTec.nameIR) := «exec:12»; (.bind (.guard ((nameIR ≠ nameIR_unqualified))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.Option (SpecTec.nameIR × tableActionIR)), SpecTecCall.«$find_tableActionIR_unqualified'» «tableActionIR_t*» nameIR⟩) (fun («exec:14» : (_root_.Option (SpecTec.nameIR × tableActionIR))) => (let «eval:1» : (_root_.Option (SpecTec.nameIR × tableActionIR)) := «exec:14»; (.pure ((«eval:1» : (_root_.Option (SpecTec.nameIR × tableActionIR)))))))))))) | [] => .unmatch))))))))) | none => .unmatch)))))))))))))) | [] => .unmatch)))))


noncomputable def «$find_tableActionIR_unqualified':clause:2» (input0 : (_root_.List tableActionIR)) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableActionIR*» : (_root_.List tableActionIR) := input0; (let nameIR : SpecTec.nameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableActionIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableActionIR*» with | «exec:2» :: «exec:1» => (let tableActionIR_h : tableActionIR := «exec:2»; (let «tableActionIR_t*» : (_root_.List tableActionIR) := «exec:1»; (match tableActionIR_h with | .«% % '#' `( % ',' % `) ';'» «exec:3» «exec:4» «exec:5» «exec:6» => (let annotationList : SpecTec.annotationList := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (let _parameterListIR : parameterListIR := «exec:5»; (let «parameterIR_control*» : (_root_.List parameterIR) := «exec:6»; (match tableActionReferenceIR with | .«% % `( % `)» «exec:7» «exec:8» «exec:9» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:7»; (let controlPlaneNameIR : SpecTec.controlPlaneNameIR := «exec:8»; (let «argumentIR_data*» : (_root_.List argumentIR) := «exec:9»; (.bind (.guard (((_root_.Option.isSome controlPlaneNameIR) = true))) (fun (_ : Unit) => (match controlPlaneNameIR with | some «exec:10» => (let nameIR_controlPlane : SpecTec.nameIR := «exec:10»; (.bind (.call ⟨(_root_.List _root_.String), SpecTecCall.«$split_text» nameIR_controlPlane "."⟩) (fun («exec:11» : (_root_.List _root_.String)) => (let «eval:0» : (_root_.List _root_.String) := «exec:11»; (let «nameIR_split*» : (_root_.List SpecTec.nameIR) := «eval:0»; (let «nameIR'*» : (_root_.List SpecTec.nameIR) := («$rev_» (X := SpecTec.nameIR) «nameIR_split*»); (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «nameIR'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «nameIR'*» with | «exec:13» :: «exec:12» => (let nameIR_unqualified : SpecTec.nameIR := «exec:13»; (let «_nameIR*» : (_root_.List SpecTec.nameIR) := «exec:12»; (.bind (.guard (nameIR_unqualified = nameIR)) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.nameIR, SpecTecCall.«$flatten_prefixedNameIR» prefixedNameIR⟩) (fun («exec:14» : SpecTec.nameIR) => (let «eval:1» : SpecTec.nameIR := «exec:14»; (let nameIR_action : SpecTec.nameIR := «eval:1»; (.pure (((_root_.Option.some (nameIR_action, tableActionIR_h)) : (_root_.Option (SpecTec.nameIR × tableActionIR))))))))))))) | [] => .unmatch))))))))) | none => .unmatch)))))))))))))) | [] => .unmatch)))))


noncomputable def «$find_tableActionIR_unqualified'_clauses» (input0 : (_root_.List tableActionIR)) (input1 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_tableActionIR_unqualified':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$find_tableActionIR_unqualified':clause:1»  input0 input1), fun (_ : _root_.Unit) => («$find_tableActionIR_unqualified':clause:2»  input0 input1)]


noncomputable def «$find_tableActionIR_unqualified:clause:0» (input0 : (_root_.List tableActionIR)) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableActionIR*» : (_root_.List tableActionIR) := input0; (let nameIR : SpecTec.nameIR := input1; (.bind (.call ⟨(_root_.List _root_.String), SpecTecCall.«$split_text» nameIR "."⟩) (fun («exec:1» : (_root_.List _root_.String)) => (let «eval:0» : (_root_.List _root_.String) := «exec:1»; (let «nameIR_split*» : (_root_.List SpecTec.nameIR) := «eval:0»; (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length («$rev_» (X := SpecTec.nameIR) «nameIR_split*»))))) (fun (_ : Unit) => (match ((«$rev_» (X := SpecTec.nameIR) «nameIR_split*»)[(0 : _root_.Nat)]?) with | some «exec:2» => (let «eval:1» : SpecTec.nameIR := «exec:2»; (let nameIR_action : SpecTec.nameIR := «eval:1»; (.bind (.call ⟨(_root_.Option (SpecTec.nameIR × tableActionIR)), SpecTecCall.«$find_tableActionIR_unqualified'» «tableActionIR*» nameIR_action⟩) (fun («exec:3» : (_root_.Option (SpecTec.nameIR × tableActionIR))) => (let «eval:2» : (_root_.Option (SpecTec.nameIR × tableActionIR)) := «exec:3»; (.pure ((«eval:2» : (_root_.Option (SpecTec.nameIR × tableActionIR)))))))))) | none => .unmatch)))))))))


noncomputable def «$find_tableActionIR_unqualified_clauses» (input0 : (_root_.List tableActionIR)) (input1 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_tableActionIR_unqualified:clause:0»  input0 input1)]


noncomputable def «$flatten_selectCaseList:clause:0» (input0 : SpecTec.selectCaseList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let selectCaseList : SpecTec.selectCaseList := input0; (.bind (.guard (((«exec:match:selectCaseList:_EMPTY» selectCaseList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List selectCase)) : (_root_.List selectCase)))))))


noncomputable def «$flatten_selectCaseList:clause:1» (input0 : SpecTec.selectCaseList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let selectCaseList' : SpecTec.selectCaseList := input0; (.bind (.guard (((«exec:match:selectCaseList:% %» selectCaseList') = true))) (fun (_ : Unit) => (match selectCaseList' with | .«% %» «exec:1» «exec:2» => (let selectCaseList : SpecTec.selectCaseList := «exec:1»; (let selectCase : SpecTec.selectCase := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.selectCase), SpecTecCall.«$flatten_selectCaseList» selectCaseList⟩) (fun («exec:3» : (_root_.List SpecTec.selectCase)) => (let «eval:0» : (_root_.List SpecTec.selectCase) := «exec:3»; (.pure (((«eval:0» ++ ([selectCase] : (_root_.List SpecTec.selectCase))) : (_root_.List SpecTec.selectCase))))))))) | _ => .unmatch))))


noncomputable def «$flatten_selectCaseList_clauses» (input0 : selectCaseList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_selectCaseList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_selectCaseList:clause:1»  input0)]


noncomputable def «$switchLabelIR_of_switchCaseIR:clause:0» (input0 : SpecTec.switchCaseIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchCaseIR : SpecTec.switchCaseIR := input0; (.bind (.guard (((«exec:match:switchCaseIR:% ':' %» switchCaseIR) = true))) (fun (_ : Unit) => (match switchCaseIR with | .«% ':' %» «exec:1» «exec:2» => (let switchLabelIR : SpecTec.switchLabelIR := «exec:1»; (let _blockStatementIR : blockStatementIR := «exec:2»; (.pure ((switchLabelIR : SpecTec.switchLabelIR))))) | _ => .unmatch))))


noncomputable def «$switchLabelIR_of_switchCaseIR:clause:1» (input0 : SpecTec.switchCaseIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchCaseIR : SpecTec.switchCaseIR := input0; (.bind (.guard (((«exec:match:switchCaseIR:% ':'» switchCaseIR) = true))) (fun (_ : Unit) => (match switchCaseIR with | .«% ':'» «exec:1» => (let switchLabelIR : SpecTec.switchLabelIR := «exec:1»; (.pure ((switchLabelIR : SpecTec.switchLabelIR)))) | _ => .unmatch))))


noncomputable def «$switchLabelIR_of_switchCaseIR_clauses» (input0 : switchCaseIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$switchLabelIR_of_switchCaseIR:clause:0»  input0), fun (_ : _root_.Unit) => («$switchLabelIR_of_switchCaseIR:clause:1»  input0)]


noncomputable def «Stmt_ok:table:iter:4:clause:0» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List switchLabelIR)) : (_root_.List switchLabelIR)))) | _ :: _ => .unmatch)


noncomputable def «Stmt_ok:table:iter:4:clause:1» (input0 : (_root_.List SpecTec.switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let switchCaseIR : SpecTec.switchCaseIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.switchCaseIR) := «exec:1»; (.bind (.call ⟨SpecTec.switchLabelIR, SpecTecCall.«$switchLabelIR_of_switchCaseIR» switchCaseIR⟩) (fun («exec:3» : SpecTec.switchLabelIR) => (let «eval:5» : SpecTec.switchLabelIR := «exec:3»; (let switchLabelIR : SpecTec.switchLabelIR := «eval:5»; (.bind (.call ⟨(_root_.List SpecTec.switchLabelIR), SpecTecCall.«Stmt_ok:table:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.switchLabelIR)) => (let «tail:1» : (_root_.List SpecTec.switchLabelIR) := «exec:4»; (.pure (((switchLabelIR :: «tail:1») : (_root_.List SpecTec.switchLabelIR))))))))))))) | [] => .unmatch)


noncomputable def «Stmt_ok:table:iter:4_clauses» (input0 : (_root_.List switchCaseIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Stmt_ok:table:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Stmt_ok:table:iter:4:clause:1»  input0)]


noncomputable def «Stmt_ok:general:iter:3:clause:0» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List switchLabelIR)) : (_root_.List switchLabelIR)))) | _ :: _ => .unmatch)


noncomputable def «Stmt_ok:general:iter:3:clause:1» (input0 : (_root_.List SpecTec.switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let switchCaseIR : SpecTec.switchCaseIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.switchCaseIR) := «exec:1»; (.bind (.call ⟨SpecTec.switchLabelIR, SpecTecCall.«$switchLabelIR_of_switchCaseIR» switchCaseIR⟩) (fun («exec:3» : SpecTec.switchLabelIR) => (let «eval:4» : SpecTec.switchLabelIR := «exec:3»; (let switchLabelIR : SpecTec.switchLabelIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.switchLabelIR), SpecTecCall.«Stmt_ok:general:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.switchLabelIR)) => (let «tail:1» : (_root_.List SpecTec.switchLabelIR) := «exec:4»; (.pure (((switchLabelIR :: «tail:1») : (_root_.List SpecTec.switchLabelIR))))))))))))) | [] => .unmatch)


noncomputable def «Stmt_ok:general:iter:3_clauses» (input0 : (_root_.List switchCaseIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Stmt_ok:general:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Stmt_ok:general:iter:3:clause:1»  input0)]


noncomputable def «$is_non_fallthrough_switchCaseIR:clause:0» (input0 : SpecTec.switchCaseIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchCaseIR : SpecTec.switchCaseIR := input0; (.bind (.guard (((«exec:match:switchCaseIR:% ':' %» switchCaseIR) = true))) (fun (_ : Unit) => (match switchCaseIR with | .«% ':' %» «exec:1» «exec:2» => (let switchLabelIR : SpecTec.switchLabelIR := «exec:1»; (let blockStatementIR : SpecTec.blockStatementIR := «exec:2»; (.pure ((true : _root_.Bool))))) | _ => .unmatch))))


noncomputable def «$is_non_fallthrough_switchCaseIR:clause:1» (input0 : SpecTec.switchCaseIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchCaseIR : SpecTec.switchCaseIR := input0; (.bind (.guard (((«exec:match:switchCaseIR:% ':'» switchCaseIR) = true))) (fun (_ : Unit) => (match switchCaseIR with | .«% ':'» «exec:1» => (let switchLabelIR : SpecTec.switchLabelIR := «exec:1»; (.pure ((false : _root_.Bool)))) | _ => .unmatch))))


noncomputable def «$is_non_fallthrough_switchCaseIR_clauses» (input0 : switchCaseIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_non_fallthrough_switchCaseIR:clause:0»  input0), fun (_ : _root_.Unit) => («$is_non_fallthrough_switchCaseIR:clause:1»  input0)]


noncomputable def «SwitchCases_table_eval:cons-fallthrough-match:iter:1:clause:0» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «SwitchCases_table_eval:cons-fallthrough-match:iter:1:clause:1» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let switchCaseIR_t : switchCaseIR := «exec:2»; (let «tail:0» : (_root_.List switchCaseIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_non_fallthrough_switchCaseIR» switchCaseIR_t⟩) (fun («exec:3» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«SwitchCases_table_eval:cons-fallthrough-match:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «SwitchCases_table_eval:cons-fallthrough-match:iter:1_clauses» (input0 : (_root_.List switchCaseIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («SwitchCases_table_eval:cons-fallthrough-match:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («SwitchCases_table_eval:cons-fallthrough-match:iter:1:clause:1»  input0)]


noncomputable def «SwitchCases_table_eval:cons-fallthrough-match-no-block:iter:1:clause:0» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «SwitchCases_table_eval:cons-fallthrough-match-no-block:iter:1:clause:1» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let switchCaseIR_t : switchCaseIR := «exec:2»; (let «tail:0» : (_root_.List switchCaseIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_non_fallthrough_switchCaseIR» switchCaseIR_t⟩) (fun («exec:3» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«SwitchCases_table_eval:cons-fallthrough-match-no-block:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «SwitchCases_table_eval:cons-fallthrough-match-no-block:iter:1_clauses» (input0 : (_root_.List switchCaseIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («SwitchCases_table_eval:cons-fallthrough-match-no-block:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («SwitchCases_table_eval:cons-fallthrough-match-no-block:iter:1:clause:1»  input0)]


noncomputable def «SwitchCases_general_eval:cons-fallthrough-match:iter:2:clause:0» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «SwitchCases_general_eval:cons-fallthrough-match:iter:2:clause:1» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let switchCaseIR_t : switchCaseIR := «exec:2»; (let «tail:0» : (_root_.List switchCaseIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_non_fallthrough_switchCaseIR» switchCaseIR_t⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«SwitchCases_general_eval:cons-fallthrough-match:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:3» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)

end SpecTec
