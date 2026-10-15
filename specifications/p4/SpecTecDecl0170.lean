import SpecTecDecl0169

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$find_action'_clauses» (input0 : (_root_.List matchAction)) (input1 : prefixedNameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_action':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$find_action':clause:1»  input0 input1), fun (_ : _root_.Unit) => («$find_action':clause:2»  input0 input1)]


noncomputable def «$find_action:clause:0» (input0 : tableContext) (input1 : SpecTec.prefixedNameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let prefixedNameIR : SpecTec.prefixedNameIR := input1; (.bind (.call ⟨(_root_.Option ((_root_.List parameterIR) × argumentListIR)), SpecTecCall.«$find_action'» (tableContext.ACTIONS TBLC) prefixedNameIR⟩) (fun («exec:1» : (_root_.Option ((_root_.List parameterIR) × argumentListIR))) => (let «eval:0» : (_root_.Option ((_root_.List parameterIR) × argumentListIR)) := «exec:1»; (.pure ((«eval:0» : (_root_.Option ((_root_.List parameterIR) × argumentListIR))))))))))


noncomputable def «$find_action_clauses» (input0 : tableContext) (input1 : prefixedNameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_action:clause:0»  input0 input1)]


noncomputable def «$set_priorities_of_tableEntryListIR:case_1:iter:0:clause:0» (input0 : (_root_.List tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableEntryIR : SpecTec.tableEntryIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableEntryIR) := «exec:1»; (.bind (.call ⟨tableEntryPriorityOptIR, SpecTecCall.«$tableEntryPriorityOptIR_of_tableEntryIR» tableEntryIR⟩) (fun («exec:3» : tableEntryPriorityOptIR) => (let «eval:1» : tableEntryPriorityOptIR := «exec:3»; (match «eval:1» with | none => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))) | some _ => .unmatch)))))) | [] => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_1:iter:0_clauses» (input0 : (_root_.List tableEntryIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:0:clause:0» (input0 : (_root_.List tableEntryState)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List tableEntryState)) : (_root_.List tableEntryState)))) | _ :: _ => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:0:clause:1» (input0 : (_root_.List tableEntryState)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let TBLS : tableEntryState := «exec:2»; (let «tail:0» : (_root_.List tableEntryState) := «exec:1»; (let TBLS' : tableEntryState := TBLS; (.bind (.call ⟨(_root_.List tableEntryState), SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:0» «tail:0»⟩) (fun («exec:3» : (_root_.List tableEntryState)) => (let «tail:1» : (_root_.List tableEntryState) := «exec:3»; (.pure (((TBLS' :: «tail:1») : (_root_.List tableEntryState)))))))))) | [] => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:0_clauses» (input0 : (_root_.List tableEntryState)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_2:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_2:iter:0:clause:1»  input0)]


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:2:clause:0» (input0 : (_root_.List tableEntryState)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Nat)) : (_root_.List _root_.Nat)))) | _ :: _ => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:2:clause:1» (input0 : (_root_.List tableEntryState)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let TBLS' : tableEntryState := «exec:2»; (let «tail:0» : (_root_.List tableEntryState) := «exec:1»; (match TBLS' with | .LPM «exec:3» => (let n_prefix : _root_.Nat := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Nat)) => (let «tail:1» : (_root_.List _root_.Nat) := «exec:4»; (.pure (((n_prefix :: «tail:1») : (_root_.List _root_.Nat)))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:2_clauses» (input0 : (_root_.List tableEntryState)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_2:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_2:iter:2:clause:1»  input0)]


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:3:clause:0» (input0 : (_root_.List tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:3:clause:1» (input0 : (_root_.List SpecTec.tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableEntryIR : SpecTec.tableEntryIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableEntryIR) := «exec:1»; (.bind (.call ⟨tableEntryPriorityOptIR, SpecTecCall.«$tableEntryPriorityOptIR_of_tableEntryIR» tableEntryIR⟩) (fun («exec:3» : tableEntryPriorityOptIR) => (let «eval:4» : tableEntryPriorityOptIR := «exec:3»; (match «eval:4» with | none => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:3» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))) | some _ => .unmatch)))))) | [] => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:3_clauses» (input0 : (_root_.List tableEntryIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_2:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_2:iter:3:clause:1»  input0)]


noncomputable def «$set_priorities_of_tableEntryListIR:case_4:iter:1:clause:0» (input0 : (_root_.List tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_4:iter:1:clause:1» (input0 : (_root_.List tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableEntryIR_t : tableEntryIR := «exec:2»; (let «tail:0» : (_root_.List tableEntryIR) := «exec:1»; (.bind (.call ⟨tableEntryPriorityOptIR, SpecTecCall.«$tableEntryPriorityOptIR_of_tableEntryIR» tableEntryIR_t⟩) (fun («exec:3» : tableEntryPriorityOptIR) => (let «eval:2» : tableEntryPriorityOptIR := «exec:3»; (match «eval:2» with | none => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_4:iter:1» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))) | some _ => .unmatch)))))) | [] => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_4:iter:1_clauses» (input0 : (_root_.List tableEntryIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_4:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_4:iter:1:clause:1»  input0)]


noncomputable def «$set_priority_of_tableEntryIR:clause:0» (input0 : SpecTec.tableEntryIR) (input1 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableEntryIR : SpecTec.tableEntryIR := input0; (let n : _root_.Nat := input1; (match tableEntryIR with | .«% % % ':' % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let constOptIR : SpecTec.constOptIR := «exec:1»; (let _tableEntryPriorityOptIR : tableEntryPriorityOptIR := «exec:2»; (let keysetExpressionIR : SpecTec.keysetExpressionIR := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (let annotationList : SpecTec.annotationList := «exec:5»; (let tableEntryPriorityIR : SpecTec.tableEntryPriorityIR := ((SpecTec.tableEntryPriorityIR.«PRIORITY '=' % ':'» ((integerLiteral.D (_root_.Int.ofNat n)) : integerLiteral)) : SpecTec.tableEntryPriorityIR); (let tableEntryIR_updated : SpecTec.tableEntryIR := ((SpecTec.tableEntryIR.«% % % ':' % % ';'» constOptIR (_root_.Option.some tableEntryPriorityIR) keysetExpressionIR tableActionReferenceIR annotationList) : SpecTec.tableEntryIR); (.pure ((tableEntryIR_updated : SpecTec.tableEntryIR)))))))))))))


noncomputable def «$set_priority_of_tableEntryIR_clauses» (input0 : tableEntryIR) (input1 : _root_.Nat) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_priority_of_tableEntryIR:clause:0»  input0 input1)]


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:5:clause:0» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List tableEntryIR)) : (_root_.List tableEntryIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:5:clause:1» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List SpecTec.tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let n_prefix : _root_.Nat := «exec:2»; (let «tail:0» : (_root_.List _root_.Nat) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let tableEntryIR : SpecTec.tableEntryIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.tableEntryIR) := «exec:3»; (.bind (.call ⟨SpecTec.tableEntryIR, SpecTecCall.«$set_priority_of_tableEntryIR» tableEntryIR n_prefix⟩) (fun («exec:5» : SpecTec.tableEntryIR) => (let «eval:6» : SpecTec.tableEntryIR := «exec:5»; (let tableEntryIR_updated : SpecTec.tableEntryIR := «eval:6»; (.bind (.call ⟨(_root_.List SpecTec.tableEntryIR), SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:5» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.tableEntryIR)) => (let «tail:2» : (_root_.List SpecTec.tableEntryIR) := «exec:6»; (.pure (((tableEntryIR_updated :: «tail:2») : (_root_.List SpecTec.tableEntryIR))))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$set_priorities_of_tableEntryListIR:case_2:iter:5_clauses» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List tableEntryIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_2:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:case_2:iter:5:clause:1»  input0 input1)]


noncomputable def «Type_wf:structTypeIR:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Type_wf:structTypeIR:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_wf:structTypeIR:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Type_wf:structTypeIR:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:structTypeIR:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Type_wf:structTypeIR:pattern-iter:1:clause:1»  input0)]


noncomputable def «Type_wf:headerTypeIR:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Type_wf:headerTypeIR:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_wf:headerTypeIR:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Type_wf:headerTypeIR:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:headerTypeIR:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Type_wf:headerTypeIR:pattern-iter:1:clause:1»  input0)]


noncomputable def «Type_wf:headerUnionTypeIR:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Type_wf:headerUnionTypeIR:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_wf:headerUnionTypeIR:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Type_wf:headerUnionTypeIR:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:headerUnionTypeIR:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Type_wf:headerUnionTypeIR:pattern-iter:1:clause:1»  input0)]

end SpecTec
