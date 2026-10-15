import SpecTecDecl0168

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$add_action_tbl:clause:0» (input0 : tableContext) (input1 : SpecTec.prefixedNameIR) (input2 : (_root_.List parameterIR)) (input3 : SpecTec.argumentListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let prefixedNameIR : SpecTec.prefixedNameIR := input1; (let «parameterIR*» : (_root_.List parameterIR) := input2; (let argumentListIR : SpecTec.argumentListIR := input3; (let matchAction : SpecTec.matchAction := ((SpecTec.matchAction.«% `( % '@' % `)» prefixedNameIR «parameterIR*» argumentListIR) : SpecTec.matchAction); (.pure ((({ TBLC with ACTIONS := ((tableContext.ACTIONS TBLC) ++ ([matchAction] : (_root_.List SpecTec.matchAction))) } : tableContext) : tableContext))))))))


noncomputable def «$add_action_tbl_clauses» (input0 : tableContext) (input1 : prefixedNameIR) (input2 : (_root_.List parameterIR)) (input3 : argumentListIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_action_tbl:clause:0»  input0 input1 input2 input3)]


noncomputable def «$is_lpm_key':clause:0» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("lpm" = t)) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$is_lpm_key':clause:1» (input0 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_lpm_key'_clauses» (input0 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_lpm_key':clause:0»  input0), fun (_ : _root_.Unit) => («$is_lpm_key':clause:1»  input0)]


noncomputable def «$is_lpm_key:clause:0» (input0 : tableKeyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% '#' % ':' % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let _typedExpressionIR : typedExpressionIR := «exec:1»; (let _nameIR : SpecTec.nameIR := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (let _annotationList : annotationList := «exec:4»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_lpm_key'» nameIR⟩) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.pure ((«eval:0» : _root_.Bool)))))))))))


noncomputable def «$is_lpm_key_clauses» (input0 : tableKeyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_lpm_key:clause:0»  input0)]


noncomputable def «$requires_priority':clause:0» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("range" = t)) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$requires_priority':clause:1» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("ternary" = t)) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$requires_priority':clause:2» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("optional" = t)) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$requires_priority':clause:3» (input0 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$requires_priority'_clauses» (input0 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$requires_priority':clause:0»  input0), fun (_ : _root_.Unit) => («$requires_priority':clause:1»  input0), fun (_ : _root_.Unit) => («$requires_priority':clause:2»  input0), fun (_ : _root_.Unit) => («$requires_priority':clause:3»  input0)]


noncomputable def «$requires_priority:clause:0» (input0 : tableKeyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% '#' % ':' % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let _typedExpressionIR : typedExpressionIR := «exec:1»; (let _nameIR : SpecTec.nameIR := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (let _annotationList : annotationList := «exec:4»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$requires_priority'» nameIR⟩) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.pure ((«eval:0» : _root_.Bool)))))))))))


noncomputable def «$requires_priority_clauses» (input0 : tableKeyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$requires_priority:clause:0»  input0)]


noncomputable def «$update_mode_tbl:case_1:iter:0:clause:0» (input0 : (_root_.List tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$update_mode_tbl:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyIR : SpecTec.tableKeyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$requires_priority» tableKeyIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (let b_pri : _root_.Bool := «eval:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_mode_tbl:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((b_pri :: «tail:1») : (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$update_mode_tbl:case_1:iter:0_clauses» (input0 : (_root_.List tableKeyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_mode_tbl:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$update_mode_tbl:case_1:iter:0:clause:1»  input0)]


noncomputable def «$update_mode_tbl:case_2:iter:0:clause:0» (input0 : (_root_.List tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$update_mode_tbl:case_2:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyIR : SpecTec.tableKeyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$requires_priority» tableKeyIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (let b_pri : _root_.Bool := «eval:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_mode_tbl:case_2:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((b_pri :: «tail:1») : (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$update_mode_tbl:case_2:iter:0_clauses» (input0 : (_root_.List tableKeyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_mode_tbl:case_2:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$update_mode_tbl:case_2:iter:0:clause:1»  input0)]


noncomputable def «$update_mode_tbl:case_2:iter:3:clause:0» (input0 : (_root_.List tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$update_mode_tbl:case_2:iter:3:clause:1» (input0 : (_root_.List SpecTec.tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyIR : SpecTec.tableKeyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_lpm_key» tableKeyIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:4» : _root_.Bool := «exec:3»; (let b_lpm : _root_.Bool := «eval:4»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_mode_tbl:case_2:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((b_lpm :: «tail:1») : (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$update_mode_tbl:case_2:iter:3_clauses» (input0 : (_root_.List tableKeyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_mode_tbl:case_2:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$update_mode_tbl:case_2:iter:3:clause:1»  input0)]


noncomputable def «$update_mode_tbl:case_3:iter:0:clause:0» (input0 : (_root_.List tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$update_mode_tbl:case_3:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyIR : SpecTec.tableKeyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$requires_priority» tableKeyIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (let b_pri : _root_.Bool := «eval:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_mode_tbl:case_3:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((b_pri :: «tail:1») : (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$update_mode_tbl:case_3:iter:0_clauses» (input0 : (_root_.List tableKeyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_mode_tbl:case_3:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$update_mode_tbl:case_3:iter:0:clause:1»  input0)]


noncomputable def «$update_mode_tbl:case_3:iter:3:clause:0» (input0 : (_root_.List tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$update_mode_tbl:case_3:iter:3:clause:1» (input0 : (_root_.List SpecTec.tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyIR : SpecTec.tableKeyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_lpm_key» tableKeyIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:4» : _root_.Bool := «exec:3»; (let b_lpm : _root_.Bool := «eval:4»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_mode_tbl:case_3:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((b_lpm :: «tail:1») : (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$update_mode_tbl:case_3:iter:3_clauses» (input0 : (_root_.List tableKeyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_mode_tbl:case_3:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$update_mode_tbl:case_3:iter:3:clause:1»  input0)]


noncomputable def «$find_action':clause:0» (input0 : (_root_.List matchAction)) (input1 : SpecTec.prefixedNameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «matchAction*» : (_root_.List matchAction) := input0; (let prefixedNameIR : SpecTec.prefixedNameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «matchAction*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((((_root_.Option.none) : (_root_.Option ((_root_.List parameterIR) × argumentListIR))) : (_root_.Option ((_root_.List parameterIR) × argumentListIR)))))))))


noncomputable def «$find_action':clause:1» (input0 : (_root_.List matchAction)) (input1 : SpecTec.prefixedNameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «matchAction*» : (_root_.List matchAction) := input0; (let prefixedNameIR : SpecTec.prefixedNameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «matchAction*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «matchAction*» with | «exec:2» :: «exec:1» => (let matchAction_h : matchAction := «exec:2»; (let «matchAction_t*» : (_root_.List matchAction) := «exec:1»; (match matchAction_h with | .«% `( % '@' % `)» «exec:3» «exec:4» «exec:5» => (let prefixedNameIR' : SpecTec.prefixedNameIR := «exec:3»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:4»; (let argumentListIR : SpecTec.argumentListIR := «exec:5»; (.bind (.guard (prefixedNameIR = prefixedNameIR')) (fun (_ : Unit) => (.pure (((_root_.Option.some («parameterIR*», argumentListIR)) : (_root_.Option ((_root_.List parameterIR) × SpecTec.argumentListIR))))))))))))) | [] => .unmatch)))))


noncomputable def «$find_action':clause:2» (input0 : (_root_.List matchAction)) (input1 : SpecTec.prefixedNameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «matchAction*» : (_root_.List matchAction) := input0; (let prefixedNameIR : SpecTec.prefixedNameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «matchAction*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «matchAction*» with | «exec:2» :: «exec:1» => (let matchAction_h : matchAction := «exec:2»; (let «matchAction_t*» : (_root_.List matchAction) := «exec:1»; (match matchAction_h with | .«% `( % '@' % `)» «exec:3» «exec:4» «exec:5» => (let prefixedNameIR_h : SpecTec.prefixedNameIR := «exec:3»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:4»; (let _argumentListIR : argumentListIR := «exec:5»; (.bind (.guard ((prefixedNameIR_h ≠ prefixedNameIR))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.Option ((_root_.List parameterIR) × argumentListIR)), SpecTecCall.«$find_action'» «matchAction_t*» prefixedNameIR⟩) (fun («exec:6» : (_root_.Option ((_root_.List parameterIR) × argumentListIR))) => (let «eval:0» : (_root_.Option ((_root_.List parameterIR) × argumentListIR)) := «exec:6»; (.pure ((«eval:0» : (_root_.Option ((_root_.List parameterIR) × argumentListIR)))))))))))))))) | [] => .unmatch)))))

end SpecTec
