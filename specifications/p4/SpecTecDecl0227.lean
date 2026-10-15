import SpecTecDecl0226

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Call_eval:controlApplyMethodCallee-copyin-exit:pattern-iter:2:clause:1» (input0 : (_root_.List (pair callTargetId SpecTec.actionDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId : SpecTec.callableId := «exec:3»; (let actionDef : SpecTec.actionDef := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId SpecTec.actionDef)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId)), SpecTecCall.«Call_eval:controlApplyMethodCallee-copyin-exit:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId))) => (let «pattern-tail:1» : (_root_.List SpecTec.actionDef) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.callableId) := («exec:5»).2; (.pure ((((actionDef :: «pattern-tail:1»), (callableId :: «pattern-tail:2»)) : ((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId))))))))))))) | [] => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-copyin-exit:pattern-iter:2_clauses» (input0 : (_root_.List (pair callTargetId actionDef))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-copyin-exit:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-copyin-exit:pattern-iter:2:clause:1»  input0)]


noncomputable def «Call_eval:controlApplyMethodCallee-localDecl-exit:pattern-iter:2:clause:0» (input0 : (_root_.List (pair callTargetId actionDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List actionDef)), ([] : (_root_.List callableId))) : ((_root_.List actionDef) × (_root_.List callableId))))) | _ :: _ => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-localDecl-exit:pattern-iter:2:clause:1» (input0 : (_root_.List (pair callTargetId SpecTec.actionDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId : SpecTec.callableId := «exec:3»; (let actionDef : SpecTec.actionDef := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId SpecTec.actionDef)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId)), SpecTecCall.«Call_eval:controlApplyMethodCallee-localDecl-exit:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId))) => (let «pattern-tail:1» : (_root_.List SpecTec.actionDef) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.callableId) := («exec:5»).2; (.pure ((((actionDef :: «pattern-tail:1»), (callableId :: «pattern-tail:2»)) : ((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId))))))))))))) | [] => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-localDecl-exit:pattern-iter:2_clauses» (input0 : (_root_.List (pair callTargetId actionDef))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-localDecl-exit:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-localDecl-exit:pattern-iter:2:clause:1»  input0)]


noncomputable def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:pattern-iter:2:clause:0» (input0 : (_root_.List (pair callTargetId actionDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List actionDef)), ([] : (_root_.List callableId))) : ((_root_.List actionDef) × (_root_.List callableId))))) | _ :: _ => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:pattern-iter:2:clause:1» (input0 : (_root_.List (pair callTargetId SpecTec.actionDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId : SpecTec.callableId := «exec:3»; (let actionDef : SpecTec.actionDef := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId SpecTec.actionDef)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId)), SpecTecCall.«Call_eval:controlApplyMethodCallee-controlBodyIR-exit:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId))) => (let «pattern-tail:1» : (_root_.List SpecTec.actionDef) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.callableId) := («exec:5»).2; (.pure ((((actionDef :: «pattern-tail:1»), (callableId :: «pattern-tail:2»)) : ((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId))))))))))))) | [] => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:pattern-iter:2_clauses» (input0 : (_root_.List (pair callTargetId actionDef))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-controlBodyIR-exit:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-controlBodyIR-exit:pattern-iter:2:clause:1»  input0)]


noncomputable def «Call_eval:controlApplyMethodCallee-cont:pattern-iter:2:clause:0» (input0 : (_root_.List (pair callTargetId actionDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List actionDef)), ([] : (_root_.List callableId))) : ((_root_.List actionDef) × (_root_.List callableId))))) | _ :: _ => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-cont:pattern-iter:2:clause:1» (input0 : (_root_.List (pair callTargetId SpecTec.actionDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId : SpecTec.callableId := «exec:3»; (let actionDef : SpecTec.actionDef := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId SpecTec.actionDef)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId)), SpecTecCall.«Call_eval:controlApplyMethodCallee-cont:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId))) => (let «pattern-tail:1» : (_root_.List SpecTec.actionDef) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.callableId) := («exec:5»).2; (.pure ((((actionDef :: «pattern-tail:1»), (callableId :: «pattern-tail:2»)) : ((_root_.List SpecTec.actionDef) × (_root_.List SpecTec.callableId))))))))))))) | [] => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-cont:pattern-iter:2_clauses» (input0 : (_root_.List (pair callTargetId actionDef))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-cont:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-cont:pattern-iter:2:clause:1»  input0)]


noncomputable def «TableMatch_eval:no-match:iter:2:clause:0» (input0 : (_root_.List tableKeyValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «TableMatch_eval:no-match:iter:2:clause:1» (input0 : (_root_.List SpecTec.tableKeyValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyValue : SpecTec.tableKeyValue := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyValue) := «exec:1»; (match tableKeyValue with | .«% ':' %» «exec:3» «exec:4» => (let value_key : value := «exec:3»; (let _nameIR : nameIR := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«TableMatch_eval:no-match:iter:2» «tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((_nameIR :: «tail:1»), (value_key :: «tail:2»)) : ((_root_.List nameIR) × (_root_.List value)))))))))))))) | [] => .unmatch)


noncomputable def «TableMatch_eval:no-match:iter:2_clauses» (input0 : (_root_.List tableKeyValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («TableMatch_eval:no-match:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («TableMatch_eval:no-match:iter:2:clause:1»  input0)]


noncomputable def «TableMatch_eval:match:iter:2:clause:0» (input0 : (_root_.List tableKeyValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «TableMatch_eval:match:iter:2:clause:1» (input0 : (_root_.List SpecTec.tableKeyValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyValue : SpecTec.tableKeyValue := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyValue) := «exec:1»; (match tableKeyValue with | .«% ':' %» «exec:3» «exec:4» => (let value_key : value := «exec:3»; (let _nameIR : nameIR := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«TableMatch_eval:match:iter:2» «tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((_nameIR :: «tail:1»), (value_key :: «tail:2»)) : ((_root_.List nameIR) × (_root_.List value)))))))))))))) | [] => .unmatch)


noncomputable def «TableMatch_eval:match:iter:2_clauses» (input0 : (_root_.List tableKeyValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («TableMatch_eval:match:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («TableMatch_eval:match:iter:2:clause:1»  input0)]


noncomputable def «$select_action:case_3:iter:0:clause:0» (input0 : (_root_.List tableMatch)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List (_root_.Option _root_.Nat))), ([] : (_root_.List tableActionReferenceIR))) : ((_root_.List (_root_.Option _root_.Nat)) × (_root_.List tableActionReferenceIR))))) | _ :: _ => .unmatch)


noncomputable def «$select_action:case_3:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableMatch)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableMatch : SpecTec.tableMatch := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableMatch) := «exec:1»; (match tableMatch with | .«% ':' %» «exec:3» «exec:4» => (let nat? : (_root_.Option _root_.Nat) := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (.bind (.call ⟨((_root_.List (_root_.Option _root_.Nat)) × (_root_.List SpecTec.tableActionReferenceIR)), SpecTecCall.«$select_action:case_3:iter:0» «tail:0»⟩) (fun («exec:5» : ((_root_.List (_root_.Option _root_.Nat)) × (_root_.List SpecTec.tableActionReferenceIR))) => (let «tail:1» : (_root_.List (_root_.Option _root_.Nat)) := («exec:5»).1; (let «tail:2» : (_root_.List SpecTec.tableActionReferenceIR) := («exec:5»).2; (.pure ((((nat? :: «tail:1»), (tableActionReferenceIR :: «tail:2»)) : ((_root_.List (_root_.Option _root_.Nat)) × (_root_.List SpecTec.tableActionReferenceIR)))))))))))))) | [] => .unmatch)


noncomputable def «$select_action:case_3:iter:0_clauses» (input0 : (_root_.List tableMatch)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$select_action:case_3:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$select_action:case_3:iter:0:clause:1»  input0)]


noncomputable def «$select_action:case_3:iter:1:clause:0» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$select_action:case_3:iter:1:clause:1» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nat? : (_root_.Option _root_.Nat) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option _root_.Nat)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome nat?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$select_action:case_3:iter:1» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «$select_action:case_3:iter:1_clauses» (input0 : (_root_.List (_root_.Option _root_.Nat))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$select_action:case_3:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$select_action:case_3:iter:1:clause:1»  input0)]


noncomputable def «$select_action:case_3:iter:2:clause:0» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Nat)) : (_root_.List _root_.Nat)))) | _ :: _ => .unmatch)


noncomputable def «$select_action:case_3:iter:2:clause:1» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nat? : (_root_.Option _root_.Nat) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option _root_.Nat)) := «exec:1»; (match nat? with | some «exec:3» => (let n_priority : _root_.Nat := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$select_action:case_3:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Nat)) => (let «tail:1» : (_root_.List _root_.Nat) := «exec:4»; (.pure (((n_priority :: «tail:1») : (_root_.List _root_.Nat)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «$select_action:case_3:iter:2_clauses» (input0 : (_root_.List (_root_.Option _root_.Nat))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$select_action:case_3:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$select_action:case_3:iter:2:clause:1»  input0)]


noncomputable def «$select_action:case_3:iter:3:clause:0» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List tableActionReferenceIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.Nat × tableActionReferenceIR))) : (_root_.List (_root_.Nat × tableActionReferenceIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$select_action:case_3:iter:3:clause:1» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List SpecTec.tableActionReferenceIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let n_priority : _root_.Nat := «exec:2»; (let «tail:0» : (_root_.List _root_.Nat) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.tableActionReferenceIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.Nat × SpecTec.tableActionReferenceIR)), SpecTecCall.«$select_action:case_3:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.Nat × SpecTec.tableActionReferenceIR))) => (let «tail:2» : (_root_.List (_root_.Nat × SpecTec.tableActionReferenceIR)) := «exec:5»; (.pure ((((n_priority, tableActionReferenceIR) :: «tail:2») : (_root_.List (_root_.Nat × SpecTec.tableActionReferenceIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$select_action:case_3:iter:3_clauses» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List tableActionReferenceIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$select_action:case_3:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$select_action:case_3:iter:3:clause:1»  input0 input1)]


noncomputable def «$select_action:case_3:pattern-iter:5:clause:0» (input0 : (_root_.List (_root_.Nat × tableActionReferenceIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List _root_.Nat)), ([] : (_root_.List tableActionReferenceIR))) : ((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR))))) | _ :: _ => .unmatch)


noncomputable def «$select_action:case_3:pattern-iter:5:clause:1» (input0 : (_root_.List (_root_.Nat × tableActionReferenceIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let n_priority_sorted : _root_.Nat := («exec:2»).1; (let tableActionReferenceIR_sorted : tableActionReferenceIR := («exec:2»).2; (let «pattern-tail:0» : (_root_.List (_root_.Nat × tableActionReferenceIR)) := «exec:1»; (.bind (.call ⟨((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR)), SpecTecCall.«$select_action:case_3:pattern-iter:5» «pattern-tail:0»⟩) (fun («exec:3» : ((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR))) => (let «pattern-tail:1» : (_root_.List _root_.Nat) := («exec:3»).1; (let «pattern-tail:2» : (_root_.List tableActionReferenceIR) := («exec:3»).2; (.pure ((((n_priority_sorted :: «pattern-tail:1»), (tableActionReferenceIR_sorted :: «pattern-tail:2»)) : ((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR)))))))))))) | [] => .unmatch)


noncomputable def «$select_action:case_3:pattern-iter:5_clauses» (input0 : (_root_.List (_root_.Nat × tableActionReferenceIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$select_action:case_3:pattern-iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («$select_action:case_3:pattern-iter:5:clause:1»  input0)]

end SpecTec
