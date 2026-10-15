import SpecTecDecl0159

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$find_overloadeds_unnamed:case_2:pattern-iter:0:clause:1» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callTargetId_t : callTargetId := «exec:3»; (let V_t : V := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId V)) := «exec:1»; (.bind (.call ⟨((_root_.List V) × (_root_.List callTargetId)), SpecTecCall.«$find_overloadeds_unnamed:case_2:pattern-iter:0» V «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List V) × (_root_.List callTargetId))) => (let «pattern-tail:1» : (_root_.List V) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List callTargetId) := («exec:5»).2; (.pure ((((V_t :: «pattern-tail:1»), (callTargetId_t :: «pattern-tail:2»)) : ((_root_.List V) × (_root_.List callTargetId))))))))))))) | [] => .unmatch)


noncomputable def «$find_overloadeds_unnamed:case_2:pattern-iter:0_clauses» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloadeds_unnamed:case_2:pattern-iter:0:clause:0» V input0), fun (_ : _root_.Unit) => («$find_overloadeds_unnamed:case_2:pattern-iter:0:clause:1» V input0)]


noncomputable def «$find_overloadeds_unnamed:case_2:iter:3:clause:0» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId V))) : (_root_.List (pair callTargetId V))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$find_overloadeds_unnamed:case_2:iter:3:clause:1» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let V_t : V := «exec:2»; (let «tail:0» : (_root_.List V) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callTargetId_t : callTargetId := «exec:4»; (let «tail:1» : (_root_.List callTargetId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_overloadeds_unnamed:case_2:iter:3» V «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId V))) => (let «tail:2» : (_root_.List (pair callTargetId V)) := «exec:5»; (.pure (((((pair.«% ':' %» callTargetId_t V_t) : (pair callableId V)) :: «tail:2») : (_root_.List (pair callTargetId V)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$find_overloadeds_unnamed:case_2:iter:3_clauses» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloadeds_unnamed:case_2:iter:3:clause:0» V input0 input1), fun (_ : _root_.Unit) => («$find_overloadeds_unnamed:case_2:iter:3:clause:1» V input0 input1)]


noncomputable def «$find_overloadeds_unnamed:case_3:pattern-iter:0:clause:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List V)), ([] : (_root_.List callTargetId))) : ((_root_.List V) × (_root_.List callTargetId))))) | _ :: _ => .unmatch)


noncomputable def «$find_overloadeds_unnamed:case_3:pattern-iter:0:clause:1» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callTargetId_t : callTargetId := «exec:3»; (let V_t : V := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId V)) := «exec:1»; (.bind (.call ⟨((_root_.List V) × (_root_.List callTargetId)), SpecTecCall.«$find_overloadeds_unnamed:case_3:pattern-iter:0» V «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List V) × (_root_.List callTargetId))) => (let «pattern-tail:1» : (_root_.List V) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List callTargetId) := («exec:5»).2; (.pure ((((V_t :: «pattern-tail:1»), (callTargetId_t :: «pattern-tail:2»)) : ((_root_.List V) × (_root_.List callTargetId))))))))))))) | [] => .unmatch)


noncomputable def «$find_overloadeds_unnamed:case_3:pattern-iter:0_clauses» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloadeds_unnamed:case_3:pattern-iter:0:clause:0» V input0), fun (_ : _root_.Unit) => («$find_overloadeds_unnamed:case_3:pattern-iter:0:clause:1» V input0)]


noncomputable def «$find_overloadeds_unnamed:case_3:iter:3:clause:0» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId V))) : (_root_.List (pair callTargetId V))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$find_overloadeds_unnamed:case_3:iter:3:clause:1» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let V_t : V := «exec:2»; (let «tail:0» : (_root_.List V) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callTargetId_t : callTargetId := «exec:4»; (let «tail:1» : (_root_.List callTargetId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_overloadeds_unnamed:case_3:iter:3» V «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId V))) => (let «tail:2» : (_root_.List (pair callTargetId V)) := «exec:5»; (.pure (((((pair.«% ':' %» callTargetId_t V_t) : (pair callableId V)) :: «tail:2») : (_root_.List (pair callTargetId V)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$find_overloadeds_unnamed:case_3:iter:3_clauses» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloadeds_unnamed:case_3:iter:3:clause:0» V input0 input1), fun (_ : _root_.Unit) => («$find_overloadeds_unnamed:case_3:iter:3:clause:1» V input0 input1)]


noncomputable def «$find_overloaded:case_1:pattern-iter:0:clause:0» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List V_T)), ([] : (_root_.List callableId))) : ((_root_.List V_T) × (_root_.List callableId))))) | _ :: _ => .unmatch)


noncomputable def «$find_overloaded:case_1:pattern-iter:0:clause:1» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId : SpecTec.callableId := «exec:3»; (let V : V_T := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId V_T)) := «exec:1»; (.bind (.call ⟨((_root_.List V_T) × (_root_.List SpecTec.callableId)), SpecTecCall.«$find_overloaded:case_1:pattern-iter:0» V_T «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List V_T) × (_root_.List SpecTec.callableId))) => (let «pattern-tail:1» : (_root_.List V_T) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.callableId) := («exec:5»).2; (.pure ((((V :: «pattern-tail:1»), (callableId :: «pattern-tail:2»)) : ((_root_.List V_T) × (_root_.List SpecTec.callableId))))))))))))) | [] => .unmatch)


noncomputable def «$find_overloaded:case_1:pattern-iter:0_clauses» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloaded:case_1:pattern-iter:0:clause:0» V_T input0), fun (_ : _root_.Unit) => («$find_overloaded:case_1:pattern-iter:0:clause:1» V_T input0)]


noncomputable def «$find_overloaded:case_1:iter:2:clause:0» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.Option id))) : (_root_.List (_root_.Option id))))) | _ :: _ => .unmatch)


noncomputable def «$find_overloaded:case_1:iter:2:clause:1» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_arg? : (_root_.Option id) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option id)) := «exec:1»; (let id? : (_root_.Option id) := id_arg?; (.bind (.call ⟨(_root_.List (_root_.Option id)), SpecTecCall.«$find_overloaded:case_1:iter:2» V_T «tail:0»⟩) (fun («exec:3» : (_root_.List (_root_.Option id))) => (let «tail:1» : (_root_.List (_root_.Option id)) := «exec:3»; (.pure (((id? :: «tail:1») : (_root_.List (_root_.Option id))))))))))) | [] => .unmatch)


noncomputable def «$find_overloaded:case_1:iter:2_clauses» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloaded:case_1:iter:2:clause:0» V_T input0), fun (_ : _root_.Unit) => («$find_overloaded:case_1:iter:2:clause:1» V_T input0)]


noncomputable def «$find_overloaded:case_1:iter:3:clause:0» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$find_overloaded:case_1:iter:3:clause:1» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id? : (_root_.Option id) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option id)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome id?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$find_overloaded:case_1:iter:3» V_T «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «$find_overloaded:case_1:iter:3_clauses» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloaded:case_1:iter:3:clause:0» V_T input0), fun (_ : _root_.Unit) => («$find_overloaded:case_1:iter:3:clause:1» V_T input0)]


noncomputable def «$find_overloaded:case_1:iter:4:clause:0» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List id)) : (_root_.List id)))) | _ :: _ => .unmatch)


noncomputable def «$find_overloaded:case_1:iter:4:clause:1» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id? : (_root_.Option id) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option id)) := «exec:1»; (match id? with | some «exec:3» => (let id_arg_inner : id := «exec:3»; (.bind (.call ⟨(_root_.List id), SpecTecCall.«$find_overloaded:case_1:iter:4» V_T «tail:0»⟩) (fun («exec:4» : (_root_.List id)) => (let «tail:1» : (_root_.List id) := «exec:4»; (.pure (((id_arg_inner :: «tail:1») : (_root_.List id)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «$find_overloaded:case_1:iter:4_clauses» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloaded:case_1:iter:4:clause:0» V_T input0), fun (_ : _root_.Unit) => («$find_overloaded:case_1:iter:4:clause:1» V_T input0)]


noncomputable def «$find_overloaded:case_1:iter:5:clause:0» (V_T : Type) (input0 : (_root_.List V_T)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId V_T))) : (_root_.List (pair callTargetId V_T))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$find_overloaded:case_1:iter:5:clause:1» (V_T : Type) (input0 : (_root_.List V_T)) (input1 : (_root_.List SpecTec.callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let V : V_T := «exec:2»; (let «tail:0» : (_root_.List V_T) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId : SpecTec.callableId := «exec:4»; (let «tail:1» : (_root_.List SpecTec.callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId V_T)), SpecTecCall.«$find_overloaded:case_1:iter:5» V_T «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId V_T))) => (let «tail:2» : (_root_.List (pair callTargetId V_T)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId V) : (pair SpecTec.callableId V_T)) :: «tail:2») : (_root_.List (pair callTargetId V_T)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$find_overloaded:case_1:iter:5_clauses» (V_T : Type) (input0 : (_root_.List V_T)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloaded:case_1:iter:5:clause:0» V_T input0 input1), fun (_ : _root_.Unit) => («$find_overloaded:case_1:iter:5:clause:1» V_T input0 input1)]


noncomputable def «$find_overloaded:case_2:pattern-iter:0:clause:0» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List V_T)), ([] : (_root_.List callableId))) : ((_root_.List V_T) × (_root_.List callableId))))) | _ :: _ => .unmatch)


noncomputable def «$find_overloaded:case_2:pattern-iter:0:clause:1» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId : SpecTec.callableId := «exec:3»; (let V : V_T := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId V_T)) := «exec:1»; (.bind (.call ⟨((_root_.List V_T) × (_root_.List SpecTec.callableId)), SpecTecCall.«$find_overloaded:case_2:pattern-iter:0» V_T «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List V_T) × (_root_.List SpecTec.callableId))) => (let «pattern-tail:1» : (_root_.List V_T) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.callableId) := («exec:5»).2; (.pure ((((V :: «pattern-tail:1»), (callableId :: «pattern-tail:2»)) : ((_root_.List V_T) × (_root_.List SpecTec.callableId))))))))))))) | [] => .unmatch)


noncomputable def «$find_overloaded:case_2:pattern-iter:0_clauses» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloaded:case_2:pattern-iter:0:clause:0» V_T input0), fun (_ : _root_.Unit) => («$find_overloaded:case_2:pattern-iter:0:clause:1» V_T input0)]


noncomputable def «$find_overloaded:case_2:iter:2:clause:0» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.Option id))) : (_root_.List (_root_.Option id))))) | _ :: _ => .unmatch)


noncomputable def «$find_overloaded:case_2:iter:2:clause:1» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_arg? : (_root_.Option id) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option id)) := «exec:1»; (let id? : (_root_.Option id) := id_arg?; (.bind (.call ⟨(_root_.List (_root_.Option id)), SpecTecCall.«$find_overloaded:case_2:iter:2» V_T «tail:0»⟩) (fun («exec:3» : (_root_.List (_root_.Option id))) => (let «tail:1» : (_root_.List (_root_.Option id)) := «exec:3»; (.pure (((id? :: «tail:1») : (_root_.List (_root_.Option id))))))))))) | [] => .unmatch)


noncomputable def «$find_overloaded:case_2:iter:2_clauses» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloaded:case_2:iter:2:clause:0» V_T input0), fun (_ : _root_.Unit) => («$find_overloaded:case_2:iter:2:clause:1» V_T input0)]

end SpecTec
