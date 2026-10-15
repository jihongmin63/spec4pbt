import SpecTecDecl0158

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$match_overloaded_unnamed:case_1:iter:1_clauses» (V_T : Type) (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_1:iter:1:clause:0» V_T input0), fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_1:iter:1:clause:1» V_T input0)]


noncomputable def «$match_overloaded_unnamed:case_2:iter:1:clause:0» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_2:iter:1:clause:1» (V_T : Type) (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_default_parameterIR» parameterIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:3»; (let b_default : _root_.Bool := «eval:2»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_unnamed:case_2:iter:1» V_T «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((b_default :: «tail:1») : (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_2:iter:1_clauses» (V_T : Type) (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_2:iter:1:clause:0» V_T input0), fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_2:iter:1:clause:1» V_T input0)]


noncomputable def «$match_overloaded_unnamed:case_2:iter:10:clause:0» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_2:iter:10:clause:1» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_omitted : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_default_parameterIR» parameterIR_omitted⟩) (fun («exec:3» : _root_.Bool) => (let «eval:11» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:11» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$match_overloaded_unnamed:case_2:iter:10» V_T «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_2:iter:10_clauses» (V_T : Type) (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_2:iter:10:clause:0» V_T input0), fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_2:iter:10:clause:1» V_T input0)]


noncomputable def «$match_overloaded_unnamed:case_2:iter:12:clause:0» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List id)) : (_root_.List id)))) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_2:iter:12:clause:1» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_omitted : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨id, SpecTecCall.«$id_of_parameterIR» parameterIR_omitted⟩) (fun («exec:3» : id) => (let «eval:13» : id := «exec:3»; (let id_default : id := «eval:13»; (.bind (.call ⟨(_root_.List id), SpecTecCall.«$match_overloaded_unnamed:case_2:iter:12» V_T «tail:0»⟩) (fun («exec:4» : (_root_.List id)) => (let «tail:1» : (_root_.List id) := «exec:4»; (.pure (((id_default :: «tail:1») : (_root_.List id))))))))))))) | [] => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_2:iter:12_clauses» (V_T : Type) (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_2:iter:12:clause:0» V_T input0), fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_2:iter:12:clause:1» V_T input0)]


noncomputable def «$match_overloaded_unnamed:case_3:iter:1:clause:0» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_3:iter:1:clause:1» (V_T : Type) (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_default_parameterIR» parameterIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:3»; (let b_default : _root_.Bool := «eval:2»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_unnamed:case_3:iter:1» V_T «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((b_default :: «tail:1») : (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_3:iter:1_clauses» (V_T : Type) (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_3:iter:1:clause:0» V_T input0), fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_3:iter:1:clause:1» V_T input0)]


noncomputable def «$match_overloaded_unnamed:case_3:iter:8:clause:0» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_3:iter:8:clause:1» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_given : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_default_parameterIR» parameterIR_given⟩) (fun («exec:3» : _root_.Bool) => (let «eval:9» : _root_.Bool := «exec:3»; (.bind (.guard ((¬ («eval:9» = true)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$match_overloaded_unnamed:case_3:iter:8» V_T «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_3:iter:8_clauses» (V_T : Type) (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_3:iter:8:clause:0» V_T input0), fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_3:iter:8:clause:1» V_T input0)]


noncomputable def «$match_overloaded_unnamed:case_3:iter:12:clause:0» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List id)) : (_root_.List id)))) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_3:iter:12:clause:1» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_omitted : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨id, SpecTecCall.«$id_of_parameterIR» parameterIR_omitted⟩) (fun («exec:3» : id) => (let «eval:13» : id := «exec:3»; (let id_optional : id := «eval:13»; (.bind (.call ⟨(_root_.List id), SpecTecCall.«$match_overloaded_unnamed:case_3:iter:12» V_T «tail:0»⟩) (fun («exec:4» : (_root_.List id)) => (let «tail:1» : (_root_.List id) := «exec:4»; (.pure (((id_optional :: «tail:1») : (_root_.List id))))))))))))) | [] => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_3:iter:12_clauses» (V_T : Type) (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_3:iter:12:clause:0» V_T input0), fun (_ : _root_.Unit) => («$match_overloaded_unnamed:case_3:iter:12:clause:1» V_T input0)]


noncomputable def «$find_overloadeds_named:case_2:pattern-iter:0:clause:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List V)), ([] : (_root_.List callTargetId))) : ((_root_.List V) × (_root_.List callTargetId))))) | _ :: _ => .unmatch)


noncomputable def «$find_overloadeds_named:case_2:pattern-iter:0:clause:1» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callTargetId_t : callTargetId := «exec:3»; (let V_t : V := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId V)) := «exec:1»; (.bind (.call ⟨((_root_.List V) × (_root_.List callTargetId)), SpecTecCall.«$find_overloadeds_named:case_2:pattern-iter:0» V «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List V) × (_root_.List callTargetId))) => (let «pattern-tail:1» : (_root_.List V) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List callTargetId) := («exec:5»).2; (.pure ((((V_t :: «pattern-tail:1»), (callTargetId_t :: «pattern-tail:2»)) : ((_root_.List V) × (_root_.List callTargetId))))))))))))) | [] => .unmatch)


noncomputable def «$find_overloadeds_named:case_2:pattern-iter:0_clauses» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloadeds_named:case_2:pattern-iter:0:clause:0» V input0), fun (_ : _root_.Unit) => («$find_overloadeds_named:case_2:pattern-iter:0:clause:1» V input0)]


noncomputable def «$find_overloadeds_named:case_2:iter:3:clause:0» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId V))) : (_root_.List (pair callTargetId V))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$find_overloadeds_named:case_2:iter:3:clause:1» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let V_t : V := «exec:2»; (let «tail:0» : (_root_.List V) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callTargetId_t : callTargetId := «exec:4»; (let «tail:1» : (_root_.List callTargetId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_overloadeds_named:case_2:iter:3» V «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId V))) => (let «tail:2» : (_root_.List (pair callTargetId V)) := «exec:5»; (.pure (((((pair.«% ':' %» callTargetId_t V_t) : (pair callableId V)) :: «tail:2») : (_root_.List (pair callTargetId V)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$find_overloadeds_named:case_2:iter:3_clauses» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloadeds_named:case_2:iter:3:clause:0» V input0 input1), fun (_ : _root_.Unit) => («$find_overloadeds_named:case_2:iter:3:clause:1» V input0 input1)]


noncomputable def «$find_overloadeds_named:case_3:pattern-iter:0:clause:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List V)), ([] : (_root_.List callTargetId))) : ((_root_.List V) × (_root_.List callTargetId))))) | _ :: _ => .unmatch)


noncomputable def «$find_overloadeds_named:case_3:pattern-iter:0:clause:1» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callTargetId_t : callTargetId := «exec:3»; (let V_t : V := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId V)) := «exec:1»; (.bind (.call ⟨((_root_.List V) × (_root_.List callTargetId)), SpecTecCall.«$find_overloadeds_named:case_3:pattern-iter:0» V «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List V) × (_root_.List callTargetId))) => (let «pattern-tail:1» : (_root_.List V) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List callTargetId) := («exec:5»).2; (.pure ((((V_t :: «pattern-tail:1»), (callTargetId_t :: «pattern-tail:2»)) : ((_root_.List V) × (_root_.List callTargetId))))))))))))) | [] => .unmatch)


noncomputable def «$find_overloadeds_named:case_3:pattern-iter:0_clauses» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloadeds_named:case_3:pattern-iter:0:clause:0» V input0), fun (_ : _root_.Unit) => («$find_overloadeds_named:case_3:pattern-iter:0:clause:1» V input0)]


noncomputable def «$find_overloadeds_named:case_3:iter:3:clause:0» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId V))) : (_root_.List (pair callTargetId V))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$find_overloadeds_named:case_3:iter:3:clause:1» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let V_t : V := «exec:2»; (let «tail:0» : (_root_.List V) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callTargetId_t : callTargetId := «exec:4»; (let «tail:1» : (_root_.List callTargetId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_overloadeds_named:case_3:iter:3» V «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId V))) => (let «tail:2» : (_root_.List (pair callTargetId V)) := «exec:5»; (.pure (((((pair.«% ':' %» callTargetId_t V_t) : (pair callableId V)) :: «tail:2») : (_root_.List (pair callTargetId V)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$find_overloadeds_named:case_3:iter:3_clauses» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_overloadeds_named:case_3:iter:3:clause:0» V input0 input1), fun (_ : _root_.Unit) => («$find_overloadeds_named:case_3:iter:3:clause:1» V input0 input1)]


noncomputable def «$find_overloadeds_unnamed:case_2:pattern-iter:0:clause:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List V)), ([] : (_root_.List callTargetId))) : ((_root_.List V) × (_root_.List callTargetId))))) | _ :: _ => .unmatch)

end SpecTec
