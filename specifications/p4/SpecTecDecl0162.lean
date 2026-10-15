import SpecTecDecl0161

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$find_non_overloaded:case_1:iter:2_clauses» (V_T : Type) (input0 : (_root_.List V_T)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloaded:case_1:iter:2:clause:0» V_T input0 input1), fun (_ : _root_.Unit) => («$find_non_overloaded:case_1:iter:2:clause:1» V_T input0 input1)]


noncomputable def «$find_non_overloaded:case_2:pattern-iter:0:clause:0» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List V_T)), ([] : (_root_.List callableId))) : ((_root_.List V_T) × (_root_.List callableId))))) | _ :: _ => .unmatch)


noncomputable def «$find_non_overloaded:case_2:pattern-iter:0:clause:1» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId : SpecTec.callableId := «exec:3»; (let V : V_T := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId V_T)) := «exec:1»; (.bind (.call ⟨((_root_.List V_T) × (_root_.List SpecTec.callableId)), SpecTecCall.«$find_non_overloaded:case_2:pattern-iter:0» V_T «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List V_T) × (_root_.List SpecTec.callableId))) => (let «pattern-tail:1» : (_root_.List V_T) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.callableId) := («exec:5»).2; (.pure ((((V :: «pattern-tail:1»), (callableId :: «pattern-tail:2»)) : ((_root_.List V_T) × (_root_.List SpecTec.callableId))))))))))))) | [] => .unmatch)


noncomputable def «$find_non_overloaded:case_2:pattern-iter:0_clauses» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloaded:case_2:pattern-iter:0:clause:0» V_T input0), fun (_ : _root_.Unit) => («$find_non_overloaded:case_2:pattern-iter:0:clause:1» V_T input0)]


noncomputable def «$find_non_overloadeds:case_2:pattern-iter:0:clause:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List V)), ([] : (_root_.List callableId))) : ((_root_.List V) × (_root_.List callableId))))) | _ :: _ => .unmatch)


noncomputable def «$find_non_overloadeds:case_2:pattern-iter:0:clause:1» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId_t : callableId := «exec:3»; (let V_t : V := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId V)) := «exec:1»; (.bind (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_2:pattern-iter:0» V «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List V) × (_root_.List callableId))) => (let «pattern-tail:1» : (_root_.List V) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List callableId) := («exec:5»).2; (.pure ((((V_t :: «pattern-tail:1»), (callableId_t :: «pattern-tail:2»)) : ((_root_.List V) × (_root_.List callableId))))))))))))) | [] => .unmatch)


noncomputable def «$find_non_overloadeds:case_2:pattern-iter:0_clauses» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloadeds:case_2:pattern-iter:0:clause:0» V input0), fun (_ : _root_.Unit) => («$find_non_overloadeds:case_2:pattern-iter:0:clause:1» V input0)]


noncomputable def «$find_non_overloadeds:case_2:iter:2:clause:0» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId V))) : (_root_.List (pair callTargetId V))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$find_non_overloadeds:case_2:iter:2:clause:1» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let V_t : V := «exec:2»; (let «tail:0» : (_root_.List V) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId_t : callableId := «exec:4»; (let «tail:1» : (_root_.List callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_non_overloadeds:case_2:iter:2» V «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId V))) => (let «tail:2» : (_root_.List (pair callTargetId V)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId_t V_t) : (pair callableId V)) :: «tail:2») : (_root_.List (pair callTargetId V)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$find_non_overloadeds:case_2:iter:2_clauses» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloadeds:case_2:iter:2:clause:0» V input0 input1), fun (_ : _root_.Unit) => («$find_non_overloadeds:case_2:iter:2:clause:1» V input0 input1)]


noncomputable def «$find_non_overloadeds:case_2:pattern-iter:5:clause:0» (V : Type) (input0 : (_root_.List (callTargetId × V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List V)), ([] : (_root_.List callableId))) : ((_root_.List V) × (_root_.List callableId))))) | _ :: _ => .unmatch)


noncomputable def «$find_non_overloadeds:case_2:pattern-iter:5:clause:1» (V : Type) (input0 : (_root_.List (callTargetId × V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableId_t_found : callableId := («exec:2»).1; (let V_t_found : V := («exec:2»).2; (let «pattern-tail:0» : (_root_.List (callTargetId × V)) := «exec:1»; (.bind (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_2:pattern-iter:5» V «pattern-tail:0»⟩) (fun («exec:3» : ((_root_.List V) × (_root_.List callableId))) => (let «pattern-tail:1» : (_root_.List V) := («exec:3»).1; (let «pattern-tail:2» : (_root_.List callableId) := («exec:3»).2; (.pure ((((V_t_found :: «pattern-tail:1»), (callableId_t_found :: «pattern-tail:2»)) : ((_root_.List V) × (_root_.List callableId)))))))))))) | [] => .unmatch)


noncomputable def «$find_non_overloadeds:case_2:pattern-iter:5_clauses» (V : Type) (input0 : (_root_.List (callTargetId × V))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloadeds:case_2:pattern-iter:5:clause:0» V input0), fun (_ : _root_.Unit) => («$find_non_overloadeds:case_2:pattern-iter:5:clause:1» V input0)]


noncomputable def «$find_non_overloadeds:case_2:iter:7:clause:0» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (callTargetId × V))) : (_root_.List (callTargetId × V))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$find_non_overloadeds:case_2:iter:7:clause:1» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let V_t_found : V := «exec:2»; (let «tail:0» : (_root_.List V) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId_t_found : callableId := «exec:4»; (let «tail:1» : (_root_.List callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (callTargetId × V)), SpecTecCall.«$find_non_overloadeds:case_2:iter:7» V «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (callTargetId × V))) => (let «tail:2» : (_root_.List (callTargetId × V)) := «exec:5»; (.pure ((((callableId_t_found, V_t_found) :: «tail:2») : (_root_.List (callTargetId × V)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$find_non_overloadeds:case_2:iter:7_clauses» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloadeds:case_2:iter:7:clause:0» V input0 input1), fun (_ : _root_.Unit) => («$find_non_overloadeds:case_2:iter:7:clause:1» V input0 input1)]


noncomputable def «$find_non_overloadeds:case_3:pattern-iter:0:clause:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List V)), ([] : (_root_.List callableId))) : ((_root_.List V) × (_root_.List callableId))))) | _ :: _ => .unmatch)


noncomputable def «$find_non_overloadeds:case_3:pattern-iter:0:clause:1» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId_t : callableId := «exec:3»; (let V_t : V := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId V)) := «exec:1»; (.bind (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_3:pattern-iter:0» V «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List V) × (_root_.List callableId))) => (let «pattern-tail:1» : (_root_.List V) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List callableId) := («exec:5»).2; (.pure ((((V_t :: «pattern-tail:1»), (callableId_t :: «pattern-tail:2»)) : ((_root_.List V) × (_root_.List callableId))))))))))))) | [] => .unmatch)


noncomputable def «$find_non_overloadeds:case_3:pattern-iter:0_clauses» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloadeds:case_3:pattern-iter:0:clause:0» V input0), fun (_ : _root_.Unit) => («$find_non_overloadeds:case_3:pattern-iter:0:clause:1» V input0)]


noncomputable def «$find_non_overloadeds:case_3:iter:2:clause:0» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId V))) : (_root_.List (pair callTargetId V))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$find_non_overloadeds:case_3:iter:2:clause:1» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let V_t : V := «exec:2»; (let «tail:0» : (_root_.List V) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId_t : callableId := «exec:4»; (let «tail:1» : (_root_.List callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_non_overloadeds:case_3:iter:2» V «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId V))) => (let «tail:2» : (_root_.List (pair callTargetId V)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId_t V_t) : (pair callableId V)) :: «tail:2») : (_root_.List (pair callTargetId V)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$find_non_overloadeds:case_3:iter:2_clauses» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloadeds:case_3:iter:2:clause:0» V input0 input1), fun (_ : _root_.Unit) => («$find_non_overloadeds:case_3:iter:2:clause:1» V input0 input1)]


noncomputable def «$find_non_overloadeds:case_3:pattern-iter:5:clause:0» (V : Type) (input0 : (_root_.List (callTargetId × V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List V)), ([] : (_root_.List callableId))) : ((_root_.List V) × (_root_.List callableId))))) | _ :: _ => .unmatch)


noncomputable def «$find_non_overloadeds:case_3:pattern-iter:5:clause:1» (V : Type) (input0 : (_root_.List (callTargetId × V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableId_t_found : callableId := («exec:2»).1; (let V_t_found : V := («exec:2»).2; (let «pattern-tail:0» : (_root_.List (callTargetId × V)) := «exec:1»; (.bind (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_3:pattern-iter:5» V «pattern-tail:0»⟩) (fun («exec:3» : ((_root_.List V) × (_root_.List callableId))) => (let «pattern-tail:1» : (_root_.List V) := («exec:3»).1; (let «pattern-tail:2» : (_root_.List callableId) := («exec:3»).2; (.pure ((((V_t_found :: «pattern-tail:1»), (callableId_t_found :: «pattern-tail:2»)) : ((_root_.List V) × (_root_.List callableId)))))))))))) | [] => .unmatch)


noncomputable def «$find_non_overloadeds:case_3:pattern-iter:5_clauses» (V : Type) (input0 : (_root_.List (callTargetId × V))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloadeds:case_3:pattern-iter:5:clause:0» V input0), fun (_ : _root_.Unit) => («$find_non_overloadeds:case_3:pattern-iter:5:clause:1» V input0)]


noncomputable def «$find_non_overloadeds:case_3:iter:7:clause:0» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (callTargetId × V))) : (_root_.List (callTargetId × V))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$find_non_overloadeds:case_3:iter:7:clause:1» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let V_t_found : V := «exec:2»; (let «tail:0» : (_root_.List V) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId_t_found : callableId := «exec:4»; (let «tail:1» : (_root_.List callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (callTargetId × V)), SpecTecCall.«$find_non_overloadeds:case_3:iter:7» V «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (callTargetId × V))) => (let «tail:2» : (_root_.List (callTargetId × V)) := «exec:5»; (.pure ((((callableId_t_found, V_t_found) :: «tail:2») : (_root_.List (callTargetId × V)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$find_non_overloadeds:case_3:iter:7_clauses» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloadeds:case_3:iter:7:clause:0» V input0 input1), fun (_ : _root_.Unit) => («$find_non_overloadeds:case_3:iter:7:clause:1» V input0 input1)]


noncomputable def «$find_non_overloadeds:clause:0» (V : Type) (input0 : (map callableId V)) (input1 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «set<pair<callableId, V>>» : (set (pair callableId V)) := input0; (let nameIR_f : nameIR := input1; (.bind (.guard (((set.«`{ % `}» ([] : (_root_.List (pair callableId V)))) : (set (pair callableId V))) = «set<pair<callableId, V>>»)) (fun (_ : Unit) => (.pure ((([] : (_root_.List (callableId × V))) : (_root_.List (callableId × V)))))))))


noncomputable def «$find_non_overloadeds:clause:1» (V : Type) (input0 : (map callableId V)) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «pair<callableId, V>*» : (_root_.List (pair callableId V)) := «exec:1»; (let nameIR_f : SpecTec.nameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «pair<callableId, V>*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «pair<callableId, V>*» with | «exec:3» :: «exec:2» => (match «exec:3» with | .«% ':' %» «exec:4» «exec:5» => (let callableId_h : callableId := «exec:4»; (let V_h : V := «exec:5»; (let «eval:1» : (_root_.List (pair callableId V)) := «exec:2»; (.bind (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_2:pattern-iter:0» V «eval:1»⟩) (fun («exec:6» : ((_root_.List V) × (_root_.List callableId))) => (let «V_t*» : (_root_.List V) := («exec:6»).1; (let «callableId_t*» : (_root_.List callableId) := («exec:6»).2; (match callableId_h with | .«% `( % `)» «exec:7» «exec:8» => (let nameIR : SpecTec.nameIR := «exec:7»; (let «_id*» : (_root_.List id) := «exec:8»; (.bind (.guard (nameIR_f = nameIR)) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_non_overloadeds:case_2:iter:2» V «V_t*» «callableId_t*»⟩) (fun («exec:9» : (_root_.List (pair callTargetId V))) => (let «eval:3» : (_root_.List (pair callableId V)) := «exec:9»; (.bind (.call ⟨(_root_.List (callableId × V)), SpecTecCall.«$find_non_overloadeds» V ((set.«`{ % `}» «eval:3») : (set (pair callableId V))) nameIR_f⟩) (fun («exec:10» : (_root_.List (callableId × V))) => (let «eval:4» : (_root_.List (callableId × V)) := «exec:10»; (let «eval:6» : (_root_.List (callableId × V)) := «eval:4»; (.bind (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_2:pattern-iter:5» V «eval:6»⟩) (fun («exec:11» : ((_root_.List V) × (_root_.List callableId))) => (let «V_t_found*» : (_root_.List V) := («exec:11»).1; (let «callableId_t_found*» : (_root_.List callableId) := («exec:11»).2; (.bind (.call ⟨(_root_.List (callTargetId × V)), SpecTecCall.«$find_non_overloadeds:case_2:iter:7» V «V_t_found*» «callableId_t_found*»⟩) (fun («exec:12» : (_root_.List (callTargetId × V))) => (let «eval:8» : (_root_.List (callableId × V)) := «exec:12»; (.pure ((((callableId_h, V_h) :: «eval:8») : (_root_.List (callableId × V)))))))))))))))))))))))))))))))) | [] => .unmatch))))))


noncomputable def «$find_non_overloadeds:clause:2» (V : Type) (input0 : (map callableId V)) (input1 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «pair<callableId, V>*» : (_root_.List (pair callableId V)) := «exec:1»; (let nameIR_f : nameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «pair<callableId, V>*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «pair<callableId, V>*» with | «exec:3» :: «exec:2» => (match «exec:3» with | .«% ':' %» «exec:4» «exec:5» => (let callableId_h : callableId := «exec:4»; (let V_h : V := «exec:5»; (let «eval:1» : (_root_.List (pair callableId V)) := «exec:2»; (.bind (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_3:pattern-iter:0» V «eval:1»⟩) (fun («exec:6» : ((_root_.List V) × (_root_.List callableId))) => (let «V_t*» : (_root_.List V) := («exec:6»).1; (let «callableId_t*» : (_root_.List callableId) := («exec:6»).2; (match callableId_h with | .«% `( % `)» «exec:7» «exec:8» => (let nameIR_f_h : nameIR := «exec:7»; (let «_id*» : (_root_.List id) := «exec:8»; (.bind (.guard ((nameIR_f ≠ nameIR_f_h))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List (pair callTargetId V)), SpecTecCall.«$find_non_overloadeds:case_3:iter:2» V «V_t*» «callableId_t*»⟩) (fun («exec:9» : (_root_.List (pair callTargetId V))) => (let «eval:3» : (_root_.List (pair callableId V)) := «exec:9»; (.bind (.call ⟨(_root_.List (callableId × V)), SpecTecCall.«$find_non_overloadeds» V ((set.«`{ % `}» «eval:3») : (set (pair callableId V))) nameIR_f⟩) (fun («exec:10» : (_root_.List (callableId × V))) => (let «eval:4» : (_root_.List (callableId × V)) := «exec:10»; (let «eval:6» : (_root_.List (callableId × V)) := «eval:4»; (.bind (.call ⟨((_root_.List V) × (_root_.List callableId)), SpecTecCall.«$find_non_overloadeds:case_3:pattern-iter:5» V «eval:6»⟩) (fun («exec:11» : ((_root_.List V) × (_root_.List callableId))) => (let «V_t_found*» : (_root_.List V) := («exec:11»).1; (let «callableId_t_found*» : (_root_.List callableId) := («exec:11»).2; (.bind (.call ⟨(_root_.List (callTargetId × V)), SpecTecCall.«$find_non_overloadeds:case_3:iter:7» V «V_t_found*» «callableId_t_found*»⟩) (fun («exec:12» : (_root_.List (callTargetId × V))) => (let «eval:8» : (_root_.List (callableId × V)) := «exec:12»; (.pure ((«eval:8» : (_root_.List (callableId × V)))))))))))))))))))))))))))))))) | [] => .unmatch))))))


noncomputable def «$find_non_overloadeds_clauses» (V : Type) (input0 : (map callableId V)) (input1 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloadeds:clause:0» V input0 input1), fun (_ : _root_.Unit) => («$find_non_overloadeds:clause:1» V input0 input1), fun (_ : _root_.Unit) => («$find_non_overloadeds:clause:2» V input0 input1)]

end SpecTec
