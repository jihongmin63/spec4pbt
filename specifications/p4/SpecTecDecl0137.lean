import SpecTecDecl0136

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$find_maps:clause:0» (K : Type) (V : Type) (input0 : (_root_.List (map K V))) (input1 : K) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (let k : K := input1; (.pure (((_root_.Option.none) : (_root_.Option V))))) | _ :: _ => .unmatch)


noncomputable def «$find_maps:clause:1» (K : Type) (V : Type) (input0 : (_root_.List (map K V))) (input1 : K) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let m : (map K V) := «exec:2»; (let ms : (_root_.List (map K V)) := «exec:1»; (let k : K := input1; (.bind (.call ⟨(_root_.Option V), SpecTecCall.«$find_map» K V m k⟩) (fun («exec:3» : (_root_.Option V)) => (match «exec:3» with | some «exec:4» => (let v : V := «exec:4»; (.pure (((_root_.Option.some v) : (_root_.Option V))))) | none => .unmatch)))))) | [] => .unmatch)


noncomputable def «$find_maps:clause:2» (K : Type) (V : Type) (input0 : (_root_.List (map K V))) (input1 : K) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let m : (map K V) := «exec:2»; (let ms : (_root_.List (map K V)) := «exec:1»; (let k : K := input1; (.bind (.call ⟨(_root_.Option V), SpecTecCall.«$find_map» K V m k⟩) (fun («exec:3» : (_root_.Option V)) => (match «exec:3» with | none => (.bind (.call ⟨(_root_.Option V), SpecTecCall.«$find_maps» K V ms k⟩) (fun («exec:4» : (_root_.Option V)) => (let r : (_root_.Option V) := «exec:4»; (.pure ((r : (_root_.Option V))))))) | some _ => .unmatch)))))) | [] => .unmatch)


noncomputable def «$find_maps_clauses» (K : Type) (V : Type) (input0 : (_root_.List (map K V))) (input1 : K) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_maps:clause:0» K V input0 input1), fun (_ : _root_.Unit) => («$find_maps:clause:1» K V input0 input1), fun (_ : _root_.Unit) => («$find_maps:clause:2» K V input0 input1)]


noncomputable def «$add_map:list:clause:0» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) (input2 : V) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (let k : K := input1; (let v : V := input2; (.pure (([((pair.«% ':' %» k v) : (pair K V))] : (_root_.List (pair K V))))))) | _ :: _ => .unmatch)


noncomputable def «$add_map:list:clause:1» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) (input2 : V) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let k : K := «exec:3»; (let old : V := «exec:4»; (let ps : (_root_.List (pair K V)) := «exec:1»; (.bind (.guard (input1 = k)) (fun (_ : Unit) => (let v : V := input2; (.pure (((((pair.«% ':' %» k v) : (pair K V)) :: ps) : (_root_.List (pair K V)))))))))))) | [] => .unmatch)


noncomputable def «$add_map:list:clause:2» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) (input2 : V) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let k' : K := «exec:3»; (let old : V := «exec:4»; (let ps : (_root_.List (pair K V)) := «exec:1»; (let k : K := input1; (let v : V := input2; (.bind (.guard ((k' ≠ k))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$add_map:list» K V ps k v⟩) (fun («exec:5» : (_root_.List (pair K V))) => (let qs : (_root_.List (pair K V)) := «exec:5»; (.pure (((((pair.«% ':' %» k' old) : (pair K V)) :: qs) : (_root_.List (pair K V)))))))))))))))) | [] => .unmatch)


noncomputable def «$add_map:list_clauses» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) (input2 : V) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_map:list:clause:0» K V input0 input1 input2), fun (_ : _root_.Unit) => («$add_map:list:clause:1» K V input0 input1 input2), fun (_ : _root_.Unit) => («$add_map:list:clause:2» K V input0 input1 input2)]


noncomputable def «$add_map:clause:0» (K : Type) (V : Type) (input0 : (map K V)) (input1 : K) (input2 : V) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let ps : (_root_.List (pair K V)) := «exec:1»; (let k : K := input1; (let v : V := input2; (.bind (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$add_map:list» K V ps k v⟩) (fun («exec:2» : (_root_.List (pair K V))) => (let qs : (_root_.List (pair K V)) := «exec:2»; (.pure ((((set.«`{ % `}» qs) : (set (pair K V))) : (map K V)))))))))))


noncomputable def «$add_map_clauses» (K : Type) (V : Type) (input0 : (map K V)) (input1 : K) (input2 : V) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_map:clause:0» K V input0 input1 input2)]


noncomputable def «$adds_map:clause:0» (K : Type) (V : Type) (input0 : (map K V)) (input1 : (_root_.List K)) (input2 : (_root_.List V)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let m : (map K V) := input0; (match input1 with | [] => (match input2 with | [] => (.pure ((m : (map K V)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch))


noncomputable def «$adds_map:clause:1» (K : Type) (V : Type) (input0 : (map K V)) (input1 : (_root_.List K)) (input2 : (_root_.List V)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let m : (map K V) := input0; (match input1 with | «exec:2» :: «exec:1» => (let k : K := «exec:2»; (let ks : (_root_.List K) := «exec:1»; (match input2 with | «exec:4» :: «exec:3» => (let v : V := «exec:4»; (let vs : (_root_.List V) := «exec:3»; (.bind (.call ⟨(map K V), SpecTecCall.«$add_map» K V m k v⟩) (fun («exec:5» : (map K V)) => (let next : (map K V) := «exec:5»; (.bind (.call ⟨(map K V), SpecTecCall.«$adds_map» K V next ks vs⟩) (fun («exec:6» : (map K V)) => (let r : (map K V) := «exec:6»; (.pure ((r : (map K V)))))))))))) | [] => .unmatch))) | [] => .unmatch))


noncomputable def «$adds_map_clauses» (K : Type) (V : Type) (input0 : (map K V)) (input1 : (_root_.List K)) (input2 : (_root_.List V)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$adds_map:clause:0» K V input0 input1 input2), fun (_ : _root_.Unit) => («$adds_map:clause:1» K V input0 input1 input2), fun (_ : _root_.Unit) => .abort "builtin $adds_map failed"]


noncomputable def «$update_map:list:clause:0» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) (input2 : V) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (let k : K := input1; (let v : V := input2; (.pure (([((pair.«% ':' %» k v) : (pair K V))] : (_root_.List (pair K V))))))) | _ :: _ => .unmatch)


noncomputable def «$update_map:list:clause:1» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) (input2 : V) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let k : K := «exec:3»; (let old : V := «exec:4»; (let ps : (_root_.List (pair K V)) := «exec:1»; (.bind (.guard (input1 = k)) (fun (_ : Unit) => (let v : V := input2; (.pure (((((pair.«% ':' %» k v) : (pair K V)) :: ps) : (_root_.List (pair K V)))))))))))) | [] => .unmatch)


noncomputable def «$update_map:list:clause:2» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) (input2 : V) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let k' : K := «exec:3»; (let old : V := «exec:4»; (let ps : (_root_.List (pair K V)) := «exec:1»; (let k : K := input1; (let v : V := input2; (.bind (.guard ((k' ≠ k))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$update_map:list» K V ps k v⟩) (fun («exec:5» : (_root_.List (pair K V))) => (let qs : (_root_.List (pair K V)) := «exec:5»; (.pure (((((pair.«% ':' %» k' old) : (pair K V)) :: qs) : (_root_.List (pair K V)))))))))))))))) | [] => .unmatch)


noncomputable def «$update_map:list_clauses» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) (input2 : V) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_map:list:clause:0» K V input0 input1 input2), fun (_ : _root_.Unit) => («$update_map:list:clause:1» K V input0 input1 input2), fun (_ : _root_.Unit) => («$update_map:list:clause:2» K V input0 input1 input2)]


noncomputable def «$update_map:clause:0» (K : Type) (V : Type) (input0 : (map K V)) (input1 : K) (input2 : V) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let ps : (_root_.List (pair K V)) := «exec:1»; (let k : K := input1; (let v : V := input2; (.bind (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$update_map:list» K V ps k v⟩) (fun («exec:2» : (_root_.List (pair K V))) => (let qs : (_root_.List (pair K V)) := «exec:2»; (.pure ((((set.«`{ % `}» qs) : (set (pair K V))) : (map K V)))))))))))


noncomputable def «$update_map_clauses» (K : Type) (V : Type) (input0 : (map K V)) (input1 : K) (input2 : V) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_map:clause:0» K V input0 input1 input2)]


noncomputable def «$extend_map:case_1:pattern-iter:0:clause:0» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List K)), ([] : (_root_.List V))) : ((_root_.List K) × (_root_.List V))))) | _ :: _ => .unmatch)


noncomputable def «$extend_map:case_1:pattern-iter:0:clause:1» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let K_a : K := «exec:3»; (let V_a : V := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair K V)) := «exec:1»; (.bind (.call ⟨((_root_.List K) × (_root_.List V)), SpecTecCall.«$extend_map:case_1:pattern-iter:0» K V «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List K) × (_root_.List V))) => (let «pattern-tail:1» : (_root_.List K) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List V) := («exec:5»).2; (.pure ((((K_a :: «pattern-tail:1»), (V_a :: «pattern-tail:2»)) : ((_root_.List K) × (_root_.List V))))))))))))) | [] => .unmatch)


noncomputable def «$extend_map:case_1:pattern-iter:0_clauses» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$extend_map:case_1:pattern-iter:0:clause:0» K V input0), fun (_ : _root_.Unit) => («$extend_map:case_1:pattern-iter:0:clause:1» K V input0)]


noncomputable def «$extend_map:case_1:pattern-iter:2:clause:0» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List K)), ([] : (_root_.List V))) : ((_root_.List K) × (_root_.List V))))) | _ :: _ => .unmatch)


noncomputable def «$extend_map:case_1:pattern-iter:2:clause:1» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let K_b : K := «exec:3»; (let V_b : V := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair K V)) := «exec:1»; (.bind (.call ⟨((_root_.List K) × (_root_.List V)), SpecTecCall.«$extend_map:case_1:pattern-iter:2» K V «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List K) × (_root_.List V))) => (let «pattern-tail:1» : (_root_.List K) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List V) := («exec:5»).2; (.pure ((((K_b :: «pattern-tail:1»), (V_b :: «pattern-tail:2»)) : ((_root_.List K) × (_root_.List V))))))))))))) | [] => .unmatch)


noncomputable def «$extend_map:case_1:pattern-iter:2_clauses» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$extend_map:case_1:pattern-iter:2:clause:0» K V input0), fun (_ : _root_.Unit) => («$extend_map:case_1:pattern-iter:2:clause:1» K V input0)]


noncomputable def «$extend_map:case_1:iter:4:clause:0» (K : Type) (V : Type) (input0 : (_root_.List K)) (input1 : (_root_.List V)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair K V))) : (_root_.List (pair K V))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$extend_map:case_1:iter:4:clause:1» (K : Type) (V : Type) (input0 : (_root_.List K)) (input1 : (_root_.List V)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let K_a : K := «exec:2»; (let «tail:0» : (_root_.List K) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let V_a : V := «exec:4»; (let «tail:1» : (_root_.List V) := «exec:3»; (.bind (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$extend_map:case_1:iter:4» K V «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair K V))) => (let «tail:2» : (_root_.List (pair K V)) := «exec:5»; (.pure (((((pair.«% ':' %» K_a V_a) : (pair K V)) :: «tail:2») : (_root_.List (pair K V)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$extend_map:case_1:iter:4_clauses» (K : Type) (V : Type) (input0 : (_root_.List K)) (input1 : (_root_.List V)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$extend_map:case_1:iter:4:clause:0» K V input0 input1), fun (_ : _root_.Unit) => («$extend_map:case_1:iter:4:clause:1» K V input0 input1)]


noncomputable def «$extend_map:case_1:pattern-iter:7:clause:0» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List K)), ([] : (_root_.List V))) : ((_root_.List K) × (_root_.List V))))) | _ :: _ => .unmatch)


noncomputable def «$extend_map:case_1:pattern-iter:7:clause:1» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let K_c : K := «exec:3»; (let V_c : V := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair K V)) := «exec:1»; (.bind (.call ⟨((_root_.List K) × (_root_.List V)), SpecTecCall.«$extend_map:case_1:pattern-iter:7» K V «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List K) × (_root_.List V))) => (let «pattern-tail:1» : (_root_.List K) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List V) := («exec:5»).2; (.pure ((((K_c :: «pattern-tail:1»), (V_c :: «pattern-tail:2»)) : ((_root_.List K) × (_root_.List V))))))))))))) | [] => .unmatch)


noncomputable def «$extend_map:case_1:pattern-iter:7_clauses» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$extend_map:case_1:pattern-iter:7:clause:0» K V input0), fun (_ : _root_.Unit) => («$extend_map:case_1:pattern-iter:7:clause:1» K V input0)]


noncomputable def «$extend_map:case_1:iter:9:clause:0» (K : Type) (V : Type) (input0 : (_root_.List K)) (input1 : (_root_.List V)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair K V))) : (_root_.List (pair K V))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)

end SpecTec
