import SpecTecDecl0135

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$assoc_:clause:0» (X : Type) (Y : Type) (input0 : X) (input1 : (_root_.List (X × Y))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let key : X := input0; (match input1 with | [] => (.pure (((_root_.Option.none) : (_root_.Option Y)))) | _ :: _ => .unmatch))


noncomputable def «$assoc_:clause:1» (X : Type) (Y : Type) (input0 : X) (input1 : (_root_.List (X × Y))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let key : X := input0; (match input1 with | «exec:2» :: «exec:1» => (.bind (.guard ((«exec:2»).1 = key)) (fun (_ : Unit) => (let value : Y := («exec:2»).2; (let ps : (_root_.List (X × Y)) := «exec:1»; (.pure (((_root_.Option.some value) : (_root_.Option Y)))))))) | [] => .unmatch))


noncomputable def «$assoc_:clause:2» (X : Type) (Y : Type) (input0 : X) (input1 : (_root_.List (X × Y))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let key : X := input0; (match input1 with | «exec:2» :: «exec:1» => (let other : X := («exec:2»).1; (let value : Y := («exec:2»).2; (let ps : (_root_.List (X × Y)) := «exec:1»; (.bind (.guard ((other ≠ key))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.Option Y), SpecTecCall.«$assoc_» X Y key ps⟩) (fun («exec:3» : (_root_.Option Y)) => (let r : (_root_.Option Y) := «exec:3»; (.pure ((r : (_root_.Option Y)))))))))))) | [] => .unmatch))


noncomputable def «$assoc__clauses» (X : Type) (Y : Type) (input0 : X) (input1 : (_root_.List (X × Y))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$assoc_:clause:0» X Y input0 input1), fun (_ : _root_.Unit) => («$assoc_:clause:1» X Y input0 input1), fun (_ : _root_.Unit) => («$assoc_:clause:2» X Y input0 input1)]


noncomputable def «$distinct_:clause:0» (K : Type) (input0 : (_root_.List K)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let xs : (_root_.List K) := input0; (.orElse (let b : _root_.Bool := true; (.bind (.guard ((_root_.List.Nodup xs))) (fun (_ : Unit) => (.pure ((b : _root_.Bool)))))) (fun () => (let b : _root_.Bool := false; (.bind (.guard (¬ ((_root_.List.Nodup xs)))) (fun (_ : Unit) => (.pure ((b : _root_.Bool)))))))))


noncomputable def «$distinct__clauses» (K : Type) (input0 : (_root_.List K)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$distinct_:clause:0» K input0)]


noncomputable def «$empty_set:clause:0» (K : Type)  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.pure ((((set.«`{ % `}» ([] : (_root_.List K))) : (set K)) : (set K))))


noncomputable def «$empty_set_clauses» (K : Type) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_set:clause:0» K )]


noncomputable def «$in_set:clause:0» (K_T : Type) [_root_.DecidableEq K_T] (input0 : K_T) (input1 : (set K_T)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let K : K_T := input0; (match input1 with | .«`{ % `}» «exec:1» => (let «K_e*» : (_root_.List K_T) := «exec:1»; (.pure (((_root_.Decidable.decide (K ∈ «K_e*»)) : _root_.Bool))))))


noncomputable def «$in_set_clauses» (K_T : Type) [_root_.DecidableEq K_T] (input0 : K_T) (input1 : (set K_T)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$in_set:clause:0» K_T input0 input1)]


noncomputable def «$sub_set:clause:0» (K : Type) (input0 : (set K)) (input1 : (set K)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let xs : (_root_.List K) := «exec:1»; (match input1 with | .«`{ % `}» «exec:2» => (let ys : (_root_.List K) := «exec:2»; (.orElse (let b : _root_.Bool := true; (.bind (.guard ((∀ (x : K), ((x ∈ xs) → (x ∈ ys))))) (fun (_ : Unit) => (.pure ((b : _root_.Bool)))))) (fun () => (let b : _root_.Bool := false; (.bind (.guard (¬ ((∀ (x : K), ((x ∈ xs) → (x ∈ ys)))))) (fun (_ : Unit) => (.pure ((b : _root_.Bool))))))))))))


noncomputable def «$sub_set_clauses» (K : Type) (input0 : (set K)) (input1 : (set K)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sub_set:clause:0» K input0 input1)]


noncomputable def «$eq_set:clause:0» (K : Type) (input0 : (set K)) (input1 : (set K)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let xs : (_root_.List K) := «exec:1»; (match input1 with | .«`{ % `}» «exec:2» => (let ys : (_root_.List K) := «exec:2»; (.orElse (let b : _root_.Bool := true; (.bind (.guard (((∀ (x : K), ((x ∈ xs) → (x ∈ ys))) ∧ (∀ (x : K), ((x ∈ ys) → (x ∈ xs)))))) (fun (_ : Unit) => (.pure ((b : _root_.Bool)))))) (fun () => (let b : _root_.Bool := false; (.bind (.guard (¬ (((∀ (x : K), ((x ∈ xs) → (x ∈ ys))) ∧ (∀ (x : K), ((x ∈ ys) → (x ∈ xs))))))) (fun (_ : Unit) => (.pure ((b : _root_.Bool))))))))))))


noncomputable def «$eq_set_clauses» (K : Type) (input0 : (set K)) (input1 : (set K)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$eq_set:clause:0» K input0 input1)]


noncomputable def «$empty_map:clause:0» (K : Type) (V : Type)  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.pure ((((set.«`{ % `}» ([] : (_root_.List (pair K V)))) : (set (pair K V))) : (map K V))))


noncomputable def «$empty_map_clauses» (K : Type) (V : Type) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_map:clause:0» K V )]


noncomputable def «$dom_map:case_1:pattern-iter:0:clause:0» (K_T : Type) (V_T : Type) (input0 : (_root_.List (pair K_T V_T))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List K_T)), ([] : (_root_.List V_T))) : ((_root_.List K_T) × (_root_.List V_T))))) | _ :: _ => .unmatch)


noncomputable def «$dom_map:case_1:pattern-iter:0:clause:1» (K_T : Type) (V_T : Type) (input0 : (_root_.List (pair K_T V_T))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let K : K_T := «exec:3»; (let V : V_T := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair K_T V_T)) := «exec:1»; (.bind (.call ⟨((_root_.List K_T) × (_root_.List V_T)), SpecTecCall.«$dom_map:case_1:pattern-iter:0» K_T V_T «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List K_T) × (_root_.List V_T))) => (let «pattern-tail:1» : (_root_.List K_T) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List V_T) := («exec:5»).2; (.pure ((((K :: «pattern-tail:1»), (V :: «pattern-tail:2»)) : ((_root_.List K_T) × (_root_.List V_T))))))))))))) | [] => .unmatch)


noncomputable def «$dom_map:case_1:pattern-iter:0_clauses» (K_T : Type) (V_T : Type) (input0 : (_root_.List (pair K_T V_T))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$dom_map:case_1:pattern-iter:0:clause:0» K_T V_T input0), fun (_ : _root_.Unit) => («$dom_map:case_1:pattern-iter:0:clause:1» K_T V_T input0)]


noncomputable def «$dom_map:clause:0» (K_T : Type) (V_T : Type) (input0 : (map K_T V_T)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «eval:1» : (_root_.List (pair K_T V_T)) := «exec:1»; (.bind (.call ⟨((_root_.List K_T) × (_root_.List V_T)), SpecTecCall.«$dom_map:case_1:pattern-iter:0» K_T V_T «eval:1»⟩) (fun («exec:2» : ((_root_.List K_T) × (_root_.List V_T))) => (let «K*» : (_root_.List K_T) := («exec:2»).1; (let «V*» : (_root_.List V_T) := («exec:2»).2; (.pure ((((set.«`{ % `}» «K*») : (set K_T)) : (set K_T))))))))))


noncomputable def «$dom_map_clauses» (K_T : Type) (V_T : Type) (input0 : (map K_T V_T)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$dom_map:clause:0» K_T V_T input0)]


noncomputable def «$codom_map:case_1:pattern-iter:0:clause:0» (K_T : Type) (V_T : Type) (input0 : (_root_.List (pair K_T V_T))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List K_T)), ([] : (_root_.List V_T))) : ((_root_.List K_T) × (_root_.List V_T))))) | _ :: _ => .unmatch)


noncomputable def «$codom_map:case_1:pattern-iter:0:clause:1» (K_T : Type) (V_T : Type) (input0 : (_root_.List (pair K_T V_T))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let K : K_T := «exec:3»; (let V : V_T := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair K_T V_T)) := «exec:1»; (.bind (.call ⟨((_root_.List K_T) × (_root_.List V_T)), SpecTecCall.«$codom_map:case_1:pattern-iter:0» K_T V_T «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List K_T) × (_root_.List V_T))) => (let «pattern-tail:1» : (_root_.List K_T) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List V_T) := («exec:5»).2; (.pure ((((K :: «pattern-tail:1»), (V :: «pattern-tail:2»)) : ((_root_.List K_T) × (_root_.List V_T))))))))))))) | [] => .unmatch)


noncomputable def «$codom_map:case_1:pattern-iter:0_clauses» (K_T : Type) (V_T : Type) (input0 : (_root_.List (pair K_T V_T))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$codom_map:case_1:pattern-iter:0:clause:0» K_T V_T input0), fun (_ : _root_.Unit) => («$codom_map:case_1:pattern-iter:0:clause:1» K_T V_T input0)]


noncomputable def «$codom_map:clause:0» (K_T : Type) (V_T : Type) (input0 : (map K_T V_T)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «eval:1» : (_root_.List (pair K_T V_T)) := «exec:1»; (.bind (.call ⟨((_root_.List K_T) × (_root_.List V_T)), SpecTecCall.«$codom_map:case_1:pattern-iter:0» K_T V_T «eval:1»⟩) (fun («exec:2» : ((_root_.List K_T) × (_root_.List V_T))) => (let «K*» : (_root_.List K_T) := («exec:2»).1; (let «V*» : (_root_.List V_T) := («exec:2»).2; (.pure ((((set.«`{ % `}» «V*») : (set V_T)) : (set V_T))))))))))


noncomputable def «$codom_map_clauses» (K_T : Type) (V_T : Type) (input0 : (map K_T V_T)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$codom_map:clause:0» K_T V_T input0)]


noncomputable def «$find_map:list:clause:0» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (let k : K := input1; (.pure (((_root_.Option.none) : (_root_.Option V))))) | _ :: _ => .unmatch)


noncomputable def «$find_map:list:clause:1» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let k : K := «exec:3»; (let v : V := «exec:4»; (let ps : (_root_.List (pair K V)) := «exec:1»; (.bind (.guard (input1 = k)) (fun (_ : Unit) => (.pure (((_root_.Option.some v) : (_root_.Option V)))))))))) | [] => .unmatch)


noncomputable def «$find_map:list:clause:2» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let k' : K := «exec:3»; (let v : V := «exec:4»; (let ps : (_root_.List (pair K V)) := «exec:1»; (let k : K := input1; (.bind (.guard ((k' ≠ k))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.Option V), SpecTecCall.«$find_map:list» K V ps k⟩) (fun («exec:5» : (_root_.Option V)) => (let r : (_root_.Option V) := «exec:5»; (.pure ((r : (_root_.Option V)))))))))))))) | [] => .unmatch)


noncomputable def «$find_map:list_clauses» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_map:list:clause:0» K V input0 input1), fun (_ : _root_.Unit) => («$find_map:list:clause:1» K V input0 input1), fun (_ : _root_.Unit) => («$find_map:list:clause:2» K V input0 input1)]


noncomputable def «$find_map:clause:0» (K : Type) (V : Type) (input0 : (map K V)) (input1 : K) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let ps : (_root_.List (pair K V)) := «exec:1»; (let k : K := input1; (.bind (.call ⟨(_root_.Option V), SpecTecCall.«$find_map:list» K V ps k⟩) (fun («exec:2» : (_root_.Option V)) => (let r : (_root_.Option V) := «exec:2»; (.pure ((r : (_root_.Option V))))))))))


noncomputable def «$find_map_clauses» (K : Type) (V : Type) (input0 : (map K V)) (input1 : K) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_map:clause:0» K V input0 input1)]

end SpecTec
