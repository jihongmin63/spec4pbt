import SpecTecDecl0134

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$strip_suffix_rec:clause:1» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let t_suffix : _root_.String := input1; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$ends_with» t t_suffix⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.pure ((t : _root_.String))))))))))


noncomputable def «$strip_suffix_rec_clauses» (input0 : _root_.String) (input1 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$strip_suffix_rec:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$strip_suffix_rec:clause:1»  input0 input1)]


noncomputable def «$contains':clause:0» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n_len : _root_.Nat := input0; (let n_len' : _root_.Nat := input1; (let t : _root_.String := input2; (let t_c : _root_.String := input3; (.bind (.guard (n_len' = n_len)) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))))


noncomputable def «$contains':clause:1» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n : _root_.Nat := input0; (let n_len : _root_.Nat := input1; (let t : _root_.String := input2; (let t_c : _root_.String := input3; (.bind (.guard ((n < n_len))) (fun (_ : Unit) => (.bind (.guard ((n < (_root_.String.utf8ByteSize t)))) (fun (_ : Unit) => (.bind (SpecTecExecution.require (((n + (1 : _root_.Nat)) ≤ (_root_.String.utf8ByteSize t))) "slice out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextSliceValid t n (1 : _root_.Nat))) "text result is not valid UTF-8") (fun (_ : Unit) => (.bind (.guard (t_c = (_root_.specTecTextSlice t n (1 : _root_.Nat)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))))))))))))


noncomputable def «$contains':clause:2» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n : _root_.Nat := input0; (let n_len : _root_.Nat := input1; (let t : _root_.String := input2; (let t_c : _root_.String := input3; (.bind (.guard ((n < n_len))) (fun (_ : Unit) => (.bind (.guard ((n < (_root_.String.utf8ByteSize t)))) (fun (_ : Unit) => (.bind (SpecTecExecution.require (((n + (1 : _root_.Nat)) ≤ (_root_.String.utf8ByteSize t))) "slice out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextSliceValid t n (1 : _root_.Nat))) "text result is not valid UTF-8") (fun (_ : Unit) => (.bind (.guard (((_root_.specTecTextSlice t n (1 : _root_.Nat)) ≠ t_c))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$contains'» (n + (1 : _root_.Nat)) n_len t t_c⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((«eval:0» : _root_.Bool))))))))))))))))))))


noncomputable def «$contains'_clauses» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$contains':clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$contains':clause:1»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$contains':clause:2»  input0 input1 input2 input3)]


noncomputable def «$contains:clause:0» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let t_c : _root_.String := input1; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$contains'» (0 : _root_.Nat) (_root_.String.utf8ByteSize t) t t_c⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((«eval:0» : _root_.Bool))))))))


noncomputable def «$contains_clauses» (input0 : _root_.String) (input1 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$contains:clause:0»  input0 input1)]


noncomputable def «$is_some_:clause:0» (X_T : Type) (input0 : (_root_.Option X_T)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let X? : (_root_.Option X_T) := input0; (.bind (.guard (((_root_.Option.isNone X?) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_some_:clause:1» (X_T : Type) (input0 : (_root_.Option X_T)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let X'? : (_root_.Option X_T) := input0; (.bind (.guard (((_root_.Option.isSome X'?) = true))) (fun (_ : Unit) => (match X'? with | some «exec:1» => (let X : X_T := «exec:1»; (.pure ((true : _root_.Bool)))) | none => .unmatch))))


noncomputable def «$is_some__clauses» (X_T : Type) (input0 : (_root_.Option X_T)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_some_:clause:0» X_T input0), fun (_ : _root_.Unit) => («$is_some_:clause:1» X_T input0)]


noncomputable def «$opt_as_seq_:clause:0» (X_T : Type) (input0 : (_root_.Option X_T)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let X? : (_root_.Option X_T) := input0; (.bind (.guard (((_root_.Option.isNone X?) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List X_T)) : (_root_.List X_T)))))))


noncomputable def «$opt_as_seq_:clause:1» (X_T : Type) (input0 : (_root_.Option X_T)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let X'? : (_root_.Option X_T) := input0; (.bind (.guard (((_root_.Option.isSome X'?) = true))) (fun (_ : Unit) => (match X'? with | some «exec:1» => (let X : X_T := «exec:1»; (.pure ((([X] : (_root_.List X_T)) : (_root_.List X_T))))) | none => .unmatch))))


noncomputable def «$opt_as_seq__clauses» (X_T : Type) (input0 : (_root_.Option X_T)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$opt_as_seq_:clause:0» X_T input0), fun (_ : _root_.Unit) => («$opt_as_seq_:clause:1» X_T input0)]


noncomputable def «$exists_:clause:0» (input0 : (_root_.List _root_.Bool)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «b*» : (_root_.List _root_.Bool) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «b*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$exists_:clause:1» (input0 : (_root_.List _root_.Bool)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «b*» : (_root_.List _root_.Bool) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «b*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «b*» with | «exec:2» :: «exec:1» => (let b_h : _root_.Bool := «exec:2»; (let «b_t*» : (_root_.List _root_.Bool) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$exists_» «b_t*»⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure (((b_h || «eval:0») : _root_.Bool)))))))) | [] => .unmatch))))


noncomputable def «$exists__clauses» (input0 : (_root_.List _root_.Bool)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$exists_:clause:0»  input0), fun (_ : _root_.Unit) => («$exists_:clause:1»  input0)]


noncomputable def «$forall_:clause:0» (input0 : (_root_.List _root_.Bool)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «b*» : (_root_.List _root_.Bool) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «b*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$forall_:clause:1» (input0 : (_root_.List _root_.Bool)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «b*» : (_root_.List _root_.Bool) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «b*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «b*» with | «exec:2» :: «exec:1» => (let b_h : _root_.Bool := «exec:2»; (let «b_t*» : (_root_.List _root_.Bool) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$forall_» «b_t*»⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure (((b_h && «eval:0») : _root_.Bool)))))))) | [] => .unmatch))))


noncomputable def «$forall__clauses» (input0 : (_root_.List _root_.Bool)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$forall_:clause:0»  input0), fun (_ : _root_.Unit) => («$forall_:clause:1»  input0)]


noncomputable def «$init_:clause:0» (input0 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nat : _root_.Nat := input0; (.bind (.guard ((0 : _root_.Nat) = nat)) (fun (_ : Unit) => (.pure ((([] : (_root_.List _root_.Nat)) : (_root_.List _root_.Nat)))))))


noncomputable def «$init_:clause:1» (input0 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n : _root_.Nat := input0; (.bind (.guard ((n ≠ (0 : _root_.Nat)))) (fun (_ : Unit) => (let i : _root_.Int := ((_root_.Int.ofNat n) - (_root_.Int.ofNat (1 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let n' : _root_.Nat := (_root_.Int.toNat i); (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$init_» n'⟩) (fun («exec:1» : (_root_.List _root_.Nat)) => (let «eval:0» : (_root_.List _root_.Nat) := «exec:1»; (.pure (((n' :: «eval:0») : (_root_.List _root_.Nat))))))))))))))))


noncomputable def «$init__clauses» (input0 : _root_.Nat) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$init_:clause:0»  input0), fun (_ : _root_.Unit) => («$init_:clause:1»  input0)]


noncomputable def «$repeat_:clause:0» (X_T : Type) (input0 : X_T) (input1 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let X : X_T := input0; (let nat : _root_.Nat := input1; (.bind (.guard ((0 : _root_.Nat) = nat)) (fun (_ : Unit) => (.pure ((([] : (_root_.List X_T)) : (_root_.List X_T))))))))


noncomputable def «$repeat_:clause:1» (X_T : Type) (input0 : X_T) (input1 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let X : X_T := input0; (let n : _root_.Nat := input1; (.bind (.guard ((n ≠ (0 : _root_.Nat)))) (fun (_ : Unit) => (let i : _root_.Int := ((_root_.Int.ofNat n) - (_root_.Int.ofNat (1 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let n' : _root_.Nat := (_root_.Int.toNat i); (.bind (.call ⟨(_root_.List X_T), SpecTecCall.«$repeat_» X_T X n'⟩) (fun («exec:1» : (_root_.List X_T)) => (let «eval:0» : (_root_.List X_T) := «exec:1»; (.pure (((([X] : (_root_.List X_T)) ++ «eval:0») : (_root_.List X_T)))))))))))))))))


noncomputable def «$repeat__clauses» (X_T : Type) (input0 : X_T) (input1 : _root_.Nat) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$repeat_:clause:0» X_T input0 input1), fun (_ : _root_.Unit) => («$repeat_:clause:1» X_T input0 input1)]


noncomputable def «$partition_:clause:0» (X : Type) (input0 : (_root_.List X)) (input1 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let xs : (_root_.List X) := input0; (let n : _root_.Nat := input1; (.bind (.guard ((n ≤ (4611686018427387903 : _root_.Nat)))) (fun (_ : Unit) => (.pure ((((_root_.List.take n xs), (_root_.List.drop n xs)) : ((_root_.List X) × (_root_.List X)))))))))


noncomputable def «$partition__clauses» (X : Type) (input0 : (_root_.List X)) (input1 : _root_.Nat) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$partition_:clause:0» X input0 input1), fun (_ : _root_.Unit) => .abort "builtin $partition_ failed"]


noncomputable def «$filter_:clause:0» (X : Type) (input0 : (_root_.List X)) (input1 : (_root_.List _root_.Bool)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «X*» : (_root_.List X) := input0; (let «b*» : (_root_.List _root_.Bool) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «X*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «b*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List X)) : (_root_.List X))))))))))


noncomputable def «$filter_:clause:1» (X : Type) (input0 : (_root_.List X)) (input1 : (_root_.List _root_.Bool)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «X*» : (_root_.List X) := input0; (let «b*» : (_root_.List _root_.Bool) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «X*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «X*» with | «exec:2» :: «exec:1» => (let X_h : X := «exec:2»; (let «X_t*» : (_root_.List X) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «b*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «b*» with | «exec:4» :: «exec:3» => (let b_h : _root_.Bool := «exec:4»; (let «b_t*» : (_root_.List _root_.Bool) := «exec:3»; (.bind (.guard ((b_h = true))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List X), SpecTecCall.«$filter_» X «X_t*» «b_t*»⟩) (fun («exec:5» : (_root_.List X)) => (let «eval:0» : (_root_.List X) := «exec:5»; (.pure (((X_h :: «eval:0») : (_root_.List X))))))))))) | [] => .unmatch))))) | [] => .unmatch)))))


noncomputable def «$filter_:clause:2» (X : Type) (input0 : (_root_.List X)) (input1 : (_root_.List _root_.Bool)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «X*» : (_root_.List X) := input0; (let «b*» : (_root_.List _root_.Bool) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «X*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «X*» with | «exec:2» :: «exec:1» => (let X_h : X := «exec:2»; (let «X_t*» : (_root_.List X) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «b*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «b*» with | «exec:4» :: «exec:3» => (let b_h : _root_.Bool := «exec:4»; (let «b_t*» : (_root_.List _root_.Bool) := «exec:3»; (.bind (.guard ((¬ (b_h = true)))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List X), SpecTecCall.«$filter_» X «X_t*» «b_t*»⟩) (fun («exec:5» : (_root_.List X)) => (let «eval:0» : (_root_.List X) := «exec:5»; (.pure ((«eval:0» : (_root_.List X))))))))))) | [] => .unmatch))))) | [] => .unmatch)))))


noncomputable def «$filter__clauses» (X : Type) (input0 : (_root_.List X)) (input1 : (_root_.List _root_.Bool)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$filter_:clause:0» X input0 input1), fun (_ : _root_.Unit) => («$filter_:clause:1» X input0 input1), fun (_ : _root_.Unit) => («$filter_:clause:2» X input0 input1)]

end SpecTec
