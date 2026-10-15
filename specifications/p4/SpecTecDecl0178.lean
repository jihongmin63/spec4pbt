import SpecTecDecl0177

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$nestable_set:row_7:iter:0:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$nestable_set:row_7:iter:0:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_tuple_in_set» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_set:row_7:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:1» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$nestable_set:row_7:iter:0_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_set:row_7:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_set:row_7:iter:0:clause:1»  input0)]


noncomputable def «$nestable_sequence_in_set:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_sequence_in_set:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_sequence_in_set:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_sequence_in_set:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_sequence_in_set:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_sequence_in_set:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_sequence_in_set:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_sequence_in_set:matches:3:row» nameTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_sequence_in_set:clause:4» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_sequence_in_set:matches:4:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_sequence_in_set» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_sequence_in_set:clause:5» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let newTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_sequence_in_set:matches:5:row» newTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_sequence_in_set:clause:6» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«TUPLE `< % `>» «exec:1» => (let «typeIR*» : (_root_.List typeIR) := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_sequence_in_set:matches:6:row» ((typeIR.«TUPLE `< % `>» «typeIR*») : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_sequence_in_set:row_6:iter:0» «typeIR*»⟩) (fun («exec:2» : (_root_.List _root_.Bool)) => (let «eval:2» : (_root_.List _root_.Bool) := «exec:2»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$forall_» «eval:2»⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.pure ((«eval:3» : _root_.Bool)))))))))))) | _ => .unmatch)


noncomputable def «$nestable_sequence_in_set:clause:7» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let enumTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_sequence_in_set:matches:7:row» enumTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_sequence_in_set:clause:8» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«SEQ `< % `>» «exec:1» => (let «typeIR*» : (_root_.List typeIR) := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_sequence_in_set:matches:8:row» ((typeIR.«SEQ `< % `>» «typeIR*») : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_sequence_in_set:row_8:iter:0» «typeIR*»⟩) (fun («exec:2» : (_root_.List _root_.Bool)) => (let «eval:2» : (_root_.List _root_.Bool) := «exec:2»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$forall_» «eval:2»⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.pure ((«eval:3» : _root_.Bool)))))))))))) | _ => .unmatch)


noncomputable def «$nestable_sequence_in_set:clause:9» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_sequence_in_set:matches:9:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_sequence_in_set_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_sequence_in_set:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_sequence_in_set:clause:1»  input0), fun (_ : _root_.Unit) => («$nestable_sequence_in_set:clause:2»  input0), fun (_ : _root_.Unit) => («$nestable_sequence_in_set:clause:3»  input0), fun (_ : _root_.Unit) => («$nestable_sequence_in_set:clause:4»  input0), fun (_ : _root_.Unit) => («$nestable_sequence_in_set:clause:5»  input0), fun (_ : _root_.Unit) => («$nestable_sequence_in_set:clause:6»  input0), fun (_ : _root_.Unit) => («$nestable_sequence_in_set:clause:7»  input0), fun (_ : _root_.Unit) => («$nestable_sequence_in_set:clause:8»  input0), fun (_ : _root_.Unit) => («$nestable_sequence_in_set:clause:9»  input0)]


noncomputable def «$nestable_sequence_in_set:row_6:iter:0:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$nestable_sequence_in_set:row_6:iter:0:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_sequence_in_set» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_sequence_in_set:row_6:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:1» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$nestable_sequence_in_set:row_6:iter:0_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_sequence_in_set:row_6:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_sequence_in_set:row_6:iter:0:clause:1»  input0)]


noncomputable def «$nestable_sequence_in_set:row_8:iter:0:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$nestable_sequence_in_set:row_8:iter:0:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_sequence_in_set» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_sequence_in_set:row_8:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:1» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$nestable_sequence_in_set:row_8:iter:0_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_sequence_in_set:row_8:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_sequence_in_set:row_8:iter:0:clause:1»  input0)]


noncomputable def «$nestable_set:row_9:iter:0:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$nestable_set:row_9:iter:0:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_sequence_in_set» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_set:row_9:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:1» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$nestable_set:row_9:iter:0_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_set:row_9:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_set:row_9:iter:0:clause:1»  input0)]


noncomputable def «$nestable_set:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_set:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_set:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .ERROR  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_set:matches:1:row» ((typeIR.ERROR) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_set:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_set:matches:2:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_set:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_set:matches:3:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_set:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_set:matches:4:row» nameTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_set:clause:5» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_set:matches:5:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_set» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_set:clause:6» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let newTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_set:matches:6:row» newTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_set:clause:7» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«TUPLE `< % `>» «exec:1» => (let «typeIR*» : (_root_.List typeIR) := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_set:matches:7:row» ((typeIR.«TUPLE `< % `>» «typeIR*») : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_set:row_7:iter:0» «typeIR*»⟩) (fun («exec:2» : (_root_.List _root_.Bool)) => (let «eval:2» : (_root_.List _root_.Bool) := «exec:2»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$forall_» «eval:2»⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.pure ((«eval:3» : _root_.Bool)))))))))))) | _ => .unmatch)


noncomputable def «$nestable_set:clause:8» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let enumTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_set:matches:8:row» enumTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))

end SpecTec
