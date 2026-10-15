import SpecTecDecl0178

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$nestable_set:clause:9» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«SEQ `< % `>» «exec:1» => (let «typeIR*» : (_root_.List typeIR) := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_set:matches:9:row» ((typeIR.«SEQ `< % `>» «typeIR*») : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_set:row_9:iter:0» «typeIR*»⟩) (fun («exec:2» : (_root_.List _root_.Bool)) => (let «eval:2» : (_root_.List _root_.Bool) := «exec:2»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$forall_» «eval:2»⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.pure ((«eval:3» : _root_.Bool)))))))))))) | _ => .unmatch)


noncomputable def «$nestable_set:clause:10» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_set:matches:10:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_set_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_set:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_set:clause:1»  input0), fun (_ : _root_.Unit) => («$nestable_set:clause:2»  input0), fun (_ : _root_.Unit) => («$nestable_set:clause:3»  input0), fun (_ : _root_.Unit) => («$nestable_set:clause:4»  input0), fun (_ : _root_.Unit) => («$nestable_set:clause:5»  input0), fun (_ : _root_.Unit) => («$nestable_set:clause:6»  input0), fun (_ : _root_.Unit) => («$nestable_set:clause:7»  input0), fun (_ : _root_.Unit) => («$nestable_set:clause:8»  input0), fun (_ : _root_.Unit) => («$nestable_set:clause:9»  input0), fun (_ : _root_.Unit) => («$nestable_set:clause:10»  input0)]


noncomputable def «$nestable_action:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_action:matches:0:row» ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_action:clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_action:matches:1:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_action» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_action:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_action:matches:2:row» objectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_action:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let synthesizedTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_action:matches:3:row» synthesizedTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_action:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_action:matches:4:row» _typeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_action_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_action:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_action:clause:1»  input0), fun (_ : _root_.Unit) => («$nestable_action:clause:2»  input0), fun (_ : _root_.Unit) => («$nestable_action:clause:3»  input0), fun (_ : _root_.Unit) => («$nestable_action:clause:4»  input0)]


noncomputable def «CallableType_wf:actionTypeIR:iter:6:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «CallableType_wf:actionTypeIR:iter:6:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_action» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:7» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:7» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:actionTypeIR:iter:6» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch)


noncomputable def «CallableType_wf:actionTypeIR:iter:6_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:actionTypeIR:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_wf:actionTypeIR:iter:6:clause:1»  input0)]


noncomputable def «$nestable_definedFunction:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_definedFunction:matches:0:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_definedFunction» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_definedFunction:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_definedFunction:matches:1:row» objectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_definedFunction:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let synthesizedTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_definedFunction:matches:2:row» synthesizedTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_definedFunction:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_definedFunction:matches:3:row» _typeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_definedFunction_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_definedFunction:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_definedFunction:clause:1»  input0), fun (_ : _root_.Unit) => («$nestable_definedFunction:clause:2»  input0), fun (_ : _root_.Unit) => («$nestable_definedFunction:clause:3»  input0)]


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:5:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:5:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_definedFunction» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:6» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:6» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:definedFunctionTypeIR:iter:5» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch)


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:5_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:definedFunctionTypeIR:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_wf:definedFunctionTypeIR:iter:5:clause:1»  input0)]


noncomputable def «$nestable_externFunction:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_externFunction:matches:0:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_externFunction» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_externFunction:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_externFunction:matches:1:row» parserObjectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_externFunction:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_externFunction:matches:2:row» controlObjectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_externFunction:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let packageObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_externFunction:matches:3:row» packageObjectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_externFunction:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_externFunction:matches:4:row» tableObjectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_externFunction:clause:5» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_externFunction:matches:5:row» _typeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_externFunction_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_externFunction:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_externFunction:clause:1»  input0), fun (_ : _root_.Unit) => («$nestable_externFunction:clause:2»  input0), fun (_ : _root_.Unit) => («$nestable_externFunction:clause:3»  input0), fun (_ : _root_.Unit) => («$nestable_externFunction:clause:4»  input0), fun (_ : _root_.Unit) => («$nestable_externFunction:clause:5»  input0)]


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:3:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_externFunction» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:4» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:4» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:externFunctionTypeIR:iter:3» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch)


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:3_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:externFunctionTypeIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_wf:externFunctionTypeIR:iter:3:clause:1»  input0)]


noncomputable def «$nestable_externMethod:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_externMethod:matches:0:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_externMethod» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_externMethod:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_externMethod:matches:1:row» parserObjectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))

end SpecTec
