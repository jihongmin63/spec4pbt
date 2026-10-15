import SpecTecDecl0238

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Cast_impl_neq:headerStackTypeIR:iter:3:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerStackTypeIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerStackTypeIR:iter:3» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:headerStackTypeIR:iter:3_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerStackTypeIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:headerStackTypeIR:iter:3:clause:1»  input0)]


noncomputable def «Cast_impl_neq:structTypeIR:iter:5:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR:iter:5:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:structTypeIR:iter:5» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR:iter:5_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR:iter:5:clause:1»  input0)]


noncomputable def «Cast_impl_neq:headerTypeIR_2:iter:5:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_2:iter:5:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerTypeIR_2:iter:5» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_2:iter:5_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_2:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_2:iter:5:clause:1»  input0)]


noncomputable def «Cast_impl_neq:sequenceTypeIR:iter:3:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:sequenceTypeIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:sequenceTypeIR:iter:3» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:sequenceTypeIR:iter:3_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:sequenceTypeIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:sequenceTypeIR:iter:3:clause:1»  input0)]


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:4:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:4:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:tupleTypeIR_2:iter:4» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:4_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:tupleTypeIR_2:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:tupleTypeIR_2:iter:4:clause:1»  input0)]


noncomputable def «Cast_impl_neq:arrayTypeIR_2:iter:3:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:arrayTypeIR_2:iter:3:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:arrayTypeIR_2:iter:3» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:arrayTypeIR_2:iter:3_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:arrayTypeIR_2:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:arrayTypeIR_2:iter:3:clause:1»  input0)]


noncomputable def «Cast_impl_neq:headerStackTypeIR_2:iter:3:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerStackTypeIR_2:iter:3:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerStackTypeIR_2:iter:3» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:headerStackTypeIR_2:iter:3_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerStackTypeIR_2:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:headerStackTypeIR_2:iter:3:clause:1»  input0)]


noncomputable def «Cast_impl_neq:structTypeIR_2:iter:6:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_2:iter:6:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:structTypeIR_2:iter:6» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_2:iter:6_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_2:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_2:iter:6:clause:1»  input0)]


noncomputable def «Cast_impl_neq:headerTypeIR_3:iter:6:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_3:iter:6:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerTypeIR_3:iter:6» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_3:iter:6_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_3:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_3:iter:6:clause:1»  input0)]


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:21:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:21:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:structTypeIR_3:iter:21» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:21_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_3:iter:21:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_3:iter:21:clause:1»  input0)]


noncomputable def «Cast_impl_neq:headerTypeIR_4:iter:21:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_4:iter:21:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerTypeIR_4:iter:21» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)

end SpecTec
