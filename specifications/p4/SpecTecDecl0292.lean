import SpecTecDecl0291

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Cast_expl_neq:tupleTypeIR:iter:2:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:tupleTypeIR:iter:2:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_b : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl typeIR_a typeIR_b⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_expl_neq:tupleTypeIR:iter:2» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:tupleTypeIR:iter:2_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:tupleTypeIR:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:tupleTypeIR:iter:2:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:arrayTypeIR:iter:2:clause:0» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_b : typeIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch))


noncomputable def «Cast_expl_neq:arrayTypeIR:iter:2:clause:1» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_b : typeIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl typeIR_a typeIR_b⟩) (fun («exec:3» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_expl_neq:arrayTypeIR:iter:2» typeIR_b «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.castResult)) => (let «tail:1» : (_root_.List SpecTec.castResult) := «exec:4»; (.pure (((castResult :: «tail:1») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))


noncomputable def «Cast_expl_neq:arrayTypeIR:iter:2_clauses» (input0 : typeIR) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:arrayTypeIR:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:arrayTypeIR:iter:2:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:headerStackTypeIR:iter:2:clause:0» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_b : typeIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch))


noncomputable def «Cast_expl_neq:headerStackTypeIR:iter:2:clause:1» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_b : typeIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl typeIR_a typeIR_b⟩) (fun («exec:3» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_expl_neq:headerStackTypeIR:iter:2» typeIR_b «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.castResult)) => (let «tail:1» : (_root_.List SpecTec.castResult) := «exec:4»; (.pure (((castResult :: «tail:1») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))


noncomputable def «Cast_expl_neq:headerStackTypeIR:iter:2_clauses» (input0 : typeIR) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerStackTypeIR:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:headerStackTypeIR:iter:2:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:structTypeIR:iter:4:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR:iter:4:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl typeIR_a typeIR_field_b⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_expl_neq:structTypeIR:iter:4» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR:iter:4_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR:iter:4:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:headerTypeIR_2:iter:4:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_2:iter:4:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl typeIR_a typeIR_field_b⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_expl_neq:headerTypeIR_2:iter:4» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_2:iter:4_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_2:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_2:iter:4:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:tupleTypeIR_2:iter:3:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:tupleTypeIR_2:iter:3:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_b_non_default : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl typeIR_a typeIR_b_non_default⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_expl_neq:tupleTypeIR_2:iter:3» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:tupleTypeIR_2:iter:3_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:tupleTypeIR_2:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:tupleTypeIR_2:iter:3:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:arrayTypeIR_2:iter:2:clause:0» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_b : typeIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch))


noncomputable def «Cast_expl_neq:arrayTypeIR_2:iter:2:clause:1» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_b : typeIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl typeIR_a typeIR_b⟩) (fun («exec:3» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_expl_neq:arrayTypeIR_2:iter:2» typeIR_b «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.castResult)) => (let «tail:1» : (_root_.List SpecTec.castResult) := «exec:4»; (.pure (((castResult :: «tail:1») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))


noncomputable def «Cast_expl_neq:arrayTypeIR_2:iter:2_clauses» (input0 : typeIR) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:arrayTypeIR_2:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:arrayTypeIR_2:iter:2:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:headerStackTypeIR_2:iter:2:clause:0» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_b : typeIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch))


noncomputable def «Cast_expl_neq:headerStackTypeIR_2:iter:2:clause:1» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_b : typeIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl typeIR_a typeIR_b⟩) (fun («exec:3» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_expl_neq:headerStackTypeIR_2:iter:2» typeIR_b «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.castResult)) => (let «tail:1» : (_root_.List SpecTec.castResult) := «exec:4»; (.pure (((castResult :: «tail:1») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))


noncomputable def «Cast_expl_neq:headerStackTypeIR_2:iter:2_clauses» (input0 : typeIR) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerStackTypeIR_2:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:headerStackTypeIR_2:iter:2:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:structTypeIR_2:iter:5:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_2:iter:5:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b_non_default : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl typeIR_a typeIR_field_b_non_default⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_expl_neq:structTypeIR_2:iter:5» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_2:iter:5_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_2:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_2:iter:5:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:headerTypeIR_3:iter:5:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_3:iter:5:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b_non_default : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl typeIR_a typeIR_field_b_non_default⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_expl_neq:headerTypeIR_3:iter:5» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_3:iter:5_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_3:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_3:iter:5:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:20:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:20:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field_a_aligned : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b_aligned : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl typeIR_field_a_aligned typeIR_field_b_aligned⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_expl_neq:structTypeIR_3:iter:20» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)

end SpecTec
