import SpecTecDecl0289

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Cast_impl_neq:arrayTypeIR_2:iter:2:clause:1» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_b : typeIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_impl typeIR_a typeIR_b⟩) (fun («exec:3» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_impl_neq:arrayTypeIR_2:iter:2» typeIR_b «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.castResult)) => (let «tail:1» : (_root_.List SpecTec.castResult) := «exec:4»; (.pure (((castResult :: «tail:1») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))


noncomputable def «Cast_impl_neq:arrayTypeIR_2:iter:2_clauses» (input0 : typeIR) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:arrayTypeIR_2:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_impl_neq:arrayTypeIR_2:iter:2:clause:1»  input0 input1)]


noncomputable def «Cast_impl_neq:headerStackTypeIR_2:iter:2:clause:0» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_b : typeIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch))


noncomputable def «Cast_impl_neq:headerStackTypeIR_2:iter:2:clause:1» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_b : typeIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_impl typeIR_a typeIR_b⟩) (fun («exec:3» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_impl_neq:headerStackTypeIR_2:iter:2» typeIR_b «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.castResult)) => (let «tail:1» : (_root_.List SpecTec.castResult) := «exec:4»; (.pure (((castResult :: «tail:1») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))


noncomputable def «Cast_impl_neq:headerStackTypeIR_2:iter:2_clauses» (input0 : typeIR) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerStackTypeIR_2:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_impl_neq:headerStackTypeIR_2:iter:2:clause:1»  input0 input1)]


noncomputable def «Cast_impl_neq:structTypeIR_2:iter:5:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_2:iter:5:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b_non_default : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_impl typeIR_a typeIR_field_b_non_default⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_impl_neq:structTypeIR_2:iter:5» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_2:iter:5_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_2:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_2:iter:5:clause:1»  input0 input1)]


noncomputable def «Cast_impl_neq:headerTypeIR_3:iter:5:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_3:iter:5:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b_non_default : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_impl typeIR_a typeIR_field_b_non_default⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_impl_neq:headerTypeIR_3:iter:5» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_3:iter:5_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_3:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_3:iter:5:clause:1»  input0 input1)]


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:20:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:20:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field_a_aligned : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b_aligned : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_impl typeIR_field_a_aligned typeIR_field_b_aligned⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_impl_neq:structTypeIR_3:iter:20» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:20_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_3:iter:20:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_3:iter:20:clause:1»  input0 input1)]


noncomputable def «Cast_impl_neq:headerTypeIR_4:iter:20:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_4:iter:20:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field_a_aligned : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b_aligned : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_impl typeIR_field_a_aligned typeIR_field_b_aligned⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_impl_neq:headerTypeIR_4:iter:20» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_4:iter:20_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_4:iter:20:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_4:iter:20:clause:1»  input0 input1)]


noncomputable def «Cast_impl_neq:structTypeIR_4:iter:20:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_4:iter:20:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field_a_aligned : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b_non_default_aligned : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_impl typeIR_field_a_aligned typeIR_field_b_non_default_aligned⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_impl_neq:structTypeIR_4:iter:20» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_4:iter:20_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_4:iter:20:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_4:iter:20:clause:1»  input0 input1)]


noncomputable def «Cast_impl_neq:headerTypeIR_5:iter:20:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List castResult)) : (_root_.List castResult)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_5:iter:20:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field_a_aligned : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b_non_default_aligned : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_impl typeIR_field_a_aligned typeIR_field_b_non_default_aligned⟩) (fun («exec:5» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:5»; (.bind (.call ⟨(_root_.List SpecTec.castResult), SpecTecCall.«Cast_impl_neq:headerTypeIR_5:iter:20» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.castResult)) => (let «tail:2» : (_root_.List SpecTec.castResult) := «exec:6»; (.pure (((castResult :: «tail:2») : (_root_.List SpecTec.castResult)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_5:iter:20_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_5:iter:20:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_5:iter:20:clause:1»  input0 input1)]


noncomputable def «Cast_expl:clause:0» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_a : typeIR := input0; (let typeIR_b : typeIR := input1; (.bind (.call ⟨typeIR, SpecTecCall.«$unroll_typeIR» typeIR_a⟩) (fun («exec:1» : typeIR) => (let «eval:0» : typeIR := «exec:1»; (let typeIR_a_unroll : typeIR := «eval:0»; (.bind (.call ⟨typeIR, SpecTecCall.«$unroll_typeIR» typeIR_b⟩) (fun («exec:2» : typeIR) => (let «eval:1» : typeIR := «exec:2»; (let typeIR_b_unroll : typeIR := «eval:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_alpha typeIR_a_unroll typeIR_b_unroll⟩) (fun («exec:3» : _root_.Unit) => (.pure ((((castResult.OK ([typeIR_b] : (_root_.List typeIR))) : castResult) : castResult)))))))))))))))


noncomputable def «Cast_expl:clause:1» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_a : typeIR := input0; (let typeIR_b : typeIR := input1; (.bind (.call ⟨typeIR, SpecTecCall.«$unroll_typeIR» typeIR_a⟩) (fun («exec:1» : typeIR) => (let «eval:0» : typeIR := «exec:1»; (let typeIR_a_unroll : typeIR := «eval:0»; (.bind (.call ⟨typeIR, SpecTecCall.«$unroll_typeIR» typeIR_b⟩) (fun («exec:2» : typeIR) => (let «eval:1» : typeIR := «exec:2»; (let typeIR_b_unroll : typeIR := «eval:1»; (.bind (.notHold (.call ⟨_root_.Unit, SpecTecCall.Type_alpha typeIR_a_unroll typeIR_b_unroll⟩)) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.castResult, SpecTecCall.Cast_expl_neq typeIR_a_unroll typeIR_b_unroll⟩) (fun («exec:3» : SpecTec.castResult) => (let castResult : SpecTec.castResult := «exec:3»; (.pure ((castResult : SpecTec.castResult))))))))))))))))))


noncomputable def Cast_expl_clauses (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:clause:0» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let typeIR' : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:boolTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («Cast_expl_neq:boolean-fixBit:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.boolTypeIR := «exec:1»; (let boolTypeIR : SpecTec.boolTypeIR := «eval:0»; (.bind (.guard (((SpecTec.boolTypeIR.BOOL) : SpecTec.boolTypeIR) = boolTypeIR)) (fun (_ : Unit) => (.bind (.guard (((SpecTec.typeIR.«BIT `< % `>» (1 : _root_.Nat)) : SpecTec.typeIR) = typeIR')) (fun (_ : Unit) => (.pure ((((castResult.OK ([((SpecTec.typeIR.«BIT `< % `>» (1 : _root_.Nat)) : SpecTec.typeIR)] : (_root_.List SpecTec.typeIR))) : castResult) : castResult))))))))) | none => .unmatch)))))


noncomputable def «Cast_expl_neq:clause:1» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:intTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Cast_expl_neq:boolean:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : SpecTec.intTypeIR := «exec:1»; (let intTypeIR : SpecTec.intTypeIR := «eval:0»; (.bind (.guard (((SpecTec.intTypeIR.INT) : SpecTec.intTypeIR) = intTypeIR)) (fun (_ : Unit) => (.bind (.guard (((SpecTec.typeIR.BOOL) : SpecTec.typeIR) = typeIR)) (fun (_ : Unit) => (.pure ((((castResult.OK ([((SpecTec.typeIR.BOOL) : SpecTec.typeIR)] : (_root_.List SpecTec.typeIR))) : castResult) : castResult))))))))) | none => .unmatch)))))


noncomputable def «Cast_expl_neq:clause:2» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:intTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Cast_expl_neq:fixInt:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : SpecTec.intTypeIR := «exec:1»; (let intTypeIR : SpecTec.intTypeIR := «eval:0»; (.bind (.guard (((SpecTec.intTypeIR.INT) : SpecTec.intTypeIR) = intTypeIR)) (fun (_ : Unit) => (let typeIR'' : SpecTec.typeIR := typeIR; (.bind (.guard (((«sub:typeIR:fixedIntTypeIR» typeIR'') = true))) (fun (_ : Unit) => (match («Cast_expl_neq:fixInt:downcast:1» typeIR'') with | some «exec:2» => (let «eval:1» : fixedIntTypeIR := «exec:2»; (match «eval:1» with | .«INT `< % `>» «exec:3» => (let w : _root_.Nat := «exec:3»; (.pure ((((castResult.OK ([((SpecTec.typeIR.«INT `< % `>» w) : SpecTec.typeIR)] : (_root_.List SpecTec.typeIR))) : castResult) : castResult)))))) | none => .unmatch)))))))) | none => .unmatch)))))


noncomputable def «Cast_expl_neq:clause:3» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:intTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Cast_expl_neq:fixBit:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : SpecTec.intTypeIR := «exec:1»; (let intTypeIR : SpecTec.intTypeIR := «eval:0»; (.bind (.guard (((SpecTec.intTypeIR.INT) : SpecTec.intTypeIR) = intTypeIR)) (fun (_ : Unit) => (let typeIR'' : SpecTec.typeIR := typeIR; (.bind (.guard (((«sub:typeIR:fixedBitTypeIR» typeIR'') = true))) (fun (_ : Unit) => (match («Cast_expl_neq:fixBit:downcast:1» typeIR'') with | some «exec:2» => (let «eval:1» : fixedBitTypeIR := «exec:2»; (match «eval:1» with | .«BIT `< % `>» «exec:3» => (let w : _root_.Nat := «exec:3»; (.pure ((((castResult.OK ([((SpecTec.typeIR.«BIT `< % `>» w) : SpecTec.typeIR)] : (_root_.List SpecTec.typeIR))) : castResult) : castResult)))))) | none => .unmatch)))))))) | none => .unmatch)))))


noncomputable def «Cast_expl_neq:clause:4» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:fixedIntTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Cast_expl_neq:arbitraryInt:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : fixedIntTypeIR := «exec:1»; (match «eval:0» with | .«INT `< % `>» «exec:2» => (let nat : _root_.Nat := «exec:2»; (let _nat : _root_.Nat := nat; (.bind (.guard (((SpecTec.typeIR.INT) : SpecTec.typeIR) = typeIR)) (fun (_ : Unit) => (.pure ((((castResult.OK ([((SpecTec.typeIR.INT) : SpecTec.typeIR)] : (_root_.List SpecTec.typeIR))) : castResult) : castResult))))))))) | none => .unmatch)))))


noncomputable def «Cast_expl_neq:clause:5» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:fixedIntTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Cast_expl_neq:fixInt_2:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : fixedIntTypeIR := «exec:1»; (match «eval:0» with | .«INT `< % `>» «exec:2» => (let nat : _root_.Nat := «exec:2»; (let w_a : _root_.Nat := nat; (let typeIR'' : SpecTec.typeIR := typeIR; (.bind (.guard (((«sub:typeIR:fixedIntTypeIR» typeIR'') = true))) (fun (_ : Unit) => (match («Cast_expl_neq:fixInt_2:downcast:1» typeIR'') with | some «exec:3» => (let «eval:1» : fixedIntTypeIR := «exec:3»; (match «eval:1» with | .«INT `< % `>» «exec:4» => (let w_b : _root_.Nat := «exec:4»; (.pure ((((castResult.OK ([((SpecTec.typeIR.«INT `< % `>» w_b) : SpecTec.typeIR)] : (_root_.List SpecTec.typeIR))) : castResult) : castResult)))))) | none => .unmatch)))))))) | none => .unmatch)))))

end SpecTec
