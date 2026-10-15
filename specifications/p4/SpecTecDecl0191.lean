import SpecTecDecl0190

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Cast_impl_neq:tupleTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:tupleTypeIR:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:tupleTypeIR:iter:4_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:tupleTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:tupleTypeIR:iter:4:clause:1»  input0)]


noncomputable def «Cast_impl_neq:arrayTypeIR:iter:4:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:arrayTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:arrayTypeIR:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:arrayTypeIR:iter:4_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:arrayTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:arrayTypeIR:iter:4:clause:1»  input0)]


noncomputable def «Cast_impl_neq:headerStackTypeIR:iter:4:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerStackTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:headerStackTypeIR:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:headerStackTypeIR:iter:4_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerStackTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:headerStackTypeIR:iter:4:clause:1»  input0)]


noncomputable def «Cast_impl_neq:structTypeIR:pattern-iter:2:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR:pattern-iter:2:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field_b : typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Cast_impl_neq:structTypeIR:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR_field_b :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR:pattern-iter:2_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR:pattern-iter:2:clause:1»  input0)]


noncomputable def «Cast_impl_neq:structTypeIR:iter:6:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR:iter:6:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:structTypeIR:iter:6» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR:iter:6_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR:iter:6:clause:1»  input0)]


noncomputable def «Cast_impl_neq:headerTypeIR_2:pattern-iter:2:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_2:pattern-iter:2:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field_b : typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Cast_impl_neq:headerTypeIR_2:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR_field_b :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_2:pattern-iter:2_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_2:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_2:pattern-iter:2:clause:1»  input0)]


noncomputable def «Cast_impl_neq:headerTypeIR_2:iter:6:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_2:iter:6:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:headerTypeIR_2:iter:6» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_2:iter:6_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_2:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_2:iter:6:clause:1»  input0)]


noncomputable def «Cast_impl_neq:sequenceTypeIR:iter:4:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:sequenceTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:sequenceTypeIR:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:sequenceTypeIR:iter:4_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:sequenceTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:sequenceTypeIR:iter:4:clause:1»  input0)]


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:5:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:5:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:tupleTypeIR_2:iter:5» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:5_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:tupleTypeIR_2:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:tupleTypeIR_2:iter:5:clause:1»  input0)]


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:6:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:6:clause:1» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_b_default : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_defaultable_typeIR» typeIR_b_default⟩) (fun («exec:3» : _root_.Bool) => (let «eval:7» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:7» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:tupleTypeIR_2:iter:6» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:6_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:tupleTypeIR_2:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:tupleTypeIR_2:iter:6:clause:1»  input0)]


noncomputable def «Cast_impl_neq:arrayTypeIR_2:iter:4:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:arrayTypeIR_2:iter:4:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:arrayTypeIR_2:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:arrayTypeIR_2:iter:4_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:arrayTypeIR_2:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:arrayTypeIR_2:iter:4:clause:1»  input0)]

end SpecTec
