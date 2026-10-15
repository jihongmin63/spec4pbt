import SpecTecDecl0184

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Cast_expl_neq:structTypeIR_2:iter:7:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:structTypeIR_2:iter:7» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_2:iter:7_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_2:iter:7:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_2:iter:7:clause:1»  input0)]


noncomputable def «Cast_expl_neq:structTypeIR_2:iter:8:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_2:iter:8:clause:1» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field_b_default : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_defaultable_typeIR» typeIR_field_b_default⟩) (fun («exec:3» : _root_.Bool) => (let «eval:9» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:9» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR_2:iter:8» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_2:iter:8_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_2:iter:8:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_2:iter:8:clause:1»  input0)]


noncomputable def «Cast_expl_neq:headerTypeIR_3:pattern-iter:2:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_3:pattern-iter:2:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field_b : typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Cast_expl_neq:headerTypeIR_3:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR_field_b :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_3:pattern-iter:2_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_3:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_3:pattern-iter:2:clause:1»  input0)]


noncomputable def «Cast_expl_neq:headerTypeIR_3:iter:7:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_3:iter:7:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_3:iter:7» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_3:iter:7_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_3:iter:7:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_3:iter:7:clause:1»  input0)]


noncomputable def «Cast_expl_neq:headerTypeIR_3:iter:8:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_3:iter:8:clause:1» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field_b_default : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_defaultable_typeIR» typeIR_field_b_default⟩) (fun («exec:3» : _root_.Bool) => (let «eval:9» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:9» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_3:iter:8» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_3:iter:8_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_3:iter:8:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_3:iter:8:clause:1»  input0)]


noncomputable def «Cast_expl_neq:structTypeIR_3:pattern-iter:2:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_3:pattern-iter:2:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field_a : typeIR := «exec:4»; (let id_field_a : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«Cast_expl_neq:structTypeIR_3:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((id_field_a :: «pattern-tail:2»), (typeIR_field_a :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_3:pattern-iter:2_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:pattern-iter:2:clause:1»  input0)]


noncomputable def «Cast_expl_neq:structTypeIR_3:pattern-iter:4:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_3:pattern-iter:4:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList' : annotationList := «exec:3»; (let typeIR_field_b : typeIR := «exec:4»; (let id_field_b : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«Cast_expl_neq:structTypeIR_3:pattern-iter:4» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList' :: «pattern-tail:1»), ((id_field_b :: «pattern-tail:2»), (typeIR_field_b :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_3:pattern-iter:4_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:pattern-iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:pattern-iter:4:clause:1»  input0)]


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:7:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_field_a*» : (_root_.List id) := input0; (let «typeIR_field_a*» : (_root_.List typeIR) := input1; (match input2 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)))


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:7:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_field_a*» : (_root_.List id) := input0; (let «typeIR_field_a*» : (_root_.List typeIR) := input1; (match input2 with | «exec:2» :: «exec:1» => (let id_field_a : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (.bind (.guard ((_root_.List.length «typeIR_field_a*») = (_root_.List.length «id_field_a*»))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR_3:iter:7» «id_field_a*» «typeIR_field_a*» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)))


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:7_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:iter:7:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:iter:7:clause:1»  input0 input1 input2)]


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:9:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:9:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_field_a : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_a : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:structTypeIR_3:iter:9» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» id_field_a typeIR_field_a) : (pair id typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:9_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:iter:9:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:iter:9:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:8:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_field_a*» : (_root_.List id) := input0; (let «typeIR_field_a*» : (_root_.List typeIR) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List (_root_.Option typeIR))) : (_root_.List (_root_.Option typeIR))))) | _ :: _ => .unmatch)))


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:8:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_field_a*» : (_root_.List id) := input0; (let «typeIR_field_a*» : (_root_.List typeIR) := input1; (match input2 with | «exec:2» :: «exec:1» => (let id_field_a : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:structTypeIR_3:iter:9» «id_field_a*» «typeIR_field_a*»⟩) (fun («exec:3» : (_root_.List (pair _root_.String typeIR))) => (let «eval:10» : (_root_.List (pair id typeIR)) := «exec:3»; (.bind (.call ⟨(_root_.Option typeIR), SpecTecCall.«$find_map» id typeIR ((set.«`{ % `}» «eval:10») : (set (pair id typeIR))) id_field_a⟩) (fun («exec:4» : (_root_.Option typeIR)) => (let «eval:11» : (_root_.Option typeIR) := «exec:4»; (let typeIR'''? : (_root_.Option typeIR) := «eval:11»; (.bind (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«Cast_expl_neq:structTypeIR_3:iter:8» «id_field_a*» «typeIR_field_a*» «tail:0»⟩) (fun («exec:5» : (_root_.List (_root_.Option typeIR))) => (let «tail:1» : (_root_.List (_root_.Option typeIR)) := «exec:5»; (.pure (((typeIR'''? :: «tail:1») : (_root_.List (_root_.Option typeIR))))))))))))))))) | [] => .unmatch)))


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:8_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:iter:8:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:iter:8:clause:1»  input0 input1 input2)]


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:12:clause:0» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:12:clause:1» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR'''? : (_root_.Option typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typeIR)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome typeIR'''?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR_3:iter:12» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:12_clauses» (input0 : (_root_.List (_root_.Option typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:iter:12:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR_3:iter:12:clause:1»  input0)]

end SpecTec
