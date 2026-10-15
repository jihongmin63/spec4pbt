import SpecTecDecl0189

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:15_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:15:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:15:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:14:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_field_b*» : (_root_.List id) := input0; (let «typeIR_field_b*» : (_root_.List typeIR) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List (_root_.Option typeIR))) : (_root_.List (_root_.Option typeIR))))) | _ :: _ => .unmatch)))


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:14:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_field_b*» : (_root_.List id) := input0; (let «typeIR_field_b*» : (_root_.List typeIR) := input1; (match input2 with | «exec:2» :: «exec:1» => (let id_field_a : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:15» «id_field_b*» «typeIR_field_b*»⟩) (fun («exec:3» : (_root_.List (pair _root_.String typeIR))) => (let «eval:16» : (_root_.List (pair id typeIR)) := «exec:3»; (.bind (.call ⟨(_root_.Option typeIR), SpecTecCall.«$find_map» id typeIR ((set.«`{ % `}» «eval:16») : (set (pair id typeIR))) id_field_a⟩) (fun («exec:4» : (_root_.Option typeIR)) => (let «eval:17» : (_root_.Option typeIR) := «exec:4»; (let typeIR''''? : (_root_.Option typeIR) := «eval:17»; (.bind (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:14» «id_field_b*» «typeIR_field_b*» «tail:0»⟩) (fun («exec:5» : (_root_.List (_root_.Option typeIR))) => (let «tail:1» : (_root_.List (_root_.Option typeIR)) := «exec:5»; (.pure (((typeIR''''? :: «tail:1») : (_root_.List (_root_.Option typeIR))))))))))))))))) | [] => .unmatch)))


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:14_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:14:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:14:clause:1»  input0 input1 input2)]


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:18:clause:0» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:18:clause:1» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR''''? : (_root_.Option typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typeIR)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome typeIR''''?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:18» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:18_clauses» (input0 : (_root_.List (_root_.Option typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:18:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:18:clause:1»  input0)]


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:19:clause:0» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:19:clause:1» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR''''? : (_root_.Option typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typeIR)) := «exec:1»; (match typeIR''''? with | some «exec:3» => (let typeIR_field_b_non_default_aligned : typeIR := «exec:3»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:19» «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_field_b_non_default_aligned :: «tail:1») : (_root_.List typeIR)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:19_clauses» (input0 : (_root_.List (_root_.Option typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:19:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:19:clause:1»  input0)]


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:22:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:22:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:22» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:22_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:22:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:22:clause:1»  input0)]


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:24:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:24:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_field_b : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field_b : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:24» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» id_field_b typeIR_field_b) : (pair id typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:24_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:24:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:24:clause:1»  input0 input1)]


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:23:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_field_b*» : (_root_.List id) := input0; (let «typeIR_field_b*» : (_root_.List typeIR) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List (_root_.Option typeIR))) : (_root_.List (_root_.Option typeIR))))) | _ :: _ => .unmatch)))


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:23:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_field_b*» : (_root_.List id) := input0; (let «typeIR_field_b*» : (_root_.List typeIR) := input1; (match input2 with | «exec:2» :: «exec:1» => (let id_default : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:24» «id_field_b*» «typeIR_field_b*»⟩) (fun («exec:3» : (_root_.List (pair _root_.String typeIR))) => (let «eval:25» : (_root_.List (pair id typeIR)) := «exec:3»; (.bind (.call ⟨(_root_.Option typeIR), SpecTecCall.«$find_map» id typeIR ((set.«`{ % `}» «eval:25») : (set (pair id typeIR))) id_default⟩) (fun («exec:4» : (_root_.Option typeIR)) => (let «eval:26» : (_root_.Option typeIR) := «exec:4»; (let typeIR'''''? : (_root_.Option typeIR) := «eval:26»; (.bind (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:23» «id_field_b*» «typeIR_field_b*» «tail:0»⟩) (fun («exec:5» : (_root_.List (_root_.Option typeIR))) => (let «tail:1» : (_root_.List (_root_.Option typeIR)) := «exec:5»; (.pure (((typeIR'''''? :: «tail:1») : (_root_.List (_root_.Option typeIR))))))))))))))))) | [] => .unmatch)))


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:23_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:23:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:23:clause:1»  input0 input1 input2)]


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:27:clause:0» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:27:clause:1» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR'''''? : (_root_.Option typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typeIR)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome typeIR'''''?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:27» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:27_clauses» (input0 : (_root_.List (_root_.Option typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:27:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:27:clause:1»  input0)]


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:28:clause:0» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:28:clause:1» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR'''''? : (_root_.Option typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typeIR)) := «exec:1»; (match typeIR'''''? with | some «exec:3» => (let typeIR_field_b_default : typeIR := «exec:3»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:28» «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_field_b_default :: «tail:1») : (_root_.List typeIR)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:28_clauses» (input0 : (_root_.List (_root_.Option typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:28:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:28:clause:1»  input0)]


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:29:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:29:clause:1» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field_b_default : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_defaultable_typeIR» typeIR_field_b_default⟩) (fun («exec:3» : _root_.Bool) => (let «eval:30» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:30» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:29» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:29_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:29:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_5:iter:29:clause:1»  input0)]


noncomputable def «Cast_impl_neq:listTypeIR:iter:4:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:listTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_impl_neq:listTypeIR:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:listTypeIR:iter:4_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:listTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:listTypeIR:iter:4:clause:1»  input0)]


noncomputable def «Cast_impl_neq:tupleTypeIR:iter:4:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)

end SpecTec
