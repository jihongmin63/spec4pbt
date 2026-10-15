import SpecTecDecl0153

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$specialize_constructorTypeDefIR:case_1:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$specialize_constructorTypeDefIR:case_1:iter:2:clause:1»  input0 input1)]


noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:4:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:4:clause:1» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR_impl : typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR_impl : typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_constructorTypeDefIR:case_1:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR_impl typeArgumentIR_impl) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:4_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$specialize_constructorTypeDefIR:case_1:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$specialize_constructorTypeDefIR:case_1:iter:4:clause:1»  input0 input1)]


noncomputable def «$specialize_constructorTypeDefIR:case_2:iter:1:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch)


noncomputable def «$specialize_constructorTypeDefIR:case_2:iter:1:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_fresh : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (let typeArgumentIR_fresh : typeArgumentIR := ((typeIR._NAME typeId_fresh) : typeIR); (.bind (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«$specialize_constructorTypeDefIR:case_2:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeArgumentIR)) => (let «tail:1» : (_root_.List typeArgumentIR) := «exec:3»; (.pure (((typeArgumentIR_fresh :: «tail:1») : (_root_.List typeArgumentIR)))))))))) | [] => .unmatch)


noncomputable def «$specialize_constructorTypeDefIR:case_2:iter:1_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$specialize_constructorTypeDefIR:case_2:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$specialize_constructorTypeDefIR:case_2:iter:1:clause:1»  input0)]


noncomputable def «$specialize_constructorTypeDefIR:case_2:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$specialize_constructorTypeDefIR:case_2:iter:2:clause:1» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR_fresh : typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_constructorTypeDefIR:case_2:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR typeArgumentIR_fresh) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$specialize_constructorTypeDefIR:case_2:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$specialize_constructorTypeDefIR:case_2:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$specialize_constructorTypeDefIR:case_2:iter:2:clause:1»  input0 input1)]


noncomputable def «Type_alpha:non-default_2:pattern-iter:2:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:non-default_2:pattern-iter:2:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:3»; (let typeIR_field_a : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_alpha:non-default_2:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List SpecTec.annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field_a :: «pattern-tail:3»))) : ((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Type_alpha:non-default_2:pattern-iter:2_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:non-default_2:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Type_alpha:non-default_2:pattern-iter:2:clause:1»  input0)]


noncomputable def «Type_alpha:non-default_2:pattern-iter:4:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List typeIR)), (([] : (_root_.List annotationList)), ([] : (_root_.List nameIR)))) : ((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List nameIR)))))) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:non-default_2:pattern-iter:4:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList' : annotationList := «exec:3»; (let typeIR_field_b : typeIR := «exec:4»; (let nameIR : SpecTec.nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List SpecTec.nameIR))), SpecTecCall.«Type_alpha:non-default_2:pattern-iter:4» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List SpecTec.nameIR)))) => (let «pattern-tail:1» : (_root_.List typeIR) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List annotationList) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.nameIR) := ((«exec:6»).2).2; (.pure ((((typeIR_field_b :: «pattern-tail:1»), ((annotationList' :: «pattern-tail:2»), (nameIR :: «pattern-tail:3»))) : ((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List SpecTec.nameIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Type_alpha:non-default_2:pattern-iter:4_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:non-default_2:pattern-iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Type_alpha:non-default_2:pattern-iter:4:clause:1»  input0)]


noncomputable def «Type_alpha:default_2:pattern-iter:2:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:default_2:pattern-iter:2:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:3»; (let typeIR_field_a : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_alpha:default_2:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List SpecTec.annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field_a :: «pattern-tail:3»))) : ((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Type_alpha:default_2:pattern-iter:2_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:default_2:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Type_alpha:default_2:pattern-iter:2:clause:1»  input0)]


noncomputable def «Type_alpha:default_2:pattern-iter:4:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List typeIR)), (([] : (_root_.List annotationList)), ([] : (_root_.List nameIR)))) : ((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List nameIR)))))) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:default_2:pattern-iter:4:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList' : annotationList := «exec:3»; (let typeIR_field_b : typeIR := «exec:4»; (let nameIR : SpecTec.nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List SpecTec.nameIR))), SpecTecCall.«Type_alpha:default_2:pattern-iter:4» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List SpecTec.nameIR)))) => (let «pattern-tail:1» : (_root_.List typeIR) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List annotationList) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.nameIR) := ((«exec:6»).2).2; (.pure ((((typeIR_field_b :: «pattern-tail:1»), ((annotationList' :: «pattern-tail:2»), (nameIR :: «pattern-tail:3»))) : ((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List SpecTec.nameIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Type_alpha:default_2:pattern-iter:4_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:default_2:pattern-iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Type_alpha:default_2:pattern-iter:4:clause:1»  input0)]


noncomputable def «ExternMethodTypeDef_alpha:rule:iter:3:clause:0» (input0 : (_root_.List typeParameterIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «ExternMethodTypeDef_alpha:rule:iter:3:clause:1» (input0 : (_root_.List typeParameterIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR_a : typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List typeParameterIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR_fresh : typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«ExternMethodTypeDef_alpha:rule:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR_a ((typeIR._NAME typeParameterIR_fresh) : typeIR)) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «ExternMethodTypeDef_alpha:rule:iter:3_clauses» (input0 : (_root_.List typeParameterIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ExternMethodTypeDef_alpha:rule:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («ExternMethodTypeDef_alpha:rule:iter:3:clause:1»  input0 input1)]


noncomputable def «ExternMethodTypeDef_alpha:rule:iter:9:clause:0» (input0 : (_root_.List typeParameterIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «ExternMethodTypeDef_alpha:rule:iter:9:clause:1» (input0 : (_root_.List typeParameterIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR_b : typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List typeParameterIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR_fresh : typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«ExternMethodTypeDef_alpha:rule:iter:9» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR_b ((typeIR._NAME typeParameterIR_fresh) : typeIR)) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «ExternMethodTypeDef_alpha:rule:iter:9_clauses» (input0 : (_root_.List typeParameterIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ExternMethodTypeDef_alpha:rule:iter:9:clause:0»  input0 input1), fun (_ : _root_.Unit) => («ExternMethodTypeDef_alpha:rule:iter:9:clause:1»  input0 input1)]


noncomputable def «$default:case_13:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$default:case_13:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_f : typeIR := «exec:4»; (let id_f : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$default:case_13:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((id_f :: «pattern-tail:2»), (typeIR_f :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$default:case_13:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:case_13:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$default:case_13:pattern-iter:1:clause:1»  input0)]


noncomputable def «$default:case_14:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)

end SpecTec
