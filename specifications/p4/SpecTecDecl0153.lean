import SpecTecDecl0152

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$subst_typeIR':case_24:iter:5:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_24:iter:5:clause:1» (input0 : (_root_.List SpecTec.annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList : SpecTec.annotationList := «exec:2»; (let «tail:0» : (_root_.List SpecTec.annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let id_field : id := «exec:4»; (let «tail:1» : (_root_.List id) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_field_subst : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$subst_typeIR':case_24:iter:5» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList typeIR_field_subst id_field) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_24:iter:5_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_24:iter:5:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$subst_typeIR':case_24:iter:5:clause:1»  input0 input1 input2)]


noncomputable def «$subst_typeIR':case_25:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_25:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let id_field : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$subst_typeIR':case_25:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List SpecTec.annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List SpecTec.annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList :: «pattern-tail:1»), ((id_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List SpecTec.annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_25:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_25:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$subst_typeIR':case_25:pattern-iter:1:clause:1»  input0)]


noncomputable def «$subst_typeIR':case_25:iter:5:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_25:iter:5:clause:1» (input0 : (_root_.List SpecTec.annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList : SpecTec.annotationList := «exec:2»; (let «tail:0» : (_root_.List SpecTec.annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let id_field : id := «exec:4»; (let «tail:1» : (_root_.List id) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_field_subst : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$subst_typeIR':case_25:iter:5» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList typeIR_field_subst id_field) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_25:iter:5_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_25:iter:5:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$subst_typeIR':case_25:iter:5:clause:1»  input0 input1 input2)]


noncomputable def «$specialize_typeDefIR:case_1:iter:1:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$specialize_typeDefIR:case_1:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) (input1 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_typeDefIR:case_1:iter:1» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR typeArgumentIR) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$specialize_typeDefIR:case_1:iter:1_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$specialize_typeDefIR:case_1:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$specialize_typeDefIR:case_1:iter:1:clause:1»  input0 input1)]


noncomputable def «$specialize_callableTypeDefIR:case_1:iter:2:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch)


noncomputable def «$specialize_callableTypeDefIR:case_1:iter:2:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_fresh : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (let typeArgumentIR_impl : typeArgumentIR := ((typeIR._NAME typeId_fresh) : typeIR); (.bind (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«$specialize_callableTypeDefIR:case_1:iter:2» «tail:0»⟩) (fun («exec:3» : (_root_.List typeArgumentIR)) => (let «tail:1» : (_root_.List typeArgumentIR) := «exec:3»; (.pure (((typeArgumentIR_impl :: «tail:1») : (_root_.List typeArgumentIR)))))))))) | [] => .unmatch)


noncomputable def «$specialize_callableTypeDefIR:case_1:iter:2_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$specialize_callableTypeDefIR:case_1:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$specialize_callableTypeDefIR:case_1:iter:2:clause:1»  input0)]


noncomputable def «$specialize_callableTypeDefIR:case_1:iter:3:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$specialize_callableTypeDefIR:case_1:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR_expl : typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_callableTypeDefIR:case_1:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR_expl typeArgumentIR) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$specialize_callableTypeDefIR:case_1:iter:3_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$specialize_callableTypeDefIR:case_1:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$specialize_callableTypeDefIR:case_1:iter:3:clause:1»  input0 input1)]


noncomputable def «$specialize_callableTypeDefIR:case_1:iter:5:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$specialize_callableTypeDefIR:case_1:iter:5:clause:1» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR_impl : typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR_impl : typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_callableTypeDefIR:case_1:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR_impl typeArgumentIR_impl) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$specialize_callableTypeDefIR:case_1:iter:5_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$specialize_callableTypeDefIR:case_1:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$specialize_callableTypeDefIR:case_1:iter:5:clause:1»  input0 input1)]


noncomputable def «$specialize_callableTypeDefIR:case_2:iter:2:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch)


noncomputable def «$specialize_callableTypeDefIR:case_2:iter:2:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_fresh : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (let typeArgumentIR_fresh : typeArgumentIR := ((typeIR._NAME typeId_fresh) : typeIR); (.bind (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«$specialize_callableTypeDefIR:case_2:iter:2» «tail:0»⟩) (fun («exec:3» : (_root_.List typeArgumentIR)) => (let «tail:1» : (_root_.List typeArgumentIR) := «exec:3»; (.pure (((typeArgumentIR_fresh :: «tail:1») : (_root_.List typeArgumentIR)))))))))) | [] => .unmatch)


noncomputable def «$specialize_callableTypeDefIR:case_2:iter:2_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$specialize_callableTypeDefIR:case_2:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$specialize_callableTypeDefIR:case_2:iter:2:clause:1»  input0)]


noncomputable def «$specialize_callableTypeDefIR:case_2:iter:3:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$specialize_callableTypeDefIR:case_2:iter:3:clause:1» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR_fresh : typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_callableTypeDefIR:case_2:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR typeArgumentIR_fresh) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$specialize_callableTypeDefIR:case_2:iter:3_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$specialize_callableTypeDefIR:case_2:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$specialize_callableTypeDefIR:case_2:iter:3:clause:1»  input0 input1)]


noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:1:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch)


noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:1:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_fresh : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (let typeArgumentIR_impl : typeArgumentIR := ((typeIR._NAME typeId_fresh) : typeIR); (.bind (.call ⟨(_root_.List typeArgumentIR), SpecTecCall.«$specialize_constructorTypeDefIR:case_1:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeArgumentIR)) => (let «tail:1» : (_root_.List typeArgumentIR) := «exec:3»; (.pure (((typeArgumentIR_impl :: «tail:1») : (_root_.List typeArgumentIR)))))))))) | [] => .unmatch)


noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:1_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$specialize_constructorTypeDefIR:case_1:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$specialize_constructorTypeDefIR:case_1:iter:1:clause:1»  input0)]


noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$specialize_constructorTypeDefIR:case_1:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR_expl : typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$specialize_constructorTypeDefIR:case_1:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR_expl typeArgumentIR) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)

end SpecTec
