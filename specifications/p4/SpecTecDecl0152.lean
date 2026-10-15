import SpecTecDecl0151

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$capture_avoiding:case_1:iter:12:clause:1» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR_impl_fresh : typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List typeParameterIR) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding:case_1:iter:12» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeParameterIR_impl_fresh) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «$capture_avoiding:case_1:iter:12_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:12:clause:0»  input0), fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:12:clause:1»  input0)]


noncomputable def «$subst_typeIR':case_10:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_10:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$subst_typeIR':case_10:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List SpecTec.annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_10:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_10:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$subst_typeIR':case_10:pattern-iter:1:clause:1»  input0)]


noncomputable def «$subst_typeIR':case_10:iter:7:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_10:iter:7:clause:1» (input0 : (_root_.List SpecTec.annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList : SpecTec.annotationList := «exec:2»; (let «tail:0» : (_root_.List SpecTec.annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_field : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_field_subst : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$subst_typeIR':case_10:iter:7» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList typeIR_field_subst nameIR_field) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_10:iter:7_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_10:iter:7:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$subst_typeIR':case_10:iter:7:clause:1»  input0 input1 input2)]


noncomputable def «$subst_typeIR':case_11:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_11:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$subst_typeIR':case_11:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List SpecTec.annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_11:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_11:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$subst_typeIR':case_11:pattern-iter:1:clause:1»  input0)]


noncomputable def «$subst_typeIR':case_11:iter:7:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_11:iter:7:clause:1» (input0 : (_root_.List SpecTec.annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList : SpecTec.annotationList := «exec:2»; (let «tail:0» : (_root_.List SpecTec.annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_field : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_field_subst : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$subst_typeIR':case_11:iter:7» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList typeIR_field_subst nameIR_field) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_11:iter:7_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_11:iter:7:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$subst_typeIR':case_11:iter:7:clause:1»  input0 input1 input2)]


noncomputable def «$subst_typeIR':case_12:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_12:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$subst_typeIR':case_12:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List SpecTec.annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List SpecTec.annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_12:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_12:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$subst_typeIR':case_12:pattern-iter:1:clause:1»  input0)]


noncomputable def «$subst_typeIR':case_12:iter:7:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_12:iter:7:clause:1» (input0 : (_root_.List SpecTec.annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList : SpecTec.annotationList := «exec:2»; (let «tail:0» : (_root_.List SpecTec.annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_field : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_field_subst : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$subst_typeIR':case_12:iter:7» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList typeIR_field_subst nameIR_field) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_12:iter:7_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_12:iter:7:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$subst_typeIR':case_12:iter:7:clause:1»  input0 input1 input2)]


noncomputable def «$subst_typeIR':case_15:pattern-iter:1:clause:0» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List callableId)), ([] : (_root_.List externMethodTypeDefIR))) : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))))) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_15:pattern-iter:1:clause:1» (input0 : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId : SpecTec.callableId := «exec:3»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.callableId) × (_root_.List SpecTec.externMethodTypeDefIR)), SpecTecCall.«$subst_typeIR':case_15:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.callableId) × (_root_.List SpecTec.externMethodTypeDefIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.callableId) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.externMethodTypeDefIR) := («exec:5»).2; (.pure ((((callableId :: «pattern-tail:1»), (externMethodTypeDefIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.callableId) × (_root_.List SpecTec.externMethodTypeDefIR))))))))))))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_15:pattern-iter:1_clauses» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_15:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$subst_typeIR':case_15:pattern-iter:1:clause:1»  input0)]


noncomputable def «$subst_typeIR':case_15:iter:8:clause:0» (input0 : (_root_.List callableTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List externMethodTypeDefIR)) : (_root_.List externMethodTypeDefIR)))) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_15:iter:8:clause:1» (input0 : (_root_.List SpecTec.callableTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableTypeDefIR : SpecTec.callableTypeDefIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.callableTypeDefIR) := «exec:1»; (match («$subst_typeIR':case_15:downcast:9» callableTypeDefIR) with | some «exec:3» => (let «eval:9» : externMethodTypeDefIR := «exec:3»; (let externMethodTypeDefIR_subst : externMethodTypeDefIR := «eval:9»; (.bind (.call ⟨(_root_.List externMethodTypeDefIR), SpecTecCall.«$subst_typeIR':case_15:iter:8» «tail:0»⟩) (fun («exec:4» : (_root_.List externMethodTypeDefIR)) => (let «tail:1» : (_root_.List externMethodTypeDefIR) := «exec:4»; (.pure (((externMethodTypeDefIR_subst :: «tail:1») : (_root_.List externMethodTypeDefIR))))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_15:iter:8_clauses» (input0 : (_root_.List callableTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_15:iter:8:clause:0»  input0), fun (_ : _root_.Unit) => («$subst_typeIR':case_15:iter:8:clause:1»  input0)]


noncomputable def «$subst_typeIR':case_15:iter:10:clause:0» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId externMethodTypeDefIR))) : (_root_.List (pair callTargetId externMethodTypeDefIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_15:iter:10:clause:1» (input0 : (_root_.List SpecTec.callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableId : SpecTec.callableId := «exec:2»; (let «tail:0» : (_root_.List SpecTec.callableId) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let externMethodTypeDefIR_subst : externMethodTypeDefIR := «exec:4»; (let «tail:1» : (_root_.List externMethodTypeDefIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId externMethodTypeDefIR)), SpecTecCall.«$subst_typeIR':case_15:iter:10» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId externMethodTypeDefIR))) => (let «tail:2» : (_root_.List (pair callTargetId externMethodTypeDefIR)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId externMethodTypeDefIR_subst) : (pair SpecTec.callableId externMethodTypeDefIR)) :: «tail:2») : (_root_.List (pair callTargetId externMethodTypeDefIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_15:iter:10_clauses» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_15:iter:10:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_15:iter:10:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_24:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$subst_typeIR':case_24:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let id_field : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$subst_typeIR':case_24:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List SpecTec.annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List SpecTec.annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList :: «pattern-tail:1»), ((id_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List SpecTec.annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$subst_typeIR':case_24:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_24:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$subst_typeIR':case_24:pattern-iter:1:clause:1»  input0)]

end SpecTec
