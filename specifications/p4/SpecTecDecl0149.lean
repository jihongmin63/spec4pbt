import SpecTecDecl0148

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$is_serializable_typeIR:row_12:iter:2:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$is_serializable_typeIR:row_12:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_serializable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_12:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:3» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$is_serializable_typeIR:row_12:iter:2_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_12:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_12:iter:2:clause:1»  input0)]


noncomputable def «$typeIR_of_typeDefIR:case_3:iter:1:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_3:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeParameterIR) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_3:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeParameterIR) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_3:iter:1_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_3:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_3:iter:1:clause:1»  input0)]


noncomputable def «$typeIR_of_typeDefIR:case_4:iter:1:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_4:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeParameterIR) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_4:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeParameterIR) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_4:iter:1_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_4:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_4:iter:1:clause:1»  input0)]


noncomputable def «$typeIR_of_typeDefIR:case_5:iter:1:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_5:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeParameterIR) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_5:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeParameterIR) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_5:iter:1_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_5:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_5:iter:1:clause:1»  input0)]


noncomputable def «$typeIR_of_typeDefIR:case_7:pattern-iter:1:clause:0» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List callableId)), ([] : (_root_.List externMethodTypeDefIR))) : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))))) | _ :: _ => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_7:pattern-iter:1:clause:1» (input0 : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId : SpecTec.callableId := «exec:3»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.callableId) × (_root_.List SpecTec.externMethodTypeDefIR)), SpecTecCall.«$typeIR_of_typeDefIR:case_7:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.callableId) × (_root_.List SpecTec.externMethodTypeDefIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.callableId) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.externMethodTypeDefIR) := («exec:5»).2; (.pure ((((callableId :: «pattern-tail:1»), (externMethodTypeDefIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.callableId) × (_root_.List SpecTec.externMethodTypeDefIR))))))))))))) | [] => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_7:pattern-iter:1_clauses» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_7:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_7:pattern-iter:1:clause:1»  input0)]


noncomputable def «$typeIR_of_typeDefIR:case_7:iter:3:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_7:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeParameterIR) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_7:iter:3» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeParameterIR) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_7:iter:3_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_7:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_7:iter:3:clause:1»  input0)]


noncomputable def «$typeIR_of_typeDefIR:case_7:iter:5:clause:0» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId externMethodTypeDefIR))) : (_root_.List (pair callTargetId externMethodTypeDefIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_7:iter:5:clause:1» (input0 : (_root_.List SpecTec.callableId)) (input1 : (_root_.List SpecTec.externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableId : SpecTec.callableId := «exec:2»; (let «tail:0» : (_root_.List SpecTec.callableId) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.externMethodTypeDefIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)), SpecTecCall.«$typeIR_of_typeDefIR:case_7:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR))) => (let «tail:2» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId externMethodTypeDefIR) : (pair SpecTec.callableId SpecTec.externMethodTypeDefIR)) :: «tail:2») : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_7:iter:5_clauses» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_7:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_7:iter:5:clause:1»  input0 input1)]


noncomputable def «$typeIR_of_typeDefIR:case_8:iter:1:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_8:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeParameterIR) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_8:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeParameterIR) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_8:iter:1_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_8:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_8:iter:1:clause:1»  input0)]


noncomputable def «$typeIR_of_typeDefIR:case_9:iter:1:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_9:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeParameterIR) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_9:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeParameterIR) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_9:iter:1_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_9:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_9:iter:1:clause:1»  input0)]


noncomputable def «$typeIR_of_typeDefIR:case_10:iter:1:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_10:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeParameterIR) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$typeIR_of_typeDefIR:case_10:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeParameterIR) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «$typeIR_of_typeDefIR:case_10:iter:1_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_10:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$typeIR_of_typeDefIR:case_10:iter:1:clause:1»  input0)]


noncomputable def «$id_of_parameterIR:clause:0» (input0 : parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % % % %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:1»; (let _direction : direction := «exec:2»; (let _typeIR : typeIR := «exec:3»; (let id : SpecTec.id := «exec:4»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:5»; (.pure ((id : SpecTec.id)))))))))


noncomputable def «$id_of_parameterIR_clauses» (input0 : parameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$id_of_parameterIR:clause:0»  input0)]

end SpecTec
