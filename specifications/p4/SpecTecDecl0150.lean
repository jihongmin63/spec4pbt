import SpecTecDecl0149

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$is_default_parameterIR:clause:0» (input0 : parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % % % %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:1»; (let _direction : direction := «exec:2»; (let _typeIR : typeIR := «exec:3»; (let _id : id := «exec:4»; (let parameterInitializerIR? : (_root_.Option parameterInitializerIR) := «exec:5»; (.bind (.guard (((_root_.Option.isNone parameterInitializerIR?) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))))))


noncomputable def «$is_default_parameterIR:clause:1» (input0 : parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % % % %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:1»; (let _direction : direction := «exec:2»; (let _typeIR : typeIR := «exec:3»; (let _id : id := «exec:4»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:5»; (.pure ((true : _root_.Bool)))))))))


noncomputable def «$is_default_parameterIR_clauses» (input0 : parameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_default_parameterIR:clause:0»  input0), fun (_ : _root_.Unit) => («$is_default_parameterIR:clause:1»  input0)]


noncomputable def «$annotationList_of_parameterIR:clause:0» (input0 : parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % % % %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:1»; (let _direction : direction := «exec:2»; (let _typeIR : typeIR := «exec:3»; (let _id : id := «exec:4»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:5»; (.pure ((annotationList : SpecTec.annotationList)))))))))


noncomputable def «$annotationList_of_parameterIR_clauses» (input0 : parameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$annotationList_of_parameterIR:clause:0»  input0)]


noncomputable def «$parameterListIR_of_actionTypeDefIR:clause:0» (input0 : actionTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% ACTION % `( % `)» «exec:1» «exec:2» «exec:3» => (let _annotationList : annotationList := «exec:1»; (let _nameIR : nameIR := «exec:2»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:3»; (.pure ((«parameterIR*» : (_root_.List parameterIR))))))))


noncomputable def «$parameterListIR_of_actionTypeDefIR_clauses» (input0 : actionTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_actionTypeDefIR:clause:0»  input0)]


noncomputable def «$parameterListIR_of_definedFunctionTypeDefIR:clause:0» (input0 : definedFunctionTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«FUNCTION % `< % ',' % `> `( % `) ':' %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let _nameIR : nameIR := «exec:1»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:2»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:3»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:4»; (let _typeIR : typeIR := «exec:5»; (.pure ((«parameterIR*» : (_root_.List parameterIR))))))))))


noncomputable def «$parameterListIR_of_definedFunctionTypeDefIR_clauses» (input0 : definedFunctionTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_definedFunctionTypeDefIR:clause:0»  input0)]


noncomputable def «$parameterListIR_of_externFunctionTypeDefIR:clause:0» (input0 : externFunctionTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let _nameIR : nameIR := «exec:1»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:2»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:3»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:4»; (let _typeIR : typeIR := «exec:5»; (.pure ((«parameterIR*» : (_root_.List parameterIR))))))))))


noncomputable def «$parameterListIR_of_externFunctionTypeDefIR_clauses» (input0 : externFunctionTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_externFunctionTypeDefIR:clause:0»  input0)]


noncomputable def «$parameterListIR_of_parserApplyMethodTypeIR:clause:0» (input0 : parserApplyMethodTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«PARSER_APPLY `( % `)» «exec:1» => (let «parameterIR*» : (_root_.List parameterIR) := «exec:1»; (.pure ((«parameterIR*» : (_root_.List parameterIR))))))


noncomputable def «$parameterListIR_of_parserApplyMethodTypeIR_clauses» (input0 : parserApplyMethodTypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_parserApplyMethodTypeIR:clause:0»  input0)]


noncomputable def «$parameterListIR_of_controlApplyMethodTypeIR:clause:0» (input0 : controlApplyMethodTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«CONTROL_APPLY `( % `)» «exec:1» => (let «parameterIR*» : (_root_.List parameterIR) := «exec:1»; (.pure ((«parameterIR*» : (_root_.List parameterIR))))))


noncomputable def «$parameterListIR_of_controlApplyMethodTypeIR_clauses» (input0 : controlApplyMethodTypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_controlApplyMethodTypeIR:clause:0»  input0)]


noncomputable def «$parameterListIR_of_tableApplyMethodTypeDefIR:clause:0» (input0 : tableApplyMethodTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableApplyMethodTypeIR : SpecTec.tableApplyMethodTypeIR := input0; (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))))


noncomputable def «$parameterListIR_of_tableApplyMethodTypeDefIR_clauses» (input0 : tableApplyMethodTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_tableApplyMethodTypeDefIR:clause:0»  input0)]


noncomputable def «$parameterListIR_of_constructorTypeDefIR:clause:0» (input0 : constructorTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«CONSTRUCTOR `< % ',' % `> `( % `) ':' %» «exec:1» «exec:2» «exec:3» «exec:4» => (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:1»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:2»; (let «constructorParameterIR*» : (_root_.List constructorParameterIR) := «exec:3»; (let _typeIR : typeIR := «exec:4»; (.pure ((«constructorParameterIR*» : (_root_.List parameterIR)))))))))


noncomputable def «$parameterListIR_of_constructorTypeDefIR_clauses» (input0 : constructorTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_constructorTypeDefIR:clause:0»  input0)]


noncomputable def «$free_typeIR:case_9:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_9:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$free_typeIR:case_9:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_9:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_9:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_9:pattern-iter:1:clause:1»  input0)]


noncomputable def «$free_typeIR:case_10:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_10:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$free_typeIR:case_10:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_10:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_10:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_10:pattern-iter:1:clause:1»  input0)]


noncomputable def «$free_typeIR:case_11:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_11:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$free_typeIR:case_11:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_11:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_11:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_11:pattern-iter:1:clause:1»  input0)]


noncomputable def «$free_typeIR:case_14:pattern-iter:1:clause:0» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List callableId)), ([] : (_root_.List externMethodTypeDefIR))) : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_14:pattern-iter:1:clause:1» (input0 : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let _callableId : callableId := «exec:3»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)) := «exec:1»; (.bind (.call ⟨((_root_.List callableId) × (_root_.List SpecTec.externMethodTypeDefIR)), SpecTecCall.«$free_typeIR:case_14:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List callableId) × (_root_.List SpecTec.externMethodTypeDefIR))) => (let «pattern-tail:1» : (_root_.List callableId) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.externMethodTypeDefIR) := («exec:5»).2; (.pure ((((_callableId :: «pattern-tail:1»), (externMethodTypeDefIR :: «pattern-tail:2»)) : ((_root_.List callableId) × (_root_.List SpecTec.externMethodTypeDefIR))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_14:pattern-iter:1_clauses» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_14:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_14:pattern-iter:1:clause:1»  input0)]


noncomputable def «$free_typeIR:case_23:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)

end SpecTec
