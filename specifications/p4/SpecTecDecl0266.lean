import SpecTecDecl0265

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$PSA_setup_egress_hdr_argument_clauses» (input0 : arch) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$PSA_setup_egress_hdr_argument:clause:0»  input0)]


noncomputable def «$PSA_setup_egress_user_meta_argument:clause:0» (input0 : arch) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ARCH : arch := input0; (.bind (.call ⟨(_root_.Option SpecTec.object), SpecTecCall.«$find_object_e» ARCH (["main"] : (_root_.List _root_.String))⟩) (fun («exec:1» : (_root_.Option SpecTec.object)) => (let «eval:0» : (_root_.Option SpecTec.object) := «exec:1»; (let object'? : (_root_.Option SpecTec.object) := «eval:0»; (.bind (.guard (((_root_.Option.isSome object'?) = true))) (fun (_ : Unit) => (match object'? with | some «exec:2» => (let object : SpecTec.object := «exec:2»; (.bind (.guard (((«sub:object:packageObject» object) = true))) (fun (_ : Unit) => (match («$PSA_setup_egress_user_meta_argument:case_1:downcast:1» object) with | some «exec:3» => (let «eval:1» : packageObject := «exec:3»; (match «eval:1» with | .«PACKAGE `< % `> `{ % `}» «exec:4» «exec:5» => (let theta : SpecTec.theta := «exec:4»; (let _frame : frame := «exec:5»; (.bind (.call ⟨(_root_.Option typeIR), SpecTecCall.«$find_map» typeId typeIR theta "EM"⟩) (fun («exec:6» : (_root_.Option typeIR)) => (let «eval:2» : (_root_.Option typeIR) := «exec:6»; (let typeIR? : (_root_.Option typeIR) := «eval:2»; (.bind (.guard (((_root_.Option.isSome typeIR?) = true))) (fun (_ : Unit) => (match typeIR? with | some «exec:7» => (let typeIR_user_meta : typeIR := «exec:7»; (let argumentIR_user_meta : argumentIR := ((argumentIR.«% '#' %» ((expressionIR.«'.' %» "egress_user_meta") : expressionIR) ((expressionNoteIR.«`( % % `)» typeIR_user_meta ((ctk.DYN) : ctk)) : expressionNoteIR)) : argumentIR); (.pure ((argumentIR_user_meta : argumentIR))))) | none => .unmatch))))))))))) | none => .unmatch)))) | none => .unmatch))))))))


noncomputable def «$PSA_setup_egress_user_meta_argument_clauses» (input0 : arch) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$PSA_setup_egress_user_meta_argument:clause:0»  input0)]


noncomputable def «Copy_in_default:rule:iter:3:clause:0» (input0 : (_root_.List parameterInitializerIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Copy_in_default:rule:iter:3:clause:1» (input0 : (_root_.List SpecTec.parameterInitializerIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterInitializerIR : SpecTec.parameterInitializerIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterInitializerIR) := «exec:1»; (.bind (.guard (((«sub:parameterInitializerIR:constantInitializerIR» parameterInitializerIR) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Copy_in_default:rule:iter:3» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Copy_in_default:rule:iter:3_clauses» (input0 : (_root_.List parameterInitializerIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:3:clause:1»  input0)]


noncomputable def «Copy_in_default:clause:0» (input0 : parameterListIR) (input1 : cursor) (input2 : evalContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameterIR*» : (_root_.List parameterIR) := input0; (let p_callee : cursor := input1; (let EC_callee_0 : evalContext := input2; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List typeIR) × ((_root_.List nameIR) × (_root_.List parameterInitializerOptIR))))), SpecTecCall.«Copy_in_default:rule:iter:0» «parameterIR*»⟩) (fun («exec:1» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List typeIR) × ((_root_.List nameIR) × (_root_.List parameterInitializerOptIR)))))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:1»).1; (let «_direction*» : (_root_.List direction) := ((«exec:1»).2).1; (let «_typeIR*» : (_root_.List typeIR) := (((«exec:1»).2).2).1; (let «nameIR*» : (_root_.List nameIR) := ((((«exec:1»).2).2).2).1; (let «parameterInitializerOptIR*» : (_root_.List parameterInitializerOptIR) := ((((«exec:1»).2).2).2).2; (.bind (.call ⟨_root_.Unit, SpecTecCall.«Copy_in_default:rule:iter:1» «parameterInitializerOptIR*»⟩) (fun («exec:2» : _root_.Unit) => (.bind (.call ⟨(_root_.List parameterInitializerIR), SpecTecCall.«Copy_in_default:rule:iter:2» «parameterInitializerOptIR*»⟩) (fun («exec:3» : (_root_.List parameterInitializerIR)) => (let «parameterInitializerIR*» : (_root_.List parameterInitializerIR) := «exec:3»; (.bind (.call ⟨_root_.Unit, SpecTecCall.«Copy_in_default:rule:iter:3» «parameterInitializerIR*»⟩) (fun («exec:4» : _root_.Unit) => (.bind (.call ⟨(_root_.List value), SpecTecCall.«Copy_in_default:rule:iter:4» «parameterInitializerIR*»⟩) (fun («exec:5» : (_root_.List value)) => (let «value*» : (_root_.List value) := «exec:5»; (.bind (.call ⟨(_root_.List prefixedNameIR), SpecTecCall.«Copy_in_default:rule:iter:6» «nameIR*»⟩) (fun («exec:6» : (_root_.List prefixedNameIR)) => (let «eval:7» : (_root_.List prefixedNameIR) := «exec:6»; (.bind (.call ⟨evalContext, SpecTecCall.«$add_vars_e» p_callee EC_callee_0 «eval:7» «value*»⟩) (fun («exec:7» : evalContext) => (let «eval:8» : evalContext := «exec:7»; (let EC_callee_1 : evalContext := «eval:8»; (.pure ((EC_callee_1 : evalContext))))))))))))))))))))))))))))))


noncomputable def Copy_in_default_clauses (input0 : parameterListIR) (input1 : cursor) (input2 : evalContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Copy_in_default:clause:0»  input0 input1 input2)]


noncomputable def «$flatten_parameterList:clause:0» (input0 : SpecTec.parameterList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parameterList : SpecTec.parameterList := input0; (.bind (.guard (((«exec:match:parameterList:_EMPTY» parameterList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List parameter)) : (_root_.List parameter)))))))


noncomputable def «$flatten_parameterList:clause:1» (input0 : SpecTec.parameterList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parameterList : SpecTec.parameterList := input0; (.bind (.guard (((«sub:parameterList:parameter» parameterList) = true))) (fun (_ : Unit) => (match («$flatten_parameterList:case_2:downcast:0» parameterList) with | some «exec:1» => (let «eval:0» : SpecTec.parameter := «exec:1»; (let parameter : SpecTec.parameter := «eval:0»; (.pure ((([parameter] : (_root_.List SpecTec.parameter)) : (_root_.List SpecTec.parameter)))))) | none => .unmatch))))


noncomputable def «$flatten_parameterList:clause:2» (input0 : SpecTec.parameterList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parameterList : SpecTec.parameterList := input0; (.bind (.guard (((«sub:parameterList:nonEmptyParameterList» parameterList) = true))) (fun (_ : Unit) => (match («$flatten_parameterList:case_3:downcast:0» parameterList) with | some «exec:1» => (let «eval:0» : SpecTec.nonEmptyParameterList := «exec:1»; (let nonEmptyParameterList' : SpecTec.nonEmptyParameterList := «eval:0»; (.bind (.guard (((«exec:match:nonEmptyParameterList:% ',' %» nonEmptyParameterList') = true))) (fun (_ : Unit) => (match nonEmptyParameterList' with | .«% ',' %» «exec:2» «exec:3» => (let nonEmptyParameterList : SpecTec.nonEmptyParameterList := «exec:2»; (let parameter : SpecTec.parameter := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.parameter), SpecTecCall.«$flatten_parameterList» («cast:nonEmptyParameterList:parameterList» nonEmptyParameterList)⟩) (fun («exec:4» : (_root_.List SpecTec.parameter)) => (let «eval:1» : (_root_.List SpecTec.parameter) := «exec:4»; (.pure (((«eval:1» ++ ([parameter] : (_root_.List SpecTec.parameter))) : (_root_.List SpecTec.parameter))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$flatten_parameterList_clauses» (input0 : parameterList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_parameterList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_parameterList:clause:1»  input0), fun (_ : _root_.Unit) => («$flatten_parameterList:clause:2»  input0)]


noncomputable def «$flatten_constructorParameterListOpt:clause:0» (input0 : SpecTec.constructorParameterListOpt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constructorParameterListOpt : SpecTec.constructorParameterListOpt := input0; (.bind (.guard (((«exec:match:constructorParameterListOpt:_EMPTY» constructorParameterListOpt) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List constructorParameter)) : (_root_.List constructorParameter)))))))


noncomputable def «$flatten_constructorParameterListOpt:clause:1» (input0 : SpecTec.constructorParameterListOpt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constructorParameterListOpt : SpecTec.constructorParameterListOpt := input0; (.bind (.guard (((«exec:match:constructorParameterListOpt:`( % `)» constructorParameterListOpt) = true))) (fun (_ : Unit) => (match constructorParameterListOpt with | .«`( % `)» «exec:1» => (let parameterList : SpecTec.parameterList := «exec:1»; (.bind (.call ⟨(_root_.List parameter), SpecTecCall.«$flatten_parameterList» parameterList⟩) (fun («exec:2» : (_root_.List parameter)) => (let «eval:0» : (_root_.List parameter) := «exec:2»; (.pure ((«eval:0» : (_root_.List constructorParameter)))))))) | _ => .unmatch))))


noncomputable def «$flatten_constructorParameterListOpt_clauses» (input0 : constructorParameterListOpt) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_constructorParameterListOpt:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_constructorParameterListOpt:clause:1»  input0)]


noncomputable def «$callableId':clause:0» (input0 : SpecTec.parameterList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parameterList : SpecTec.parameterList := input0; (.bind (.guard (((«exec:match:parameterList:_EMPTY» parameterList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List id)) : (_root_.List id)))))))


noncomputable def «$callableId':clause:1» (input0 : SpecTec.parameterList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parameterList : SpecTec.parameterList := input0; (.bind (.guard (((«sub:parameterList:parameter» parameterList) = true))) (fun (_ : Unit) => (match («$callableId':case_2:downcast:0» parameterList) with | some «exec:1» => (let «eval:0» : parameter := «exec:1»; (match «eval:0» with | .«% % % % %» «exec:2» «exec:3» «exec:4» «exec:5» «exec:6» => (let _annotationList : annotationList := «exec:2»; (let _direction : direction := «exec:3»; (let _type : type := «exec:4»; (let name : SpecTec.name := «exec:5»; (let _initializerOpt : initializerOpt := «exec:6»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» name⟩) (fun («exec:7» : nameIR) => (let «eval:1» : nameIR := «exec:7»; (.pure ((([«eval:1»] : (_root_.List id)) : (_root_.List id)))))))))))))) | none => .unmatch))))


noncomputable def «$callableId':clause:2» (input0 : SpecTec.parameterList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parameterList : SpecTec.parameterList := input0; (.bind (.guard (((«sub:parameterList:nonEmptyParameterList» parameterList) = true))) (fun (_ : Unit) => (match («$callableId':case_3:downcast:0» parameterList) with | some «exec:1» => (let «eval:0» : SpecTec.nonEmptyParameterList := «exec:1»; (let nonEmptyParameterList' : SpecTec.nonEmptyParameterList := «eval:0»; (.bind (.guard (((«exec:match:nonEmptyParameterList:% ',' %» nonEmptyParameterList') = true))) (fun (_ : Unit) => (match nonEmptyParameterList' with | .«% ',' %» «exec:2» «exec:3» => (let nonEmptyParameterList : SpecTec.nonEmptyParameterList := «exec:2»; (match «exec:3» with | .«% % % % %» «exec:4» «exec:5» «exec:6» «exec:7» «exec:8» => (let _annotationList : annotationList := «exec:4»; (let _direction : direction := «exec:5»; (let _type : type := «exec:6»; (let name : SpecTec.name := «exec:7»; (let _initializerOpt : initializerOpt := «exec:8»; (.bind (.call ⟨(_root_.List id), SpecTecCall.«$callableId'» («cast:nonEmptyParameterList:parameterList» nonEmptyParameterList)⟩) (fun («exec:9» : (_root_.List id)) => (let «eval:1» : (_root_.List id) := «exec:9»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» name⟩) (fun («exec:10» : nameIR) => (let «eval:2» : nameIR := «exec:10»; (.pure (((«eval:1» ++ ([«eval:2»] : (_root_.List nameIR))) : (_root_.List id))))))))))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$callableId'_clauses» (input0 : parameterList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callableId':clause:0»  input0), fun (_ : _root_.Unit) => («$callableId':clause:1»  input0), fun (_ : _root_.Unit) => («$callableId':clause:2»  input0)]


noncomputable def «$callableId:clause:0» (input0 : SpecTec.name) (input1 : SpecTec.parameterList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let name : SpecTec.name := input0; (let parameterList : SpecTec.parameterList := input1; (.bind (.call ⟨nameIR, SpecTecCall.«$name» name⟩) (fun («exec:1» : nameIR) => (let «eval:0» : nameIR := «exec:1»; (.bind (.call ⟨(_root_.List id), SpecTecCall.«$callableId'» parameterList⟩) (fun («exec:2» : (_root_.List id)) => (let «eval:1» : (_root_.List id) := «exec:2»; (.pure ((((callTargetId.«% `( % `)» «eval:0» «eval:1») : callTargetId) : callableId)))))))))))


noncomputable def «$callableId_clauses» (input0 : name) (input1 : parameterList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callableId:clause:0»  input0 input1)]


noncomputable def «$constructorId:clause:0» (input0 : SpecTec.name) (input1 : SpecTec.constructorParameterListOpt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let name : SpecTec.name := input0; (let constructorParameterListOpt : SpecTec.constructorParameterListOpt := input1; (.bind (.guard (((«exec:match:constructorParameterListOpt:_EMPTY» constructorParameterListOpt) = true))) (fun (_ : Unit) => (.bind (.call ⟨nameIR, SpecTecCall.«$name» name⟩) (fun («exec:1» : nameIR) => (let «eval:0» : nameIR := «exec:1»; (.pure ((((callTargetId.«% `( % `)» «eval:0» ([] : (_root_.List id))) : callTargetId) : constructorId))))))))))


noncomputable def «$constructorId:clause:1» (input0 : SpecTec.name) (input1 : SpecTec.constructorParameterListOpt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let name : SpecTec.name := input0; (let constructorParameterListOpt : SpecTec.constructorParameterListOpt := input1; (.bind (.guard (((«exec:match:constructorParameterListOpt:`( % `)» constructorParameterListOpt) = true))) (fun (_ : Unit) => (match constructorParameterListOpt with | .«`( % `)» «exec:1» => (let parameterList : SpecTec.parameterList := «exec:1»; (.bind (.call ⟨callableId, SpecTecCall.«$callableId» name parameterList⟩) (fun («exec:2» : callableId) => (let «eval:0» : callableId := «exec:2»; (.pure ((«eval:0» : constructorId))))))) | _ => .unmatch)))))


noncomputable def «$constructorId_clauses» (input0 : name) (input1 : constructorParameterListOpt) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$constructorId:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$constructorId:clause:1»  input0 input1)]


noncomputable def «$callableId_of_externMethodPrototype:clause:0» (input0 : SpecTec.externMethodPrototype) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodPrototype : SpecTec.externMethodPrototype := input0; (.bind (.guard (((«exec:match:externMethodPrototype:% % ';'» externMethodPrototype) = true))) (fun (_ : Unit) => (match externMethodPrototype with | .«% % ';'» «exec:1» «exec:2» => (let _annotationList : annotationList := «exec:1»; (match «exec:2» with | .«% % % `( % `)» «exec:3» «exec:4» «exec:5» «exec:6» => (let _typeOrVoid : typeOrVoid := «exec:3»; (let name : SpecTec.name := «exec:4»; (let _typeParameterListOpt : typeParameterListOpt := «exec:5»; (let parameterList : SpecTec.parameterList := «exec:6»; (.bind (.call ⟨callableId, SpecTecCall.«$callableId» name parameterList⟩) (fun («exec:7» : callableId) => (let «eval:0» : callableId := «exec:7»; (.pure ((«eval:0» : callableId)))))))))))) | _ => .unmatch))))


noncomputable def «$callableId_of_externMethodPrototype:clause:1» (input0 : SpecTec.externMethodPrototype) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodPrototype : SpecTec.externMethodPrototype := input0; (.bind (.guard (((«exec:match:externMethodPrototype:% ABSTRACT % ';'» externMethodPrototype) = true))) (fun (_ : Unit) => (match externMethodPrototype with | .«% ABSTRACT % ';'» «exec:1» «exec:2» => (let _annotationList : annotationList := «exec:1»; (match «exec:2» with | .«% % % `( % `)» «exec:3» «exec:4» «exec:5» «exec:6» => (let _typeOrVoid : typeOrVoid := «exec:3»; (let name : SpecTec.name := «exec:4»; (let _typeParameterListOpt : typeParameterListOpt := «exec:5»; (let parameterList : SpecTec.parameterList := «exec:6»; (.bind (.call ⟨callableId, SpecTecCall.«$callableId» name parameterList⟩) (fun («exec:7» : callableId) => (let «eval:0» : callableId := «exec:7»; (.pure ((«eval:0» : callableId)))))))))))) | _ => .unmatch))))


noncomputable def «$callableId_of_externMethodPrototype_clauses» (input0 : externMethodPrototype) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callableId_of_externMethodPrototype:clause:0»  input0), fun (_ : _root_.Unit) => («$callableId_of_externMethodPrototype:clause:1»  input0)]


noncomputable def «$constructorId_of_externConstructorPrototype:clause:0» (input0 : externConstructorPrototype) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % `( % `) ';'» «exec:1» «exec:2» «exec:3» => (let _annotationList : annotationList := «exec:1»; (let typeIdentifier : SpecTec.typeIdentifier := «exec:2»; (let parameterList : SpecTec.parameterList := «exec:3»; (.bind (.call ⟨callableId, SpecTecCall.«$callableId» («cast:typeIdentifier:name» typeIdentifier) parameterList⟩) (fun («exec:4» : callableId) => (let «eval:0» : callableId := «exec:4»; (.pure ((«eval:0» : constructorId))))))))))


noncomputable def «$constructorId_of_externConstructorPrototype_clauses» (input0 : externConstructorPrototype) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$constructorId_of_externConstructorPrototype:clause:0»  input0)]


noncomputable def «Decl_ok:externObjectDeclaration:iter:4:clause:0» (input0 : (_root_.List externMethodPrototype)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List callableId)) : (_root_.List callableId)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:externObjectDeclaration:iter:4:clause:1» (input0 : (_root_.List SpecTec.externMethodPrototype)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externMethodPrototype : SpecTec.externMethodPrototype := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externMethodPrototype) := «exec:1»; (.bind (.call ⟨callableId, SpecTecCall.«$callableId_of_externMethodPrototype» externMethodPrototype⟩) (fun («exec:3» : callableId) => (let «eval:5» : callableId := «exec:3»; (let callableId_method : callableId := «eval:5»; (.bind (.call ⟨(_root_.List callableId), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List callableId)) => (let «tail:1» : (_root_.List callableId) := «exec:4»; (.pure (((callableId_method :: «tail:1») : (_root_.List callableId))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:externObjectDeclaration:iter:4_clauses» (input0 : (_root_.List externMethodPrototype)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:externObjectDeclaration:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:externObjectDeclaration:iter:4:clause:1»  input0)]

end SpecTec
