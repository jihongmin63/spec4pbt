import SpecTecDecl0235

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_typeParameterListIR:case_1:iter:0:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeParameter)) : (_root_.List typeParameter)))) | _ :: _ => .unmatch)


noncomputable def «$lift_typeParameterListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeParameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.typeParameter, SpecTecCall.«$lift_typeParameterIR» typeParameterIR⟩) (fun («exec:3» : SpecTec.typeParameter) => (let «eval:1» : SpecTec.typeParameter := «exec:3»; (let typeParameter : SpecTec.typeParameter := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.typeParameter), SpecTecCall.«$lift_typeParameterListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeParameter)) => (let «tail:1» : (_root_.List SpecTec.typeParameter) := «exec:4»; (.pure (((typeParameter :: «tail:1») : (_root_.List SpecTec.typeParameter))))))))))))) | [] => .unmatch)


noncomputable def «$lift_typeParameterListIR:case_1:iter:0_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeParameterListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typeParameterListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_typeParameterListIR:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeParameterIR*» : (_root_.List typeParameterIR) := input0; (.bind (.call ⟨(_root_.List typeParameter), SpecTecCall.«$lift_typeParameterListIR:case_1:iter:0» «typeParameterIR*»⟩) (fun («exec:1» : (_root_.List typeParameter)) => (let «typeParameter*» : (_root_.List typeParameter) := «exec:1»; (.bind (.call ⟨SpecTec.typeParameterListOpt, SpecTecCall.«$unflatten_typeParameterListOpt» «typeParameter*»⟩) (fun («exec:2» : SpecTec.typeParameterListOpt) => (let «eval:2» : SpecTec.typeParameterListOpt := «exec:2»; (let typeParameterListOpt : SpecTec.typeParameterListOpt := «eval:2»; (.pure ((typeParameterListOpt : SpecTec.typeParameterListOpt)))))))))))


noncomputable def «$lift_typeParameterListIR_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeParameterListIR:clause:0»  input0)]


noncomputable def «$lift_nameTypeIR:clause:0» (input0 : nameTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | ._NAME «exec:1» => (let typeId : SpecTec.typeId := «exec:1»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:2» : SpecTec.typeName) => (let «eval:0» : SpecTec.typeName := «exec:2»; (let typeName : SpecTec.typeName := «eval:0»; (.pure (((«cast:typeIdentifier:namedType» typeName) : namedType)))))))))


noncomputable def «$lift_nameTypeIR_clauses» (input0 : nameTypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_nameTypeIR:clause:0»  input0)]


noncomputable def «$optional_annotation_of_parameterIR'':clause:0» (input0 : SpecTec.annotation) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let annotation : SpecTec.annotation := input0; (.bind (.guard (((«exec:match:annotation:'@' %» annotation) = true))) (fun (_ : Unit) => (match annotation with | .«'@' %» «exec:1» => (let name : SpecTec.name := «exec:1»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» name⟩) (fun («exec:2» : nameIR) => (let «eval:0» : nameIR := «exec:2»; (.bind (.guard («eval:0» = "optional")) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))) | _ => .unmatch))))


noncomputable def «$optional_annotation_of_parameterIR'':clause:1» (input0 : SpecTec.annotation) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let annotation : SpecTec.annotation := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$optional_annotation_of_parameterIR''_clauses» (input0 : annotation) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$optional_annotation_of_parameterIR'':clause:0»  input0), fun (_ : _root_.Unit) => («$optional_annotation_of_parameterIR'':clause:1»  input0)]


noncomputable def «$optional_annotation_of_parameterIR':case_1:iter:1:clause:0» (input0 : (_root_.List annotation)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$optional_annotation_of_parameterIR':case_1:iter:1:clause:1» (input0 : (_root_.List SpecTec.annotation)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotation : SpecTec.annotation := «exec:2»; (let «tail:0» : (_root_.List SpecTec.annotation) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$optional_annotation_of_parameterIR''» annotation⟩) (fun («exec:3» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:3»; (let b : _root_.Bool := «eval:2»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$optional_annotation_of_parameterIR':case_1:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((b :: «tail:1») : (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$optional_annotation_of_parameterIR':case_1:iter:1_clauses» (input0 : (_root_.List annotation)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$optional_annotation_of_parameterIR':case_1:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$optional_annotation_of_parameterIR':case_1:iter:1:clause:1»  input0)]


noncomputable def «$name_annotation_opt:clause:0» (input0 : SpecTec.annotation) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let annotation : SpecTec.annotation := input0; (.bind (.guard (((«exec:match:annotation:'@' % `( % `)» annotation) = true))) (fun (_ : Unit) => (match annotation with | .«'@' % `( % `)» «exec:1» «exec:2» => (let name : SpecTec.name := «exec:1»; (let annotationBody : SpecTec.annotationBody := «exec:2»; (.bind (.call ⟨SpecTec.nameIR, SpecTecCall.«$name» name⟩) (fun («exec:3» : SpecTec.nameIR) => (let «eval:0» : SpecTec.nameIR := «exec:3»; (.bind (.guard («eval:0» = "name")) (fun (_ : Unit) => (let annotationBody'' : SpecTec.annotationBody := annotationBody; (.bind (.guard (((«exec:match:annotationBody:% %» annotationBody'') = true))) (fun (_ : Unit) => (match annotationBody'' with | .«% %» «exec:4» «exec:5» => (let annotationBody' : SpecTec.annotationBody := «exec:4»; (let annotationToken : SpecTec.annotationToken := «exec:5»; (.bind (.guard (((«exec:match:annotationBody:_EMPTY» annotationBody') = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.String, SpecTecCall.«$print_» SpecTec.annotationToken annotationToken⟩) (fun («exec:6» : _root_.String) => (let «eval:1» : _root_.String := «exec:6»; (let nameIR : SpecTec.nameIR := «eval:1»; (.bind (.call ⟨_root_.String, SpecTecCall.«$strip_suffix» nameIR "\""⟩) (fun («exec:7» : _root_.String) => (let «eval:2» : _root_.String := «exec:7»; (.bind (.call ⟨_root_.String, SpecTecCall.«$strip_prefix» «eval:2» "\""⟩) (fun («exec:8» : _root_.String) => (let «eval:3» : _root_.String := «exec:8»; (.pure (((_root_.Option.some «eval:3») : (_root_.Option SpecTec.nameIR)))))))))))))))))) | _ => .unmatch))))))))))) | _ => .unmatch))))


noncomputable def «$name_annotation_opt:clause:1» (input0 : SpecTec.annotation) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let annotation : SpecTec.annotation := input0; (.pure ((((_root_.Option.none) : (_root_.Option nameIR)) : (_root_.Option nameIR)))))


noncomputable def «$name_annotation_opt_clauses» (input0 : annotation) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$name_annotation_opt:clause:0»  input0), fun (_ : _root_.Unit) => («$name_annotation_opt:clause:1»  input0)]


noncomputable def «$name_annotation:case_1:iter:1:clause:0» (input0 : (_root_.List annotation)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.Option nameIR))) : (_root_.List (_root_.Option nameIR))))) | _ :: _ => .unmatch)


noncomputable def «$name_annotation:case_1:iter:1:clause:1» (input0 : (_root_.List SpecTec.annotation)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotation : SpecTec.annotation := «exec:2»; (let «tail:0» : (_root_.List SpecTec.annotation) := «exec:1»; (.bind (.call ⟨(_root_.Option nameIR), SpecTecCall.«$name_annotation_opt» annotation⟩) (fun («exec:3» : (_root_.Option nameIR)) => (let «eval:2» : (_root_.Option nameIR) := «exec:3»; (let nameIR_opt? : (_root_.Option nameIR) := «eval:2»; (.bind (.call ⟨(_root_.List (_root_.Option nameIR)), SpecTecCall.«$name_annotation:case_1:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.Option nameIR))) => (let «tail:1» : (_root_.List (_root_.Option nameIR)) := «exec:4»; (.pure (((nameIR_opt? :: «tail:1») : (_root_.List (_root_.Option nameIR)))))))))))))) | [] => .unmatch)


noncomputable def «$name_annotation:case_1:iter:1_clauses» (input0 : (_root_.List annotation)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$name_annotation:case_1:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$name_annotation:case_1:iter:1:clause:1»  input0)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:4:clause:0» (input0 : (_root_.List annotation)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.Option nameIR))) : (_root_.List (_root_.Option nameIR))))) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:4:clause:1» (input0 : (_root_.List SpecTec.annotation)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotation : SpecTec.annotation := «exec:2»; (let «tail:0» : (_root_.List SpecTec.annotation) := «exec:1»; (.bind (.call ⟨(_root_.Option nameIR), SpecTecCall.«$name_annotation_opt» annotation⟩) (fun («exec:3» : (_root_.Option nameIR)) => (let «eval:5» : (_root_.Option nameIR) := «exec:3»; (let nameIR_names_opt? : (_root_.Option nameIR) := «eval:5»; (.bind (.call ⟨(_root_.List (_root_.Option nameIR)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.Option nameIR))) => (let «tail:1» : (_root_.List (_root_.Option nameIR)) := «exec:4»; (.pure (((nameIR_names_opt? :: «tail:1») : (_root_.List (_root_.Option nameIR)))))))))))))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:4_clauses» (input0 : (_root_.List annotation)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:4:clause:1»  input0)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:3:clause:0» (input0 : (_root_.List (_root_.List annotation))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List (_root_.Option nameIR)))) : (_root_.List (_root_.List (_root_.Option nameIR)))))) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:3:clause:1» (input0 : (_root_.List (_root_.List annotation))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «annotation*» : (_root_.List annotation) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List annotation)) := «exec:1»; (.bind (.call ⟨(_root_.List (_root_.Option nameIR)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:4» «annotation*»⟩) (fun («exec:3» : (_root_.List (_root_.Option nameIR))) => (let «nameIR_names_opt?*» : (_root_.List (_root_.Option nameIR)) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List (_root_.Option nameIR))), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List (_root_.Option nameIR)))) => (let «tail:1» : (_root_.List (_root_.List (_root_.Option nameIR))) := «exec:4»; (.pure (((«nameIR_names_opt?*» :: «tail:1») : (_root_.List (_root_.List (_root_.Option nameIR)))))))))))))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:3_clauses» (input0 : (_root_.List (_root_.List annotation))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:3:clause:1»  input0)]


noncomputable def «$assignop_as_binop:clause:0» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'+='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'+'») : binop)) : (_root_.Option binop)))))))


noncomputable def «$assignop_as_binop:clause:1» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'-='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'-'») : binop)) : (_root_.Option binop)))))))


noncomputable def «$assignop_as_binop:clause:2» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'|+|='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'|+|'») : binop)) : (_root_.Option binop)))))))


noncomputable def «$assignop_as_binop:clause:3» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'|-|='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'|-|'») : binop)) : (_root_.Option binop)))))))


noncomputable def «$assignop_as_binop:clause:4» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'*='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'*'») : binop)) : (_root_.Option binop)))))))


noncomputable def «$assignop_as_binop:clause:5» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'/='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'/'») : binop)) : (_root_.Option binop)))))))


noncomputable def «$assignop_as_binop:clause:6» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'%='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'%'») : binop)) : (_root_.Option binop)))))))

end SpecTec
