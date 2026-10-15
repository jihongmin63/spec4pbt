import SpecTecDecl0303

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_typeIR_as_typeOrVoid:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:voidTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$lift_typeIR_as_typeOrVoid:case_1:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.voidTypeIR := «exec:1»; (let voidTypeIR : SpecTec.voidTypeIR := «eval:0»; (.bind (.guard (((SpecTec.voidTypeIR.VOID) : SpecTec.voidTypeIR) = voidTypeIR)) (fun (_ : Unit) => (.pure ((((typeOrVoid.VOID) : typeOrVoid) : typeOrVoid))))))) | none => .unmatch))))


noncomputable def «$lift_typeIR_as_typeOrVoid:clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard ((typeIR ≠ ((SpecTec.typeIR.VOID) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:1» : type) => (let «eval:0» : type := «exec:1»; (.pure (((«cast:type:typeOrVoid» «eval:0») : typeOrVoid)))))))))


noncomputable def «$lift_typeIR_as_typeOrVoid_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeIR_as_typeOrVoid:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typeIR_as_typeOrVoid:clause:1»  input0)]


noncomputable def «$lift_parameterIR:clause:0» (input0 : parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % % % %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:1»; (let direction : SpecTec.direction := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (let nameIR : SpecTec.nameIR := «exec:4»; (let parameterInitializerOptIR : SpecTec.parameterInitializerOptIR := «exec:5»; (.bind (.guard (((_root_.Option.all (fun («sub:item» : parameterInitializerIR) => («sub:parameterInitializerIR:constantInitializerIR» «sub:item»)) parameterInitializerOptIR) = true))) (fun (_ : Unit) => (match (_root_.Option.mapM (fun («$lift_parameterIR:case_1:downcast:0:item» : parameterInitializerIR) => («$lift_parameterIR:case_1:downcast:0:0» «$lift_parameterIR:case_1:downcast:0:item»)) parameterInitializerOptIR) with | some «exec:6» => (let «eval:0» : (_root_.Option constantInitializerIR) := «exec:6»; (let constantInitializerIR? : (_root_.Option constantInitializerIR) := «eval:0»; (.bind (.call ⟨SpecTec.type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:7» : SpecTec.type) => (let «eval:1» : SpecTec.type := «exec:7»; (let type : SpecTec.type := «eval:1»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:8» : nonTypeName) => (let «eval:2» : nonTypeName := «exec:8»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:2»); (.bind (.call ⟨SpecTec.initializerOpt, SpecTecCall.«$lift_constantInitializerOptIR_as_initializerOpt» constantInitializerIR?⟩) (fun («exec:9» : SpecTec.initializerOpt) => (let «eval:3» : SpecTec.initializerOpt := «exec:9»; (let initializerOpt : SpecTec.initializerOpt := «eval:3»; (.pure ((((parameter.«% % % % %» annotationList direction type name initializerOpt) : parameter) : parameter))))))))))))))))) | none => .unmatch)))))))))


noncomputable def «$lift_parameterIR_clauses» (input0 : parameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parameterIR:clause:0»  input0)]


noncomputable def «$lift_parameterListIR:case_1:iter:0:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List parameter)) : (_root_.List parameter)))) | _ :: _ => .unmatch)


noncomputable def «$lift_parameterListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.parameter, SpecTecCall.«$lift_parameterIR» parameterIR⟩) (fun («exec:3» : SpecTec.parameter) => (let «eval:1» : SpecTec.parameter := «exec:3»; (let parameter : SpecTec.parameter := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.parameter), SpecTecCall.«$lift_parameterListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parameter)) => (let «tail:1» : (_root_.List SpecTec.parameter) := «exec:4»; (.pure (((parameter :: «tail:1») : (_root_.List SpecTec.parameter))))))))))))) | [] => .unmatch)


noncomputable def «$lift_parameterListIR:case_1:iter:0_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parameterListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_parameterListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_parameterListIR:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameterIR*» : (_root_.List parameterIR) := input0; (.bind (.call ⟨(_root_.List parameter), SpecTecCall.«$lift_parameterListIR:case_1:iter:0» «parameterIR*»⟩) (fun («exec:1» : (_root_.List parameter)) => (let «parameter*» : (_root_.List parameter) := «exec:1»; (.bind (.call ⟨SpecTec.parameterList, SpecTecCall.«$unflatten_parameterList» «parameter*»⟩) (fun («exec:2» : SpecTec.parameterList) => (let «eval:2» : SpecTec.parameterList := «exec:2»; (let parameterList : SpecTec.parameterList := «eval:2»; (.pure ((parameterList : SpecTec.parameterList)))))))))))


noncomputable def «$lift_parameterListIR_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parameterListIR:clause:0»  input0)]


noncomputable def «$lift_constructorParameterIR:clause:0» (input0 : SpecTec.constructorParameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constructorParameterIR : SpecTec.constructorParameterIR := input0; (.bind (.call ⟨parameter, SpecTecCall.«$lift_parameterIR» constructorParameterIR⟩) (fun («exec:1» : parameter) => (let «eval:0» : parameter := «exec:1»; (.pure ((«eval:0» : constructorParameter)))))))


noncomputable def «$lift_constructorParameterIR_clauses» (input0 : constructorParameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_constructorParameterIR:clause:0»  input0)]


noncomputable def «$lift_constructorParameterListIR:case_1:iter:0:clause:0» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List constructorParameter)) : (_root_.List constructorParameter)))) | _ :: _ => .unmatch)


noncomputable def «$lift_constructorParameterListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let constructorParameterIR : SpecTec.constructorParameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.constructorParameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.constructorParameter, SpecTecCall.«$lift_constructorParameterIR» constructorParameterIR⟩) (fun («exec:3» : SpecTec.constructorParameter) => (let «eval:1» : SpecTec.constructorParameter := «exec:3»; (let constructorParameter : SpecTec.constructorParameter := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.constructorParameter), SpecTecCall.«$lift_constructorParameterListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.constructorParameter)) => (let «tail:1» : (_root_.List SpecTec.constructorParameter) := «exec:4»; (.pure (((constructorParameter :: «tail:1») : (_root_.List SpecTec.constructorParameter))))))))))))) | [] => .unmatch)


noncomputable def «$lift_constructorParameterListIR:case_1:iter:0_clauses» (input0 : (_root_.List constructorParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_constructorParameterListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_constructorParameterListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_constructorParameterListIR:clause:0» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «constructorParameterIR*» : (_root_.List constructorParameterIR) := input0; (.bind (.call ⟨(_root_.List constructorParameter), SpecTecCall.«$lift_constructorParameterListIR:case_1:iter:0» «constructorParameterIR*»⟩) (fun («exec:1» : (_root_.List constructorParameter)) => (let «constructorParameter*» : (_root_.List constructorParameter) := «exec:1»; (.bind (.call ⟨SpecTec.constructorParameterListOpt, SpecTecCall.«$unflatten_constructorParameterList» «constructorParameter*»⟩) (fun («exec:2» : SpecTec.constructorParameterListOpt) => (let «eval:2» : SpecTec.constructorParameterListOpt := «exec:2»; (let constructorParameterListOpt : SpecTec.constructorParameterListOpt := «eval:2»; (.pure ((constructorParameterListOpt : SpecTec.constructorParameterListOpt)))))))))))


noncomputable def «$lift_constructorParameterListIR_clauses» (input0 : (_root_.List constructorParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_constructorParameterListIR:clause:0»  input0)]


noncomputable def «$lift_typeArgumentListIR_as_realTypeArgumentList:case_1:iter:0:clause:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List realTypeArgument)) : (_root_.List realTypeArgument)))) | _ :: _ => .unmatch)


noncomputable def «$lift_typeArgumentListIR_as_realTypeArgumentList:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨SpecTec.realTypeArgument, SpecTecCall.«$lift_typeArgumentIR_as_realTypeArgument» typeArgumentIR⟩) (fun («exec:3» : SpecTec.realTypeArgument) => (let «eval:1» : SpecTec.realTypeArgument := «exec:3»; (let realTypeArgument : SpecTec.realTypeArgument := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.realTypeArgument), SpecTecCall.«$lift_typeArgumentListIR_as_realTypeArgumentList:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.realTypeArgument)) => (let «tail:1» : (_root_.List SpecTec.realTypeArgument) := «exec:4»; (.pure (((realTypeArgument :: «tail:1») : (_root_.List SpecTec.realTypeArgument))))))))))))) | [] => .unmatch)


noncomputable def «$lift_typeArgumentListIR_as_realTypeArgumentList:case_1:iter:0_clauses» (input0 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeArgumentListIR_as_realTypeArgumentList:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typeArgumentListIR_as_realTypeArgumentList:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_typeArgumentListIR_as_realTypeArgumentList:clause:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeArgumentIR*» : (_root_.List typeArgumentIR) := input0; (.bind (.call ⟨(_root_.List realTypeArgument), SpecTecCall.«$lift_typeArgumentListIR_as_realTypeArgumentList:case_1:iter:0» «typeArgumentIR*»⟩) (fun («exec:1» : (_root_.List realTypeArgument)) => (let «realTypeArgument*» : (_root_.List realTypeArgument) := «exec:1»; (.bind (.call ⟨SpecTec.realTypeArgumentList, SpecTecCall.«$unflatten_realTypeArgumentList» «realTypeArgument*»⟩) (fun («exec:2» : SpecTec.realTypeArgumentList) => (let «eval:2» : SpecTec.realTypeArgumentList := «exec:2»; (let realTypeArgumentList : SpecTec.realTypeArgumentList := «eval:2»; (.pure ((realTypeArgumentList : SpecTec.realTypeArgumentList)))))))))))


noncomputable def «$lift_typeArgumentListIR_as_realTypeArgumentList_clauses» (input0 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeArgumentListIR_as_realTypeArgumentList:clause:0»  input0)]


noncomputable def «$lift_typedExpressionIR:clause:0» (input0 : typedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% '#' %» «exec:1» «exec:2» => (let expressionIR : SpecTec.expressionIR := «exec:1»; (let _expressionNoteIR : expressionNoteIR := «exec:2»; (.bind (.call ⟨expression, SpecTecCall.«$lift_expressionIR» expressionIR⟩) (fun («exec:3» : expression) => (let «eval:0» : expression := «exec:3»; (.pure ((«eval:0» : expression)))))))))


noncomputable def «$lift_typedExpressionIR_clauses» (input0 : typedExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typedExpressionIR:clause:0»  input0)]


noncomputable def «$lift_namedExpressionIR:clause:0» (input0 : namedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% '=' %» «exec:1» «exec:2» => (let nameIR : SpecTec.nameIR := «exec:1»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:2»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:3» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:3»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:4» : SpecTec.expression) => (let «eval:1» : SpecTec.expression := «exec:4»; (let expression : SpecTec.expression := «eval:1»; (.pure ((((namedExpression.«% '=' %» name expression) : namedExpression) : namedExpression))))))))))))))


noncomputable def «$lift_namedExpressionIR_clauses» (input0 : namedExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_namedExpressionIR:clause:0»  input0)]


noncomputable def «$lift_typedExpressionListIR:clause:0» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typedExpressionIR*» : (_root_.List typedExpressionIR) := input0; (.bind (.call ⟨(_root_.List expression), SpecTecCall.«$lift_typedExpressionListIR:case_1:iter:0» «typedExpressionIR*»⟩) (fun («exec:1» : (_root_.List expression)) => (let «expression*» : (_root_.List expression) := «exec:1»; (.bind (.call ⟨SpecTec.expressionList, SpecTecCall.«$unflatten_expressionList» «expression*»⟩) (fun («exec:2» : SpecTec.expressionList) => (let «eval:2» : SpecTec.expressionList := «exec:2»; (let expressionList : SpecTec.expressionList := «eval:2»; (.pure ((expressionList : SpecTec.expressionList)))))))))))


noncomputable def «$lift_typedExpressionListIR_clauses» (input0 : (_root_.List typedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typedExpressionListIR:clause:0»  input0)]


noncomputable def «$lift_typedExpressionListIR:case_1:iter:0:clause:0» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List expression)) : (_root_.List expression)))) | _ :: _ => .unmatch)


noncomputable def «$lift_typedExpressionListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typedExpressionIR) := «exec:1»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:3» : SpecTec.expression) => (let «eval:1» : SpecTec.expression := «exec:3»; (let expression : SpecTec.expression := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.expression), SpecTecCall.«$lift_typedExpressionListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.expression)) => (let «tail:1» : (_root_.List SpecTec.expression) := «exec:4»; (.pure (((expression :: «tail:1») : (_root_.List SpecTec.expression))))))))))))) | [] => .unmatch)


noncomputable def «$lift_typedExpressionListIR:case_1:iter:0_clauses» (input0 : (_root_.List typedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typedExpressionListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typedExpressionListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_unaryExpressionIR:clause:0» (input0 : unaryExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% %» «exec:1» «exec:2» => (let unop : SpecTec.unop := «exec:1»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:2»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:3» : SpecTec.expression) => (let «eval:0» : SpecTec.expression := «exec:3»; (let expression : SpecTec.expression := «eval:0»; (.pure ((((unaryExpression.«% %» unop expression) : unaryExpression) : unaryExpression))))))))))

end SpecTec
