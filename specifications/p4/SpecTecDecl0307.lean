import SpecTecDecl0306

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_expressionIR:clause:6» (input0 : SpecTec.expressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionIR : SpecTec.expressionIR := input0; (.bind (.guard (((«sub:expressionIR:castExpressionIR» expressionIR) = true))) (fun (_ : Unit) => (match («$lift_expressionIR:case_7:downcast:0» expressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.castExpressionIR := «exec:1»; (let castExpressionIR : SpecTec.castExpressionIR := «eval:0»; (.bind (.call ⟨expression, SpecTecCall.«$lift_castExpressionIR» castExpressionIR⟩) (fun («exec:2» : expression) => (let «eval:1» : expression := «exec:2»; (.pure ((«eval:1» : expression)))))))) | none => .unmatch))))


noncomputable def «$lift_expressionIR:clause:7» (input0 : SpecTec.expressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionIR : SpecTec.expressionIR := input0; (.bind (.guard (((«sub:expressionIR:dataExpressionIR» expressionIR) = true))) (fun (_ : Unit) => (match («$lift_expressionIR:case_8:downcast:0» expressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.dataExpressionIR := «exec:1»; (let dataExpressionIR : SpecTec.dataExpressionIR := «eval:0»; (.bind (.call ⟨dataExpression, SpecTecCall.«$lift_dataExpressionIR» dataExpressionIR⟩) (fun («exec:2» : dataExpression) => (let «eval:1» : dataExpression := «exec:2»; (.pure (((«cast:dataExpression:expression» «eval:1») : expression)))))))) | none => .unmatch))))


noncomputable def «$lift_expressionIR:clause:8» (input0 : SpecTec.expressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionIR : SpecTec.expressionIR := input0; (.bind (.guard (((«sub:expressionIR:accessExpressionIR» expressionIR) = true))) (fun (_ : Unit) => (match («$lift_expressionIR:case_9:downcast:0» expressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.accessExpressionIR := «exec:1»; (let accessExpressionIR : SpecTec.accessExpressionIR := «eval:0»; (.bind (.call ⟨accessExpression, SpecTecCall.«$lift_accessExpressionIR» accessExpressionIR⟩) (fun («exec:2» : accessExpression) => (let «eval:1» : accessExpression := «exec:2»; (.pure (((«cast:accessExpression:expression» «eval:1») : expression)))))))) | none => .unmatch))))


noncomputable def «$lift_expressionIR:clause:9» (input0 : SpecTec.expressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionIR : SpecTec.expressionIR := input0; (.bind (.guard (((«sub:expressionIR:callExpressionIR» expressionIR) = true))) (fun (_ : Unit) => (match («$lift_expressionIR:case_10:downcast:0» expressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.callExpressionIR := «exec:1»; (let callExpressionIR : SpecTec.callExpressionIR := «eval:0»; (.bind (.call ⟨callExpression, SpecTecCall.«$lift_callExpressionIR» callExpressionIR⟩) (fun («exec:2» : callExpression) => (let «eval:1» : callExpression := «exec:2»; (.pure (((«cast:callExpression:expression» «eval:1») : expression)))))))) | none => .unmatch))))


noncomputable def «$lift_expressionIR:clause:10» (input0 : SpecTec.expressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionIR : SpecTec.expressionIR := input0; (.bind (.guard (((«sub:expressionIR:parenthesizedExpressionIR» expressionIR) = true))) (fun (_ : Unit) => (match («$lift_expressionIR:case_11:downcast:0» expressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.parenthesizedExpressionIR := «exec:1»; (let parenthesizedExpressionIR : SpecTec.parenthesizedExpressionIR := «eval:0»; (.bind (.call ⟨parenthesizedExpression, SpecTecCall.«$lift_parenthesizedExpressionIR» parenthesizedExpressionIR⟩) (fun («exec:2» : parenthesizedExpression) => (let «eval:1» : parenthesizedExpression := «exec:2»; (.pure (((«cast:parenthesizedExpression:expression» «eval:1») : expression)))))))) | none => .unmatch))))


noncomputable def «$lift_expressionIR_clauses» (input0 : expressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_expressionIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_expressionIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_expressionIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_expressionIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_expressionIR:clause:4»  input0), fun (_ : _root_.Unit) => («$lift_expressionIR:clause:5»  input0), fun (_ : _root_.Unit) => («$lift_expressionIR:clause:6»  input0), fun (_ : _root_.Unit) => («$lift_expressionIR:clause:7»  input0), fun (_ : _root_.Unit) => («$lift_expressionIR:clause:8»  input0), fun (_ : _root_.Unit) => («$lift_expressionIR:clause:9»  input0), fun (_ : _root_.Unit) => («$lift_expressionIR:clause:10»  input0)]


noncomputable def «$lift_argumentIR:clause:0» (input0 : SpecTec.argumentIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentIR : SpecTec.argumentIR := input0; (.bind (.guard (((«sub:argumentIR:typedExpressionIR» argumentIR) = true))) (fun (_ : Unit) => (match («$lift_argumentIR:case_1:downcast:0» argumentIR) with | some «exec:1» => (let «eval:0» : SpecTec.typedExpressionIR := «exec:1»; (let typedExpressionIR : SpecTec.typedExpressionIR := «eval:0»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:2» : SpecTec.expression) => (let «eval:1» : SpecTec.expression := «exec:2»; (let expression : SpecTec.expression := «eval:1»; (.pure (((«cast:expression:argument» expression) : argument))))))))) | none => .unmatch))))


noncomputable def «$lift_argumentIR:clause:1» (input0 : SpecTec.argumentIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentIR : SpecTec.argumentIR := input0; (.bind (.guard (((«exec:match:argumentIR:% '=' %» argumentIR) = true))) (fun (_ : Unit) => (match argumentIR with | .«% '=' %» «exec:1» «exec:2» => (let nameIR : SpecTec.nameIR := «exec:1»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:2»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:3» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:3»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:4» : SpecTec.expression) => (let «eval:1» : SpecTec.expression := «exec:4»; (let expression : SpecTec.expression := «eval:1»; (.pure ((((argument.«% '=' %» name expression) : argument) : argument))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_argumentIR:clause:2» (input0 : SpecTec.argumentIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentIR : SpecTec.argumentIR := input0; (.bind (.guard (((«exec:match:argumentIR:% '=' '_'» argumentIR) = true))) (fun (_ : Unit) => (match argumentIR with | .«% '=' '_'» «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:2» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:2»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (.pure ((((argument.«% '=' '_'» name) : argument) : argument)))))))) | _ => .unmatch))))


noncomputable def «$lift_argumentIR:clause:3» (input0 : SpecTec.argumentIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentIR : SpecTec.argumentIR := input0; (.bind (.guard (((«exec:match:argumentIR:'_'» argumentIR) = true))) (fun (_ : Unit) => (.pure ((((argument.«'_'») : argument) : argument))))))


noncomputable def «$lift_argumentIR_clauses» (input0 : argumentIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_argumentIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_argumentIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_argumentIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_argumentIR:clause:3»  input0)]


noncomputable def «$lift_initializerIR:clause:0» (input0 : initializerIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«'=' %» «exec:1» => (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:1»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:2» : SpecTec.expression) => (let «eval:0» : SpecTec.expression := «exec:2»; (let expression : SpecTec.expression := «eval:0»; (.pure ((((initializer.«'=' %» expression) : initializer) : initializer)))))))))


noncomputable def «$lift_initializerIR_clauses» (input0 : initializerIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_initializerIR:clause:0»  input0)]


noncomputable def «$lift_initializerOptIR:clause:0» (input0 : (_root_.Option initializerIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let initializerIR? : (_root_.Option initializerIR) := input0; (.bind (.guard (((_root_.Option.isNone initializerIR?) = true))) (fun (_ : Unit) => (.pure ((((initializerOpt._EMPTY) : initializerOpt) : initializerOpt))))))


noncomputable def «$lift_initializerOptIR:clause:1» (input0 : (_root_.Option SpecTec.initializerIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let initializerIR'? : (_root_.Option SpecTec.initializerIR) := input0; (.bind (.guard (((_root_.Option.isSome initializerIR'?) = true))) (fun (_ : Unit) => (match initializerIR'? with | some «exec:1» => (let initializerIR : SpecTec.initializerIR := «exec:1»; (.bind (.call ⟨initializer, SpecTecCall.«$lift_initializerIR» initializerIR⟩) (fun («exec:2» : initializer) => (let «eval:0» : initializer := «exec:2»; (.pure (((«cast:initializer:initializerOpt» «eval:0») : initializerOpt))))))) | none => .unmatch))))


noncomputable def «$lift_initializerOptIR_clauses» (input0 : (_root_.Option initializerIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_initializerOptIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_initializerOptIR:clause:1»  input0)]


noncomputable def «$lift_namedExpressionListIR:case_1:iter:0:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List namedExpression)) : (_root_.List namedExpression)))) | _ :: _ => .unmatch)


noncomputable def «$lift_namedExpressionListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let namedExpressionIR : SpecTec.namedExpressionIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.namedExpressionIR) := «exec:1»; (.bind (.call ⟨SpecTec.namedExpression, SpecTecCall.«$lift_namedExpressionIR» namedExpressionIR⟩) (fun («exec:3» : SpecTec.namedExpression) => (let «eval:1» : SpecTec.namedExpression := «exec:3»; (let namedExpression : SpecTec.namedExpression := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.namedExpression), SpecTecCall.«$lift_namedExpressionListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.namedExpression)) => (let «tail:1» : (_root_.List SpecTec.namedExpression) := «exec:4»; (.pure (((namedExpression :: «tail:1») : (_root_.List SpecTec.namedExpression))))))))))))) | [] => .unmatch)


noncomputable def «$lift_namedExpressionListIR:case_1:iter:0_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_namedExpressionListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_namedExpressionListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_namedExpressionListIR:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «namedExpressionIR*» : (_root_.List namedExpressionIR) := input0; (.bind (.call ⟨(_root_.List namedExpression), SpecTecCall.«$lift_namedExpressionListIR:case_1:iter:0» «namedExpressionIR*»⟩) (fun («exec:1» : (_root_.List namedExpression)) => (let «namedExpression*» : (_root_.List namedExpression) := «exec:1»; (.bind (.call ⟨SpecTec.namedExpressionList, SpecTecCall.«$unflatten_namedExpressionList» «namedExpression*»⟩) (fun («exec:2» : SpecTec.namedExpressionList) => (let «eval:2» : SpecTec.namedExpressionList := «exec:2»; (let namedExpressionList : SpecTec.namedExpressionList := «eval:2»; (.pure ((namedExpressionList : SpecTec.namedExpressionList)))))))))))


noncomputable def «$lift_namedExpressionListIR_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_namedExpressionListIR:clause:0»  input0)]


noncomputable def «$lift_simpleKeysetExpressionIR:clause:0» (input0 : SpecTec.simpleKeysetExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let simpleKeysetExpressionIR : SpecTec.simpleKeysetExpressionIR := input0; (.bind (.guard (((«sub:simpleKeysetExpressionIR:typedExpressionIR» simpleKeysetExpressionIR) = true))) (fun (_ : Unit) => (match («$lift_simpleKeysetExpressionIR:case_1:downcast:0» simpleKeysetExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.typedExpressionIR := «exec:1»; (let typedExpressionIR : SpecTec.typedExpressionIR := «eval:0»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:2» : SpecTec.expression) => (let «eval:1» : SpecTec.expression := «exec:2»; (let expression : SpecTec.expression := «eval:1»; (.pure (((«cast:expression:simpleKeysetExpression» expression) : simpleKeysetExpression))))))))) | none => .unmatch))))


noncomputable def «$lift_simpleKeysetExpressionIR:clause:1» (input0 : SpecTec.simpleKeysetExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let simpleKeysetExpressionIR : SpecTec.simpleKeysetExpressionIR := input0; (.bind (.guard (((«exec:match:simpleKeysetExpressionIR:% '&&&' %» simpleKeysetExpressionIR) = true))) (fun (_ : Unit) => (match simpleKeysetExpressionIR with | .«% '&&&' %» «exec:1» «exec:2» => (let typedExpressionIR_base : typedExpressionIR := «exec:1»; (let typedExpressionIR_mask : typedExpressionIR := «exec:2»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_base⟩) (fun («exec:3» : expression) => (let «eval:0» : expression := «exec:3»; (let expression_base : expression := «eval:0»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_mask⟩) (fun («exec:4» : expression) => (let «eval:1» : expression := «exec:4»; (let expression_mask : expression := «eval:1»; (.pure ((((simpleKeysetExpression.«% '&&&' %» expression_base expression_mask) : simpleKeysetExpression) : simpleKeysetExpression))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_simpleKeysetExpressionIR:clause:2» (input0 : SpecTec.simpleKeysetExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let simpleKeysetExpressionIR : SpecTec.simpleKeysetExpressionIR := input0; (.bind (.guard (((«exec:match:simpleKeysetExpressionIR:% '..' %» simpleKeysetExpressionIR) = true))) (fun (_ : Unit) => (match simpleKeysetExpressionIR with | .«% '..' %» «exec:1» «exec:2» => (let typedExpressionIR_lb : typedExpressionIR := «exec:1»; (let typedExpressionIR_ub : typedExpressionIR := «exec:2»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_lb⟩) (fun («exec:3» : expression) => (let «eval:0» : expression := «exec:3»; (let expression_lb : expression := «eval:0»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_ub⟩) (fun («exec:4» : expression) => (let «eval:1» : expression := «exec:4»; (let expression_ub : expression := «eval:1»; (.pure ((((simpleKeysetExpression.«% '..' %» expression_lb expression_ub) : simpleKeysetExpression) : simpleKeysetExpression))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_simpleKeysetExpressionIR:clause:3» (input0 : SpecTec.simpleKeysetExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let simpleKeysetExpressionIR : SpecTec.simpleKeysetExpressionIR := input0; (.bind (.guard (((«exec:match:simpleKeysetExpressionIR:DEFAULT» simpleKeysetExpressionIR) = true))) (fun (_ : Unit) => (.pure ((((simpleKeysetExpression.DEFAULT) : simpleKeysetExpression) : simpleKeysetExpression))))))


noncomputable def «$lift_simpleKeysetExpressionIR:clause:4» (input0 : SpecTec.simpleKeysetExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let simpleKeysetExpressionIR : SpecTec.simpleKeysetExpressionIR := input0; (.bind (.guard (((«exec:match:simpleKeysetExpressionIR:'_'» simpleKeysetExpressionIR) = true))) (fun (_ : Unit) => (.pure ((((simpleKeysetExpression.«'_'») : simpleKeysetExpression) : simpleKeysetExpression))))))


noncomputable def «$lift_simpleKeysetExpressionIR_clauses» (input0 : simpleKeysetExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_simpleKeysetExpressionIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_simpleKeysetExpressionIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_simpleKeysetExpressionIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_simpleKeysetExpressionIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_simpleKeysetExpressionIR:clause:4»  input0)]


noncomputable def «$lift_simpleKeysetExpressionListIR:case_1:iter:0:clause:0» (input0 : (_root_.List simpleKeysetExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List simpleKeysetExpression)) : (_root_.List simpleKeysetExpression)))) | _ :: _ => .unmatch)


noncomputable def «$lift_simpleKeysetExpressionListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.simpleKeysetExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let simpleKeysetExpressionIR : SpecTec.simpleKeysetExpressionIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.simpleKeysetExpressionIR) := «exec:1»; (.bind (.call ⟨SpecTec.simpleKeysetExpression, SpecTecCall.«$lift_simpleKeysetExpressionIR» simpleKeysetExpressionIR⟩) (fun («exec:3» : SpecTec.simpleKeysetExpression) => (let «eval:1» : SpecTec.simpleKeysetExpression := «exec:3»; (let simpleKeysetExpression : SpecTec.simpleKeysetExpression := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.simpleKeysetExpression), SpecTecCall.«$lift_simpleKeysetExpressionListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.simpleKeysetExpression)) => (let «tail:1» : (_root_.List SpecTec.simpleKeysetExpression) := «exec:4»; (.pure (((simpleKeysetExpression :: «tail:1») : (_root_.List SpecTec.simpleKeysetExpression))))))))))))) | [] => .unmatch)


noncomputable def «$lift_simpleKeysetExpressionListIR:case_1:iter:0_clauses» (input0 : (_root_.List simpleKeysetExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_simpleKeysetExpressionListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_simpleKeysetExpressionListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_simpleKeysetExpressionListIR:clause:0» (input0 : (_root_.List simpleKeysetExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «simpleKeysetExpressionIR*» : (_root_.List simpleKeysetExpressionIR) := input0; (.bind (.call ⟨(_root_.List simpleKeysetExpression), SpecTecCall.«$lift_simpleKeysetExpressionListIR:case_1:iter:0» «simpleKeysetExpressionIR*»⟩) (fun («exec:1» : (_root_.List simpleKeysetExpression)) => (let «simpleKeysetExpression*» : (_root_.List simpleKeysetExpression) := «exec:1»; (.bind (.call ⟨SpecTec.simpleKeysetExpressionList, SpecTecCall.«$unflatten_simpleKeysetExpressionList» «simpleKeysetExpression*»⟩) (fun («exec:2» : SpecTec.simpleKeysetExpressionList) => (let «eval:2» : SpecTec.simpleKeysetExpressionList := «exec:2»; (let simpleKeysetExpressionList : SpecTec.simpleKeysetExpressionList := «eval:2»; (.pure ((simpleKeysetExpressionList : SpecTec.simpleKeysetExpressionList)))))))))))


noncomputable def «$lift_simpleKeysetExpressionListIR_clauses» (input0 : (_root_.List simpleKeysetExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_simpleKeysetExpressionListIR:clause:0»  input0)]

end SpecTec
