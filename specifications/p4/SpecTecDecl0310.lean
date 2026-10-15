import SpecTecDecl0309

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_conditionalStatementIR:clause:0» (input0 : SpecTec.conditionalStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let conditionalStatementIR : SpecTec.conditionalStatementIR := input0; (.bind (.guard (((«exec:match:conditionalStatementIR:IF `( % `) %» conditionalStatementIR) = true))) (fun (_ : Unit) => (match conditionalStatementIR with | .«IF `( % `) %» «exec:1» «exec:2» => (let typedExpressionIR_cond : typedExpressionIR := «exec:1»; (let statementIR_then : statementIR := «exec:2»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_cond⟩) (fun («exec:3» : expression) => (let «eval:0» : expression := «exec:3»; (let expression_cond : expression := «eval:0»; (.bind (.call ⟨statement, SpecTecCall.«$lift_statementIR» statementIR_then⟩) (fun («exec:4» : statement) => (let «eval:1» : statement := «exec:4»; (let statement_then : statement := «eval:1»; (.pure ((((conditionalStatement.«IF `( % `) %» expression_cond statement_then) : conditionalStatement) : conditionalStatement))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_conditionalStatementIR:clause:1» (input0 : SpecTec.conditionalStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let conditionalStatementIR : SpecTec.conditionalStatementIR := input0; (.bind (.guard (((«exec:match:conditionalStatementIR:IF `( % `) % ELSE %» conditionalStatementIR) = true))) (fun (_ : Unit) => (match conditionalStatementIR with | .«IF `( % `) % ELSE %» «exec:1» «exec:2» «exec:3» => (let typedExpressionIR_cond : typedExpressionIR := «exec:1»; (let statementIR_then : statementIR := «exec:2»; (let statementIR_else : statementIR := «exec:3»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_cond⟩) (fun («exec:4» : expression) => (let «eval:0» : expression := «exec:4»; (let expression_cond : expression := «eval:0»; (.bind (.call ⟨statement, SpecTecCall.«$lift_statementIR» statementIR_then⟩) (fun («exec:5» : statement) => (let «eval:1» : statement := «exec:5»; (let statement_then : statement := «eval:1»; (.bind (.call ⟨statement, SpecTecCall.«$lift_statementIR» statementIR_else⟩) (fun («exec:6» : statement) => (let «eval:2» : statement := «exec:6»; (let statement_else : statement := «eval:2»; (.pure ((((conditionalStatement.«IF `( % `) % ELSE %» expression_cond statement_then statement_else) : conditionalStatement) : conditionalStatement)))))))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_conditionalStatementIR_clauses» (input0 : conditionalStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_conditionalStatementIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_conditionalStatementIR:clause:1»  input0)]


noncomputable def «$lift_switchCaseIR:clause:0» (input0 : SpecTec.switchCaseIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchCaseIR : SpecTec.switchCaseIR := input0; (.bind (.guard (((«exec:match:switchCaseIR:% ':' %» switchCaseIR) = true))) (fun (_ : Unit) => (match switchCaseIR with | .«% ':' %» «exec:1» «exec:2» => (let switchLabelIR : SpecTec.switchLabelIR := «exec:1»; (let blockStatementIR : SpecTec.blockStatementIR := «exec:2»; (.bind (.call ⟨SpecTec.switchLabel, SpecTecCall.«$lift_switchLabelIR» switchLabelIR⟩) (fun («exec:3» : SpecTec.switchLabel) => (let «eval:0» : SpecTec.switchLabel := «exec:3»; (let switchLabel : SpecTec.switchLabel := «eval:0»; (.bind (.call ⟨SpecTec.blockStatement, SpecTecCall.«$lift_blockStatementIR» blockStatementIR⟩) (fun («exec:4» : SpecTec.blockStatement) => (let «eval:1» : SpecTec.blockStatement := «exec:4»; (let blockStatement : SpecTec.blockStatement := «eval:1»; (.pure ((((switchCase.«% ':' %» switchLabel blockStatement) : switchCase) : switchCase))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_switchCaseIR:clause:1» (input0 : SpecTec.switchCaseIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchCaseIR : SpecTec.switchCaseIR := input0; (.bind (.guard (((«exec:match:switchCaseIR:% ':'» switchCaseIR) = true))) (fun (_ : Unit) => (match switchCaseIR with | .«% ':'» «exec:1» => (let switchLabelIR : SpecTec.switchLabelIR := «exec:1»; (.bind (.call ⟨SpecTec.switchLabel, SpecTecCall.«$lift_switchLabelIR» switchLabelIR⟩) (fun («exec:2» : SpecTec.switchLabel) => (let «eval:0» : SpecTec.switchLabel := «exec:2»; (let switchLabel : SpecTec.switchLabel := «eval:0»; (.pure ((((switchCase.«% ':'» switchLabel) : switchCase) : switchCase)))))))) | _ => .unmatch))))


noncomputable def «$lift_switchCaseIR_clauses» (input0 : switchCaseIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_switchCaseIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_switchCaseIR:clause:1»  input0)]


noncomputable def «$lift_switchCaseListIR:clause:0» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «switchCaseIR*» : (_root_.List switchCaseIR) := input0; (.bind (.call ⟨(_root_.List switchCase), SpecTecCall.«$lift_switchCaseListIR:case_1:iter:0» «switchCaseIR*»⟩) (fun («exec:1» : (_root_.List switchCase)) => (let «switchCase*» : (_root_.List switchCase) := «exec:1»; (.bind (.call ⟨SpecTec.switchCaseList, SpecTecCall.«$unflatten_switchCaseList» «switchCase*»⟩) (fun («exec:2» : SpecTec.switchCaseList) => (let «eval:2» : SpecTec.switchCaseList := «exec:2»; (let switchCaseList : SpecTec.switchCaseList := «eval:2»; (.pure ((switchCaseList : SpecTec.switchCaseList)))))))))))


noncomputable def «$lift_switchCaseListIR_clauses» (input0 : (_root_.List switchCaseIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_switchCaseListIR:clause:0»  input0)]


noncomputable def «$lift_switchCaseListIR:case_1:iter:0:clause:0» (input0 : (_root_.List switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List switchCase)) : (_root_.List switchCase)))) | _ :: _ => .unmatch)


noncomputable def «$lift_switchCaseListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.switchCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let switchCaseIR : SpecTec.switchCaseIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.switchCaseIR) := «exec:1»; (.bind (.call ⟨SpecTec.switchCase, SpecTecCall.«$lift_switchCaseIR» switchCaseIR⟩) (fun («exec:3» : SpecTec.switchCase) => (let «eval:1» : SpecTec.switchCase := «exec:3»; (let switchCase : SpecTec.switchCase := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.switchCase), SpecTecCall.«$lift_switchCaseListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.switchCase)) => (let «tail:1» : (_root_.List SpecTec.switchCase) := «exec:4»; (.pure (((switchCase :: «tail:1») : (_root_.List SpecTec.switchCase))))))))))))) | [] => .unmatch)


noncomputable def «$lift_switchCaseListIR:case_1:iter:0_clauses» (input0 : (_root_.List switchCaseIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_switchCaseListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_switchCaseListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_switchStatementIR:clause:0» (input0 : switchStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«SWITCH `( % `) `{ % `}» «exec:1» «exec:2» => (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:1»; (let «switchCaseIR*» : (_root_.List switchCaseIR) := «exec:2»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:3» : SpecTec.expression) => (let «eval:0» : SpecTec.expression := «exec:3»; (let expression : SpecTec.expression := «eval:0»; (.bind (.call ⟨SpecTec.switchCaseList, SpecTecCall.«$lift_switchCaseListIR» «switchCaseIR*»⟩) (fun («exec:4» : SpecTec.switchCaseList) => (let «eval:1» : SpecTec.switchCaseList := «exec:4»; (let switchCaseList : SpecTec.switchCaseList := «eval:1»; (.pure ((((switchStatement.«SWITCH `( % `) `{ % `}» expression switchCaseList) : switchStatement) : switchStatement))))))))))))))


noncomputable def «$lift_switchStatementIR_clauses» (input0 : switchStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_switchStatementIR:clause:0»  input0)]


noncomputable def «$lift_blockElementStatementListIR:case_1:iter:0:clause:0» (input0 : (_root_.List blockElementStatementIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List blockElementStatement)) : (_root_.List blockElementStatement)))) | _ :: _ => .unmatch)


noncomputable def «$lift_blockElementStatementListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.blockElementStatementIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let blockElementStatementIR : SpecTec.blockElementStatementIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.blockElementStatementIR) := «exec:1»; (.bind (.call ⟨SpecTec.blockElementStatement, SpecTecCall.«$lift_blockElementStatementIR» blockElementStatementIR⟩) (fun («exec:3» : SpecTec.blockElementStatement) => (let «eval:1» : SpecTec.blockElementStatement := «exec:3»; (let blockElementStatement : SpecTec.blockElementStatement := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.blockElementStatement), SpecTecCall.«$lift_blockElementStatementListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.blockElementStatement)) => (let «tail:1» : (_root_.List SpecTec.blockElementStatement) := «exec:4»; (.pure (((blockElementStatement :: «tail:1») : (_root_.List SpecTec.blockElementStatement))))))))))))) | [] => .unmatch)


noncomputable def «$lift_blockElementStatementListIR:case_1:iter:0_clauses» (input0 : (_root_.List blockElementStatementIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_blockElementStatementListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_blockElementStatementListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_blockElementStatementListIR:clause:0» (input0 : (_root_.List blockElementStatementIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «blockElementStatementIR*» : (_root_.List blockElementStatementIR) := input0; (.bind (.call ⟨(_root_.List blockElementStatement), SpecTecCall.«$lift_blockElementStatementListIR:case_1:iter:0» «blockElementStatementIR*»⟩) (fun («exec:1» : (_root_.List blockElementStatement)) => (let «blockElementStatement*» : (_root_.List blockElementStatement) := «exec:1»; (.bind (.call ⟨SpecTec.blockElementStatementList, SpecTecCall.«$unflatten_blockElementStatementList» «blockElementStatement*»⟩) (fun («exec:2» : SpecTec.blockElementStatementList) => (let «eval:2» : SpecTec.blockElementStatementList := «exec:2»; (let blockElementStatementList : SpecTec.blockElementStatementList := «eval:2»; (.pure ((blockElementStatementList : SpecTec.blockElementStatementList)))))))))))


noncomputable def «$lift_blockElementStatementListIR_clauses» (input0 : (_root_.List blockElementStatementIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_blockElementStatementListIR:clause:0»  input0)]


noncomputable def «$lift_functionPrototypeIR:clause:0» (input0 : functionPrototypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % `< % ',' % `> `( % `)» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let typeIR : SpecTec.typeIR := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := «exec:3»; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := «exec:4»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:5»; (.bind (.call ⟨SpecTec.typeOrVoid, SpecTecCall.«$lift_typeIR_as_typeOrVoid» typeIR⟩) (fun («exec:6» : SpecTec.typeOrVoid) => (let «eval:0» : SpecTec.typeOrVoid := «exec:6»; (let typeOrVoid : SpecTec.typeOrVoid := «eval:0»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:7» : nonTypeName) => (let «eval:1» : nonTypeName := «exec:7»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:1»); (let «typeParameterIR*» : (_root_.List typeParameterIR) := («typeParameterIR_expl*» ++ «typeParameterIR_impl*»); (.bind (.call ⟨SpecTec.typeParameterListOpt, SpecTecCall.«$lift_typeParameterListIR» «typeParameterIR*»⟩) (fun («exec:8» : SpecTec.typeParameterListOpt) => (let «eval:2» : SpecTec.typeParameterListOpt := «exec:8»; (let typeParameterListOpt : SpecTec.typeParameterListOpt := «eval:2»; (.bind (.call ⟨SpecTec.parameterList, SpecTecCall.«$lift_parameterListIR» «parameterIR*»⟩) (fun («exec:9» : SpecTec.parameterList) => (let «eval:3» : SpecTec.parameterList := «exec:9»; (let parameterList : SpecTec.parameterList := «eval:3»; (.pure ((((functionPrototype.«% % % `( % `)» typeOrVoid name typeParameterListOpt parameterList) : functionPrototype) : functionPrototype))))))))))))))))))))))))))


noncomputable def «$lift_functionPrototypeIR_clauses» (input0 : functionPrototypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_functionPrototypeIR:clause:0»  input0)]


noncomputable def «$lift_functionDeclarationIR:clause:0» (input0 : functionDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % %» «exec:1» «exec:2» «exec:3» => (let annotationList : SpecTec.annotationList := «exec:1»; (let functionPrototypeIR : SpecTec.functionPrototypeIR := «exec:2»; (let blockStatementIR : SpecTec.blockStatementIR := «exec:3»; (.bind (.call ⟨SpecTec.functionPrototype, SpecTecCall.«$lift_functionPrototypeIR» functionPrototypeIR⟩) (fun («exec:4» : SpecTec.functionPrototype) => (let «eval:0» : SpecTec.functionPrototype := «exec:4»; (let functionPrototype : SpecTec.functionPrototype := «eval:0»; (.bind (.call ⟨SpecTec.blockStatement, SpecTecCall.«$lift_blockStatementIR» blockStatementIR⟩) (fun («exec:5» : SpecTec.blockStatement) => (let «eval:1» : SpecTec.blockStatement := «exec:5»; (let blockStatement : SpecTec.blockStatement := «eval:1»; (.pure ((((functionDeclaration.«% % %» annotationList functionPrototype blockStatement) : functionDeclaration) : functionDeclaration)))))))))))))))


noncomputable def «$lift_functionDeclarationIR_clauses» (input0 : functionDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_functionDeclarationIR:clause:0»  input0)]


noncomputable def «$lift_actionDeclarationIR:clause:0» (input0 : actionDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% ACTION % `( % `) %» «exec:1» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:3»; (let blockStatementIR : SpecTec.blockStatementIR := «exec:4»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:5» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:5»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (.bind (.call ⟨SpecTec.parameterList, SpecTecCall.«$lift_parameterListIR» «parameterIR*»⟩) (fun («exec:6» : SpecTec.parameterList) => (let «eval:1» : SpecTec.parameterList := «exec:6»; (let parameterList : SpecTec.parameterList := «eval:1»; (.bind (.call ⟨SpecTec.blockStatement, SpecTecCall.«$lift_blockStatementIR» blockStatementIR⟩) (fun («exec:7» : SpecTec.blockStatement) => (let «eval:2» : SpecTec.blockStatement := «exec:7»; (let blockStatement : SpecTec.blockStatement := «eval:2»; (.pure ((((actionDeclaration.«% ACTION % `( % `) %» annotationList name parameterList blockStatement) : actionDeclaration) : actionDeclaration))))))))))))))))))))


noncomputable def «$lift_actionDeclarationIR_clauses» (input0 : actionDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_actionDeclarationIR:clause:0»  input0)]


noncomputable def «$lift_objectDeclarationIR:clause:0» (input0 : SpecTec.objectDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectDeclarationIR : SpecTec.objectDeclarationIR := input0; (.bind (.guard (((«sub:objectDeclarationIR:functionDeclarationIR» objectDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_objectDeclarationIR:case_1:downcast:0» objectDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.functionDeclarationIR := «exec:1»; (let functionDeclarationIR : SpecTec.functionDeclarationIR := «eval:0»; (.bind (.call ⟨functionDeclaration, SpecTecCall.«$lift_functionDeclarationIR» functionDeclarationIR⟩) (fun («exec:2» : functionDeclaration) => (let «eval:1» : functionDeclaration := «exec:2»; (.pure (((«cast:functionDeclaration:objectDeclaration» «eval:1») : objectDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_objectDeclarationIR:clause:1» (input0 : SpecTec.objectDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectDeclarationIR : SpecTec.objectDeclarationIR := input0; (.bind (.guard (((«sub:objectDeclarationIR:instantiationIR» objectDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_objectDeclarationIR:case_2:downcast:0» objectDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.instantiationIR := «exec:1»; (let instantiationIR : SpecTec.instantiationIR := «eval:0»; (.bind (.call ⟨instantiation, SpecTecCall.«$lift_instantiationIR» instantiationIR⟩) (fun («exec:2» : instantiation) => (let «eval:1» : instantiation := «exec:2»; (.pure (((«cast:instantiation:objectDeclaration» «eval:1») : objectDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_objectDeclarationIR_clauses» (input0 : objectDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_objectDeclarationIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_objectDeclarationIR:clause:1»  input0)]


noncomputable def «$lift_objectDeclarationListIR:clause:0» (input0 : (_root_.List objectDeclarationIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «objectDeclarationIR*» : (_root_.List objectDeclarationIR) := input0; (.bind (.call ⟨(_root_.List objectDeclaration), SpecTecCall.«$lift_objectDeclarationListIR:case_1:iter:0» «objectDeclarationIR*»⟩) (fun («exec:1» : (_root_.List objectDeclaration)) => (let «objectDeclaration*» : (_root_.List objectDeclaration) := «exec:1»; (.bind (.call ⟨SpecTec.objectDeclarationList, SpecTecCall.«$unflatten_objectDeclarationList» «objectDeclaration*»⟩) (fun («exec:2» : SpecTec.objectDeclarationList) => (let «eval:2» : SpecTec.objectDeclarationList := «exec:2»; (let objectDeclarationList : SpecTec.objectDeclarationList := «eval:2»; (.pure ((objectDeclarationList : SpecTec.objectDeclarationList)))))))))))


noncomputable def «$lift_objectDeclarationListIR_clauses» (input0 : (_root_.List objectDeclarationIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_objectDeclarationListIR:clause:0»  input0)]


noncomputable def «$lift_objectDeclarationListIR:case_1:iter:0:clause:0» (input0 : (_root_.List objectDeclarationIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List objectDeclaration)) : (_root_.List objectDeclaration)))) | _ :: _ => .unmatch)


noncomputable def «$lift_objectDeclarationListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.objectDeclarationIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let objectDeclarationIR : SpecTec.objectDeclarationIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.objectDeclarationIR) := «exec:1»; (.bind (.call ⟨SpecTec.objectDeclaration, SpecTecCall.«$lift_objectDeclarationIR» objectDeclarationIR⟩) (fun («exec:3» : SpecTec.objectDeclaration) => (let «eval:1» : SpecTec.objectDeclaration := «exec:3»; (let objectDeclaration : SpecTec.objectDeclaration := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.objectDeclaration), SpecTecCall.«$lift_objectDeclarationListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.objectDeclaration)) => (let «tail:1» : (_root_.List SpecTec.objectDeclaration) := «exec:4»; (.pure (((objectDeclaration :: «tail:1») : (_root_.List SpecTec.objectDeclaration))))))))))))) | [] => .unmatch)


noncomputable def «$lift_objectDeclarationListIR:case_1:iter:0_clauses» (input0 : (_root_.List objectDeclarationIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_objectDeclarationListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_objectDeclarationListIR:case_1:iter:0:clause:1»  input0)]

end SpecTec
