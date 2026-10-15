import SpecTecDecl0312

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_parserTypeDeclarationIR:clause:0» (input0 : parserTypeDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% PARSER % `< % ',' % `> `( % `) ';'» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := «exec:3»; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := «exec:4»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:5»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:6» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:6»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (let «typeParameterIR*» : (_root_.List typeParameterIR) := («typeParameterIR_expl*» ++ «typeParameterIR_impl*»); (.bind (.call ⟨SpecTec.typeParameterListOpt, SpecTecCall.«$lift_typeParameterListIR» «typeParameterIR*»⟩) (fun («exec:7» : SpecTec.typeParameterListOpt) => (let «eval:1» : SpecTec.typeParameterListOpt := «exec:7»; (let typeParameterListOpt : SpecTec.typeParameterListOpt := «eval:1»; (.bind (.call ⟨SpecTec.parameterList, SpecTecCall.«$lift_parameterListIR» «parameterIR*»⟩) (fun («exec:8» : SpecTec.parameterList) => (let «eval:2» : SpecTec.parameterList := «exec:8»; (let parameterList : SpecTec.parameterList := «eval:2»; (.pure ((((parserTypeDeclaration.«% PARSER % % `( % `) ';'» annotationList name typeParameterListOpt parameterList) : parserTypeDeclaration) : parserTypeDeclaration))))))))))))))))))))))


noncomputable def «$lift_parserTypeDeclarationIR_clauses» (input0 : parserTypeDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserTypeDeclarationIR:clause:0»  input0)]


noncomputable def «$lift_parserStatementIR:clause:0» (input0 : SpecTec.parserStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserStatementIR : SpecTec.parserStatementIR := input0; (.bind (.guard (((«sub:parserStatementIR:emptyStatement» parserStatementIR) = true))) (fun (_ : Unit) => (match («$lift_parserStatementIR:case_1:downcast:0» parserStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.emptyStatementIR := «exec:1»; (let emptyStatementIR : SpecTec.emptyStatementIR := «eval:0»; (.bind (.call ⟨emptyStatement, SpecTecCall.«$lift_emptyStatementIR» emptyStatementIR⟩) (fun («exec:2» : emptyStatement) => (let «eval:1» : emptyStatement := «exec:2»; (.pure (((«cast:emptyStatement:parserStatement» «eval:1») : parserStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_parserStatementIR:clause:1» (input0 : SpecTec.parserStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserStatementIR : SpecTec.parserStatementIR := input0; (.bind (.guard (((«sub:parserStatementIR:assignmentStatementIR» parserStatementIR) = true))) (fun (_ : Unit) => (match («$lift_parserStatementIR:case_2:downcast:0» parserStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.assignmentStatementIR := «exec:1»; (let assignmentStatementIR : SpecTec.assignmentStatementIR := «eval:0»; (.bind (.call ⟨assignmentStatement, SpecTecCall.«$lift_assignmentStatementIR» assignmentStatementIR⟩) (fun («exec:2» : assignmentStatement) => (let «eval:1» : assignmentStatement := «exec:2»; (.pure (((«cast:assignmentStatement:parserStatement» «eval:1») : parserStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_parserStatementIR:clause:2» (input0 : SpecTec.parserStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserStatementIR : SpecTec.parserStatementIR := input0; (.bind (.guard (((«sub:parserStatementIR:callStatementIR» parserStatementIR) = true))) (fun (_ : Unit) => (match («$lift_parserStatementIR:case_3:downcast:0» parserStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.callStatementIR := «exec:1»; (let callStatementIR : SpecTec.callStatementIR := «eval:0»; (.bind (.call ⟨callStatement, SpecTecCall.«$lift_callStatementIR» callStatementIR⟩) (fun («exec:2» : callStatement) => (let «eval:1» : callStatement := «exec:2»; (.pure (((«cast:callStatement:parserStatement» «eval:1») : parserStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_parserStatementIR:clause:3» (input0 : SpecTec.parserStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserStatementIR : SpecTec.parserStatementIR := input0; (.bind (.guard (((«sub:parserStatementIR:directApplicationStatementIR» parserStatementIR) = true))) (fun (_ : Unit) => (match («$lift_parserStatementIR:case_4:downcast:0» parserStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.directApplicationStatementIR := «exec:1»; (let directApplicationStatementIR : SpecTec.directApplicationStatementIR := «eval:0»; (.bind (.call ⟨directApplicationStatement, SpecTecCall.«$lift_directApplicationStatementIR» directApplicationStatementIR⟩) (fun («exec:2» : directApplicationStatement) => (let «eval:1» : directApplicationStatement := «exec:2»; (.pure (((«cast:directApplicationStatement:parserStatement» «eval:1») : parserStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_parserStatementIR:clause:4» (input0 : SpecTec.parserStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserStatementIR : SpecTec.parserStatementIR := input0; (.bind (.guard (((«sub:parserStatementIR:parserBlockStatementIR» parserStatementIR) = true))) (fun (_ : Unit) => (match («$lift_parserStatementIR:case_5:downcast:0» parserStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.parserBlockStatementIR := «exec:1»; (let parserBlockStatementIR : SpecTec.parserBlockStatementIR := «eval:0»; (.bind (.call ⟨parserBlockStatement, SpecTecCall.«$lift_parserBlockStatementIR» parserBlockStatementIR⟩) (fun («exec:2» : parserBlockStatement) => (let «eval:1» : parserBlockStatement := «exec:2»; (.pure (((«cast:parserBlockStatement:parserStatement» «eval:1») : parserStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_parserStatementIR:clause:5» (input0 : SpecTec.parserStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserStatementIR : SpecTec.parserStatementIR := input0; (.bind (.guard (((«sub:parserStatementIR:parserConditionalStatementIR» parserStatementIR) = true))) (fun (_ : Unit) => (match («$lift_parserStatementIR:case_6:downcast:0» parserStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.parserConditionalStatementIR := «exec:1»; (let parserConditionalStatementIR : SpecTec.parserConditionalStatementIR := «eval:0»; (.bind (.call ⟨parserConditionalStatement, SpecTecCall.«$lift_parserConditionalStatementIR» parserConditionalStatementIR⟩) (fun («exec:2» : parserConditionalStatement) => (let «eval:1» : parserConditionalStatement := «exec:2»; (.pure (((«cast:parserConditionalStatement:parserStatement» «eval:1») : parserStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_parserStatementIR_clauses» (input0 : parserStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserStatementIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_parserStatementIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_parserStatementIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_parserStatementIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_parserStatementIR:clause:4»  input0), fun (_ : _root_.Unit) => («$lift_parserStatementIR:clause:5»  input0)]


noncomputable def «$lift_parserBlockElementStatementIR:clause:0» (input0 : SpecTec.parserBlockElementStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserBlockElementStatementIR : SpecTec.parserBlockElementStatementIR := input0; (.bind (.guard (((«sub:parserBlockElementStatementIR:constantDeclarationIR» parserBlockElementStatementIR) = true))) (fun (_ : Unit) => (match («$lift_parserBlockElementStatementIR:case_1:downcast:0» parserBlockElementStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.constantDeclarationIR := «exec:1»; (let constantDeclarationIR : SpecTec.constantDeclarationIR := «eval:0»; (.bind (.call ⟨constantDeclaration, SpecTecCall.«$lift_constantDeclarationIR» constantDeclarationIR⟩) (fun («exec:2» : constantDeclaration) => (let «eval:1» : constantDeclaration := «exec:2»; (.pure (((«cast:constantDeclaration:parserBlockElementStatement» «eval:1») : parserBlockElementStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_parserBlockElementStatementIR:clause:1» (input0 : SpecTec.parserBlockElementStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserBlockElementStatementIR : SpecTec.parserBlockElementStatementIR := input0; (.bind (.guard (((«sub:parserBlockElementStatementIR:variableDeclarationIR» parserBlockElementStatementIR) = true))) (fun (_ : Unit) => (match («$lift_parserBlockElementStatementIR:case_2:downcast:0» parserBlockElementStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.variableDeclarationIR := «exec:1»; (let variableDeclarationIR : SpecTec.variableDeclarationIR := «eval:0»; (.bind (.call ⟨variableDeclaration, SpecTecCall.«$lift_variableDeclarationIR» variableDeclarationIR⟩) (fun («exec:2» : variableDeclaration) => (let «eval:1» : variableDeclaration := «exec:2»; (.pure (((«cast:variableDeclaration:parserBlockElementStatement» «eval:1») : parserBlockElementStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_parserBlockElementStatementIR:clause:2» (input0 : SpecTec.parserBlockElementStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserBlockElementStatementIR : SpecTec.parserBlockElementStatementIR := input0; (.bind (.guard (((«sub:parserBlockElementStatementIR:parserStatementIR» parserBlockElementStatementIR) = true))) (fun (_ : Unit) => (match («$lift_parserBlockElementStatementIR:case_3:downcast:0» parserBlockElementStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.parserStatementIR := «exec:1»; (let parserStatementIR : SpecTec.parserStatementIR := «eval:0»; (.bind (.call ⟨parserStatement, SpecTecCall.«$lift_parserStatementIR» parserStatementIR⟩) (fun («exec:2» : parserStatement) => (let «eval:1» : parserStatement := «exec:2»; (.pure (((«cast:parserStatement:parserBlockElementStatement» «eval:1») : parserBlockElementStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_parserBlockElementStatementIR_clauses» (input0 : parserBlockElementStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserBlockElementStatementIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_parserBlockElementStatementIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_parserBlockElementStatementIR:clause:2»  input0)]


noncomputable def «$lift_parserBlockElementStatementListIR:clause:0» (input0 : (_root_.List parserBlockElementStatementIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parserBlockElementStatementIR*» : (_root_.List parserBlockElementStatementIR) := input0; (.bind (.call ⟨(_root_.List parserBlockElementStatement), SpecTecCall.«$lift_parserBlockElementStatementListIR:case_1:iter:0» «parserBlockElementStatementIR*»⟩) (fun («exec:1» : (_root_.List parserBlockElementStatement)) => (let «parserBlockElementStatement*» : (_root_.List parserBlockElementStatement) := «exec:1»; (.bind (.call ⟨SpecTec.parserBlockElementStatementList, SpecTecCall.«$unflatten_parserBlockElementStatementList» «parserBlockElementStatement*»⟩) (fun («exec:2» : SpecTec.parserBlockElementStatementList) => (let «eval:2» : SpecTec.parserBlockElementStatementList := «exec:2»; (let parserBlockElementStatementList : SpecTec.parserBlockElementStatementList := «eval:2»; (.pure ((parserBlockElementStatementList : SpecTec.parserBlockElementStatementList)))))))))))


noncomputable def «$lift_parserBlockElementStatementListIR_clauses» (input0 : (_root_.List parserBlockElementStatementIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserBlockElementStatementListIR:clause:0»  input0)]


noncomputable def «$lift_parserBlockElementStatementListIR:case_1:iter:0:clause:0» (input0 : (_root_.List parserBlockElementStatementIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List parserBlockElementStatement)) : (_root_.List parserBlockElementStatement)))) | _ :: _ => .unmatch)


noncomputable def «$lift_parserBlockElementStatementListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.parserBlockElementStatementIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parserBlockElementStatementIR : SpecTec.parserBlockElementStatementIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parserBlockElementStatementIR) := «exec:1»; (.bind (.call ⟨SpecTec.parserBlockElementStatement, SpecTecCall.«$lift_parserBlockElementStatementIR» parserBlockElementStatementIR⟩) (fun («exec:3» : SpecTec.parserBlockElementStatement) => (let «eval:1» : SpecTec.parserBlockElementStatement := «exec:3»; (let parserBlockElementStatement : SpecTec.parserBlockElementStatement := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.parserBlockElementStatement), SpecTecCall.«$lift_parserBlockElementStatementListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parserBlockElementStatement)) => (let «tail:1» : (_root_.List SpecTec.parserBlockElementStatement) := «exec:4»; (.pure (((parserBlockElementStatement :: «tail:1») : (_root_.List SpecTec.parserBlockElementStatement))))))))))))) | [] => .unmatch)


noncomputable def «$lift_parserBlockElementStatementListIR:case_1:iter:0_clauses» (input0 : (_root_.List parserBlockElementStatementIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserBlockElementStatementListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_parserBlockElementStatementListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_parserBlockStatementIR:clause:0» (input0 : parserBlockStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% `{ % `}» «exec:1» «exec:2» => (let annotationList : SpecTec.annotationList := «exec:1»; (let «parserBlockElementStatementIR*» : (_root_.List parserBlockElementStatementIR) := «exec:2»; (.bind (.call ⟨SpecTec.parserBlockElementStatementList, SpecTecCall.«$lift_parserBlockElementStatementListIR» «parserBlockElementStatementIR*»⟩) (fun («exec:3» : SpecTec.parserBlockElementStatementList) => (let «eval:0» : SpecTec.parserBlockElementStatementList := «exec:3»; (let parserBlockElementStatementList : SpecTec.parserBlockElementStatementList := «eval:0»; (.pure ((((parserBlockStatement.«% `{ % `}» annotationList parserBlockElementStatementList) : parserBlockStatement) : parserBlockStatement))))))))))


noncomputable def «$lift_parserBlockStatementIR_clauses» (input0 : parserBlockStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserBlockStatementIR:clause:0»  input0)]


noncomputable def «$lift_parserConditionalStatementIR:clause:0» (input0 : SpecTec.parserConditionalStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserConditionalStatementIR : SpecTec.parserConditionalStatementIR := input0; (.bind (.guard (((«exec:match:parserConditionalStatementIR:IF `( % `) %» parserConditionalStatementIR) = true))) (fun (_ : Unit) => (match parserConditionalStatementIR with | .«IF `( % `) %» «exec:1» «exec:2» => (let typedExpressionIR_cond : typedExpressionIR := «exec:1»; (let parserStatementIR_then : parserStatementIR := «exec:2»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_cond⟩) (fun («exec:3» : expression) => (let «eval:0» : expression := «exec:3»; (let expression_cond : expression := «eval:0»; (.bind (.call ⟨parserStatement, SpecTecCall.«$lift_parserStatementIR» parserStatementIR_then⟩) (fun («exec:4» : parserStatement) => (let «eval:1» : parserStatement := «exec:4»; (let parserStatement_then : parserStatement := «eval:1»; (.pure ((((parserConditionalStatement.«IF `( % `) %» expression_cond parserStatement_then) : parserConditionalStatement) : parserConditionalStatement))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_parserConditionalStatementIR:clause:1» (input0 : SpecTec.parserConditionalStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserConditionalStatementIR : SpecTec.parserConditionalStatementIR := input0; (.bind (.guard (((«exec:match:parserConditionalStatementIR:IF `( % `) % ELSE %» parserConditionalStatementIR) = true))) (fun (_ : Unit) => (match parserConditionalStatementIR with | .«IF `( % `) % ELSE %» «exec:1» «exec:2» «exec:3» => (let typedExpressionIR_cond : typedExpressionIR := «exec:1»; (let parserStatementIR_then : parserStatementIR := «exec:2»; (let parserStatementIR_else : parserStatementIR := «exec:3»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_cond⟩) (fun («exec:4» : expression) => (let «eval:0» : expression := «exec:4»; (let expression_cond : expression := «eval:0»; (.bind (.call ⟨parserStatement, SpecTecCall.«$lift_parserStatementIR» parserStatementIR_then⟩) (fun («exec:5» : parserStatement) => (let «eval:1» : parserStatement := «exec:5»; (let parserStatement_then : parserStatement := «eval:1»; (.bind (.call ⟨parserStatement, SpecTecCall.«$lift_parserStatementIR» parserStatementIR_else⟩) (fun («exec:6» : parserStatement) => (let «eval:2» : parserStatement := «exec:6»; (let parserStatement_else : parserStatement := «eval:2»; (.pure ((((parserConditionalStatement.«IF `( % `) % ELSE %» expression_cond parserStatement_then parserStatement_else) : parserConditionalStatement) : parserConditionalStatement)))))))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_parserConditionalStatementIR_clauses» (input0 : parserConditionalStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserConditionalStatementIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_parserConditionalStatementIR:clause:1»  input0)]


noncomputable def «$lift_parserStateIR:clause:0» (input0 : parserStateIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% STATE % `{ % % `}» «exec:1» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let «parserBlockElementStatementIR*» : (_root_.List parserBlockElementStatementIR) := «exec:3»; (let transitionStatementIR : SpecTec.transitionStatementIR := «exec:4»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:5» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:5»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (.bind (.call ⟨SpecTec.parserBlockElementStatementList, SpecTecCall.«$lift_parserBlockElementStatementListIR» «parserBlockElementStatementIR*»⟩) (fun («exec:6» : SpecTec.parserBlockElementStatementList) => (let «eval:1» : SpecTec.parserBlockElementStatementList := «exec:6»; (let parserBlockElementStatementList : SpecTec.parserBlockElementStatementList := «eval:1»; (.bind (.call ⟨SpecTec.transitionStatement, SpecTecCall.«$lift_transitionStatementIR» transitionStatementIR⟩) (fun («exec:7» : SpecTec.transitionStatement) => (let «eval:2» : SpecTec.transitionStatement := «exec:7»; (let transitionStatement : SpecTec.transitionStatement := «eval:2»; (.pure ((((parserState.«% STATE % `{ % % `}» annotationList name parserBlockElementStatementList transitionStatement) : parserState) : parserState))))))))))))))))))))


noncomputable def «$lift_parserStateIR_clauses» (input0 : parserStateIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserStateIR:clause:0»  input0)]


noncomputable def «$lift_parserStateListIR:case_1:iter:0:clause:0» (input0 : (_root_.List parserStateIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List parserState)) : (_root_.List parserState)))) | _ :: _ => .unmatch)


noncomputable def «$lift_parserStateListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.parserStateIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parserStateIR : SpecTec.parserStateIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parserStateIR) := «exec:1»; (.bind (.call ⟨SpecTec.parserState, SpecTecCall.«$lift_parserStateIR» parserStateIR⟩) (fun («exec:3» : SpecTec.parserState) => (let «eval:1» : SpecTec.parserState := «exec:3»; (let parserState : SpecTec.parserState := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.parserState), SpecTecCall.«$lift_parserStateListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parserState)) => (let «tail:1» : (_root_.List SpecTec.parserState) := «exec:4»; (.pure (((parserState :: «tail:1») : (_root_.List SpecTec.parserState))))))))))))) | [] => .unmatch)


noncomputable def «$lift_parserStateListIR:case_1:iter:0_clauses» (input0 : (_root_.List parserStateIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserStateListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_parserStateListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_parserStateListIR:clause:0» (input0 : (_root_.List parserStateIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parserStateIR*» : (_root_.List parserStateIR) := input0; (.bind (.call ⟨(_root_.List parserState), SpecTecCall.«$lift_parserStateListIR:case_1:iter:0» «parserStateIR*»⟩) (fun («exec:1» : (_root_.List parserState)) => (let «parserState*» : (_root_.List parserState) := «exec:1»; (.bind (.call ⟨SpecTec.parserStateList, SpecTecCall.«$unflatten_parserStateList» «parserState*»⟩) (fun («exec:2» : SpecTec.parserStateList) => (let «eval:2» : SpecTec.parserStateList := «exec:2»; (let parserStateList : SpecTec.parserStateList := «eval:2»; (.pure ((parserStateList : SpecTec.parserStateList)))))))))))


noncomputable def «$lift_parserStateListIR_clauses» (input0 : (_root_.List parserStateIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserStateListIR:clause:0»  input0)]


noncomputable def «$lift_parserLocalDeclarationIR:clause:0» (input0 : SpecTec.parserLocalDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserLocalDeclarationIR : SpecTec.parserLocalDeclarationIR := input0; (.bind (.guard (((«sub:parserLocalDeclarationIR:constantDeclarationIR» parserLocalDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_parserLocalDeclarationIR:case_1:downcast:0» parserLocalDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.constantDeclarationIR := «exec:1»; (let constantDeclarationIR : SpecTec.constantDeclarationIR := «eval:0»; (.bind (.call ⟨constantDeclaration, SpecTecCall.«$lift_constantDeclarationIR» constantDeclarationIR⟩) (fun («exec:2» : constantDeclaration) => (let «eval:1» : constantDeclaration := «exec:2»; (.pure (((«cast:constantDeclaration:parserLocalDeclaration» «eval:1») : parserLocalDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_parserLocalDeclarationIR:clause:1» (input0 : SpecTec.parserLocalDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserLocalDeclarationIR : SpecTec.parserLocalDeclarationIR := input0; (.bind (.guard (((«sub:parserLocalDeclarationIR:instantiationIR» parserLocalDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_parserLocalDeclarationIR:case_2:downcast:0» parserLocalDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.instantiationIR := «exec:1»; (let instantiationIR : SpecTec.instantiationIR := «eval:0»; (.bind (.call ⟨instantiation, SpecTecCall.«$lift_instantiationIR» instantiationIR⟩) (fun («exec:2» : instantiation) => (let «eval:1» : instantiation := «exec:2»; (.pure (((«cast:instantiation:parserLocalDeclaration» «eval:1») : parserLocalDeclaration)))))))) | none => .unmatch))))

end SpecTec
