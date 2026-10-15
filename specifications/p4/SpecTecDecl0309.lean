import SpecTecDecl0308

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_directApplicationStatementIR:clause:1» (input0 : directApplicationStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% '.' APPLY `( % `) ';'» «exec:1» «exec:2» => (let constructorTargetIR : SpecTec.constructorTargetIR := «exec:1»; (let «argumentIR*» : (_root_.List argumentIR) := «exec:2»; (match constructorTargetIR with | .«% `< % `>» «exec:3» «exec:4» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:3»; (let «typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:4»; (.bind (.guard (((_root_.List.length «typeArgumentIR*») > (0 : _root_.Nat)))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.prefixedTypeName, SpecTecCall.«$lift_prefixedNameIR_as_prefixedTypeName» prefixedNameIR⟩) (fun («exec:5» : SpecTec.prefixedTypeName) => (let «eval:0» : SpecTec.prefixedTypeName := «exec:5»; (let prefixedTypeName : SpecTec.prefixedTypeName := «eval:0»; (.bind (.call ⟨SpecTec.typeArgumentList, SpecTecCall.«$lift_typeArgumentListIR» «typeArgumentIR*»⟩) (fun («exec:6» : SpecTec.typeArgumentList) => (let «eval:1» : SpecTec.typeArgumentList := «exec:6»; (let typeArgumentList : SpecTec.typeArgumentList := «eval:1»; (let namedType : SpecTec.namedType := ((SpecTec.namedType.«% `< % `>» prefixedTypeName typeArgumentList) : SpecTec.namedType); (.bind (.call ⟨SpecTec.argumentList, SpecTecCall.«$lift_argumentListIR» «argumentIR*»⟩) (fun («exec:7» : SpecTec.argumentList) => (let «eval:2» : SpecTec.argumentList := «exec:7»; (let argumentList : SpecTec.argumentList := «eval:2»; (.pure ((((directApplicationStatement.«% '.' APPLY `( % `) ';'» namedType argumentList) : directApplicationStatement) : directApplicationStatement))))))))))))))))))))))))


noncomputable def «$lift_directApplicationStatementIR_clauses» (input0 : directApplicationStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_directApplicationStatementIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_directApplicationStatementIR:clause:1»  input0)]


noncomputable def «$lift_returnStatementIR:clause:0» (input0 : SpecTec.returnStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let returnStatementIR : SpecTec.returnStatementIR := input0; (.bind (.guard (((«exec:match:returnStatementIR:RETURN ';'» returnStatementIR) = true))) (fun (_ : Unit) => (.pure ((((returnStatement.«RETURN ';'») : returnStatement) : returnStatement))))))


noncomputable def «$lift_returnStatementIR:clause:1» (input0 : SpecTec.returnStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let returnStatementIR : SpecTec.returnStatementIR := input0; (.bind (.guard (((«exec:match:returnStatementIR:RETURN % ';'» returnStatementIR) = true))) (fun (_ : Unit) => (match returnStatementIR with | .«RETURN % ';'» «exec:1» => (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:1»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:2» : SpecTec.expression) => (let «eval:0» : SpecTec.expression := «exec:2»; (let expression : SpecTec.expression := «eval:0»; (.pure ((((returnStatement.«RETURN % ';'» expression) : returnStatement) : returnStatement)))))))) | _ => .unmatch))))


noncomputable def «$lift_returnStatementIR_clauses» (input0 : returnStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_returnStatementIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_returnStatementIR:clause:1»  input0)]


noncomputable def «$lift_constantDeclarationIR:clause:0» (input0 : SpecTec.constantDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constantDeclarationIR : SpecTec.constantDeclarationIR := input0; (match constantDeclarationIR with | .«% CONST % % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (let constantInitializerIR : SpecTec.constantInitializerIR := «exec:4»; (.bind (.call ⟨SpecTec.type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:5» : SpecTec.type) => (let «eval:0» : SpecTec.type := «exec:5»; (let type : SpecTec.type := «eval:0»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:6» : nonTypeName) => (let «eval:1» : nonTypeName := «exec:6»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:1»); (.bind (.call ⟨SpecTec.initializer, SpecTecCall.«$lift_constantInitializerIR_as_initializer» constantInitializerIR⟩) (fun («exec:7» : SpecTec.initializer) => (let «eval:2» : SpecTec.initializer := «exec:7»; (let initializer : SpecTec.initializer := «eval:2»; (.pure ((((constantDeclaration.«% CONST % % % ';'» annotationList type name initializer) : constantDeclaration) : constantDeclaration)))))))))))))))))))))


noncomputable def «$lift_constantDeclarationIR_clauses» (input0 : constantDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_constantDeclarationIR:clause:0»  input0)]


noncomputable def «$lift_variableDeclarationIR:clause:0» (input0 : variableDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (let initializerIR? : (_root_.Option initializerIR) := «exec:4»; (.bind (.call ⟨SpecTec.type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:5» : SpecTec.type) => (let «eval:0» : SpecTec.type := «exec:5»; (let type : SpecTec.type := «eval:0»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:6» : nonTypeName) => (let «eval:1» : nonTypeName := «exec:6»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:1»); (.bind (.call ⟨SpecTec.initializerOpt, SpecTecCall.«$lift_initializerOptIR» initializerIR?⟩) (fun («exec:7» : SpecTec.initializerOpt) => (let «eval:2» : SpecTec.initializerOpt := «exec:7»; (let initializerOpt : SpecTec.initializerOpt := «eval:2»; (.pure ((((variableDeclaration.«% % % % ';'» annotationList type name initializerOpt) : variableDeclaration) : variableDeclaration))))))))))))))))))))


noncomputable def «$lift_variableDeclarationIR_clauses» (input0 : variableDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_variableDeclarationIR:clause:0»  input0)]


noncomputable def «$lift_switchLabelIR:clause:0» (input0 : SpecTec.switchLabelIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchLabelIR : SpecTec.switchLabelIR := input0; (.bind (.guard (((«exec:match:switchLabelIR:DEFAULT» switchLabelIR) = true))) (fun (_ : Unit) => (.pure ((((switchLabel.DEFAULT) : switchLabel) : switchLabel))))))


noncomputable def «$lift_switchLabelIR:clause:1» (input0 : SpecTec.switchLabelIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let switchLabelIR : SpecTec.switchLabelIR := input0; (.bind (.guard (((«sub:switchLabelIR:typedExpressionIR» switchLabelIR) = true))) (fun (_ : Unit) => (match («$lift_switchLabelIR:case_2:downcast:0» switchLabelIR) with | some «exec:1» => (let «eval:0» : SpecTec.typedExpressionIR := «exec:1»; (let typedExpressionIR : SpecTec.typedExpressionIR := «eval:0»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:2» : SpecTec.expression) => (let «eval:1» : SpecTec.expression := «exec:2»; (let expression : SpecTec.expression := «eval:1»; (.bind (.call ⟨SpecTec.expressionNonBrace, SpecTecCall.«$expression_as_expressionNonBrace» expression⟩) (fun («exec:3» : SpecTec.expressionNonBrace) => (let «eval:2» : SpecTec.expressionNonBrace := «exec:3»; (let expressionNonBrace : SpecTec.expressionNonBrace := «eval:2»; (.pure (((«cast:expressionNonBrace:switchLabel» expressionNonBrace) : switchLabel))))))))))))) | none => .unmatch))))


noncomputable def «$lift_switchLabelIR_clauses» (input0 : switchLabelIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_switchLabelIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_switchLabelIR:clause:1»  input0)]


noncomputable def «$lift_statementIR:clause:0» (input0 : SpecTec.statementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let statementIR : SpecTec.statementIR := input0; (.bind (.guard (((«sub:statementIR:emptyStatement» statementIR) = true))) (fun (_ : Unit) => (match («$lift_statementIR:case_1:downcast:0» statementIR) with | some «exec:1» => (let «eval:0» : SpecTec.emptyStatementIR := «exec:1»; (let emptyStatementIR : SpecTec.emptyStatementIR := «eval:0»; (.bind (.call ⟨emptyStatement, SpecTecCall.«$lift_emptyStatementIR» emptyStatementIR⟩) (fun («exec:2» : emptyStatement) => (let «eval:1» : emptyStatement := «exec:2»; (.pure (((«cast:emptyStatement:statement» «eval:1») : statement)))))))) | none => .unmatch))))


noncomputable def «$lift_statementIR:clause:1» (input0 : SpecTec.statementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let statementIR : SpecTec.statementIR := input0; (.bind (.guard (((«sub:statementIR:assignmentStatementIR» statementIR) = true))) (fun (_ : Unit) => (match («$lift_statementIR:case_2:downcast:0» statementIR) with | some «exec:1» => (let «eval:0» : SpecTec.assignmentStatementIR := «exec:1»; (let assignmentStatementIR : SpecTec.assignmentStatementIR := «eval:0»; (.bind (.call ⟨assignmentStatement, SpecTecCall.«$lift_assignmentStatementIR» assignmentStatementIR⟩) (fun («exec:2» : assignmentStatement) => (let «eval:1» : assignmentStatement := «exec:2»; (.pure (((«cast:assignmentStatement:statement» «eval:1») : statement)))))))) | none => .unmatch))))


noncomputable def «$lift_statementIR:clause:2» (input0 : SpecTec.statementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let statementIR : SpecTec.statementIR := input0; (.bind (.guard (((«sub:statementIR:callStatementIR» statementIR) = true))) (fun (_ : Unit) => (match («$lift_statementIR:case_3:downcast:0» statementIR) with | some «exec:1» => (let «eval:0» : SpecTec.callStatementIR := «exec:1»; (let callStatementIR : SpecTec.callStatementIR := «eval:0»; (.bind (.call ⟨callStatement, SpecTecCall.«$lift_callStatementIR» callStatementIR⟩) (fun («exec:2» : callStatement) => (let «eval:1» : callStatement := «exec:2»; (.pure (((«cast:callStatement:statement» «eval:1») : statement)))))))) | none => .unmatch))))


noncomputable def «$lift_statementIR:clause:3» (input0 : SpecTec.statementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let statementIR : SpecTec.statementIR := input0; (.bind (.guard (((«sub:statementIR:directApplicationStatementIR» statementIR) = true))) (fun (_ : Unit) => (match («$lift_statementIR:case_4:downcast:0» statementIR) with | some «exec:1» => (let «eval:0» : SpecTec.directApplicationStatementIR := «exec:1»; (let directApplicationStatementIR : SpecTec.directApplicationStatementIR := «eval:0»; (.bind (.call ⟨directApplicationStatement, SpecTecCall.«$lift_directApplicationStatementIR» directApplicationStatementIR⟩) (fun («exec:2» : directApplicationStatement) => (let «eval:1» : directApplicationStatement := «exec:2»; (.pure (((«cast:directApplicationStatement:statement» «eval:1») : statement)))))))) | none => .unmatch))))


noncomputable def «$lift_statementIR:clause:4» (input0 : SpecTec.statementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let statementIR : SpecTec.statementIR := input0; (.bind (.guard (((«sub:statementIR:returnStatementIR» statementIR) = true))) (fun (_ : Unit) => (match («$lift_statementIR:case_5:downcast:0» statementIR) with | some «exec:1» => (let «eval:0» : SpecTec.returnStatementIR := «exec:1»; (let returnStatementIR : SpecTec.returnStatementIR := «eval:0»; (.bind (.call ⟨returnStatement, SpecTecCall.«$lift_returnStatementIR» returnStatementIR⟩) (fun («exec:2» : returnStatement) => (let «eval:1» : returnStatement := «exec:2»; (.pure (((«cast:returnStatement:statement» «eval:1») : statement)))))))) | none => .unmatch))))


noncomputable def «$lift_statementIR:clause:5» (input0 : SpecTec.statementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let statementIR : SpecTec.statementIR := input0; (.bind (.guard (((«sub:statementIR:exitStatement» statementIR) = true))) (fun (_ : Unit) => (match («$lift_statementIR:case_6:downcast:0» statementIR) with | some «exec:1» => (let «eval:0» : SpecTec.exitStatementIR := «exec:1»; (let exitStatementIR : SpecTec.exitStatementIR := «eval:0»; (.bind (.call ⟨exitStatement, SpecTecCall.«$lift_exitStatementIR» exitStatementIR⟩) (fun («exec:2» : exitStatement) => (let «eval:1» : exitStatement := «exec:2»; (.pure (((«cast:exitStatement:statement» «eval:1») : statement)))))))) | none => .unmatch))))


noncomputable def «$lift_statementIR:clause:6» (input0 : SpecTec.statementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let statementIR : SpecTec.statementIR := input0; (.bind (.guard (((«sub:statementIR:blockStatementIR» statementIR) = true))) (fun (_ : Unit) => (match («$lift_statementIR:case_7:downcast:0» statementIR) with | some «exec:1» => (let «eval:0» : SpecTec.blockStatementIR := «exec:1»; (let blockStatementIR : SpecTec.blockStatementIR := «eval:0»; (.bind (.call ⟨blockStatement, SpecTecCall.«$lift_blockStatementIR» blockStatementIR⟩) (fun («exec:2» : blockStatement) => (let «eval:1» : blockStatement := «exec:2»; (.pure (((«cast:blockStatement:statement» «eval:1») : statement)))))))) | none => .unmatch))))


noncomputable def «$lift_statementIR:clause:7» (input0 : SpecTec.statementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let statementIR : SpecTec.statementIR := input0; (.bind (.guard (((«sub:statementIR:conditionalStatementIR» statementIR) = true))) (fun (_ : Unit) => (match («$lift_statementIR:case_8:downcast:0» statementIR) with | some «exec:1» => (let «eval:0» : SpecTec.conditionalStatementIR := «exec:1»; (let conditionalStatementIR : SpecTec.conditionalStatementIR := «eval:0»; (.bind (.call ⟨conditionalStatement, SpecTecCall.«$lift_conditionalStatementIR» conditionalStatementIR⟩) (fun («exec:2» : conditionalStatement) => (let «eval:1» : conditionalStatement := «exec:2»; (.pure (((«cast:conditionalStatement:statement» «eval:1») : statement)))))))) | none => .unmatch))))


noncomputable def «$lift_statementIR:clause:8» (input0 : SpecTec.statementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let statementIR : SpecTec.statementIR := input0; (.bind (.guard (((«sub:statementIR:switchStatementIR» statementIR) = true))) (fun (_ : Unit) => (match («$lift_statementIR:case_9:downcast:0» statementIR) with | some «exec:1» => (let «eval:0» : SpecTec.switchStatementIR := «exec:1»; (let switchStatementIR : SpecTec.switchStatementIR := «eval:0»; (.bind (.call ⟨switchStatement, SpecTecCall.«$lift_switchStatementIR» switchStatementIR⟩) (fun («exec:2» : switchStatement) => (let «eval:1» : switchStatement := «exec:2»; (.pure (((«cast:switchStatement:statement» «eval:1») : statement)))))))) | none => .unmatch))))


noncomputable def «$lift_statementIR:clause:9» (input0 : SpecTec.statementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let statementIR : SpecTec.statementIR := input0; (.bind (.call ⟨statement, SpecTecCall.«$sink» statement⟩) (fun («exec:1» : statement) => (let «eval:0» : statement := «exec:1»; (.pure ((«eval:0» : statement)))))))


noncomputable def «$lift_statementIR_clauses» (input0 : statementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_statementIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_statementIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_statementIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_statementIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_statementIR:clause:4»  input0), fun (_ : _root_.Unit) => («$lift_statementIR:clause:5»  input0), fun (_ : _root_.Unit) => («$lift_statementIR:clause:6»  input0), fun (_ : _root_.Unit) => («$lift_statementIR:clause:7»  input0), fun (_ : _root_.Unit) => («$lift_statementIR:clause:8»  input0), fun (_ : _root_.Unit) => («$lift_statementIR:clause:9»  input0)]


noncomputable def «$lift_blockElementStatementIR:clause:0» (input0 : SpecTec.blockElementStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let blockElementStatementIR : SpecTec.blockElementStatementIR := input0; (.bind (.guard (((«sub:blockElementStatementIR:constantDeclarationIR» blockElementStatementIR) = true))) (fun (_ : Unit) => (match («$lift_blockElementStatementIR:case_1:downcast:0» blockElementStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.constantDeclarationIR := «exec:1»; (let constantDeclarationIR : SpecTec.constantDeclarationIR := «eval:0»; (.bind (.call ⟨constantDeclaration, SpecTecCall.«$lift_constantDeclarationIR» constantDeclarationIR⟩) (fun («exec:2» : constantDeclaration) => (let «eval:1» : constantDeclaration := «exec:2»; (.pure (((«cast:constantDeclaration:blockElementStatement» «eval:1») : blockElementStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_blockElementStatementIR:clause:1» (input0 : SpecTec.blockElementStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let blockElementStatementIR : SpecTec.blockElementStatementIR := input0; (.bind (.guard (((«sub:blockElementStatementIR:variableDeclarationIR» blockElementStatementIR) = true))) (fun (_ : Unit) => (match («$lift_blockElementStatementIR:case_2:downcast:0» blockElementStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.variableDeclarationIR := «exec:1»; (let variableDeclarationIR : SpecTec.variableDeclarationIR := «eval:0»; (.bind (.call ⟨variableDeclaration, SpecTecCall.«$lift_variableDeclarationIR» variableDeclarationIR⟩) (fun («exec:2» : variableDeclaration) => (let «eval:1» : variableDeclaration := «exec:2»; (.pure (((«cast:variableDeclaration:blockElementStatement» «eval:1») : blockElementStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_blockElementStatementIR:clause:2» (input0 : SpecTec.blockElementStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let blockElementStatementIR : SpecTec.blockElementStatementIR := input0; (.bind (.guard (((«sub:blockElementStatementIR:statementIR» blockElementStatementIR) = true))) (fun (_ : Unit) => (match («$lift_blockElementStatementIR:case_3:downcast:0» blockElementStatementIR) with | some «exec:1» => (let «eval:0» : SpecTec.statementIR := «exec:1»; (let statementIR : SpecTec.statementIR := «eval:0»; (.bind (.call ⟨statement, SpecTecCall.«$lift_statementIR» statementIR⟩) (fun («exec:2» : statement) => (let «eval:1» : statement := «exec:2»; (.pure (((«cast:statement:blockElementStatement» «eval:1») : blockElementStatement)))))))) | none => .unmatch))))


noncomputable def «$lift_blockElementStatementIR_clauses» (input0 : blockElementStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_blockElementStatementIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_blockElementStatementIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_blockElementStatementIR:clause:2»  input0)]


noncomputable def «$lift_blockStatementIR:clause:0» (input0 : blockStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% `{ % `}» «exec:1» «exec:2» => (let annotationList : SpecTec.annotationList := «exec:1»; (let «blockElementStatementIR*» : (_root_.List blockElementStatementIR) := «exec:2»; (.bind (.call ⟨(_root_.List blockElementStatement), SpecTecCall.«$lift_blockStatementIR:case_1:iter:0» «blockElementStatementIR*»⟩) (fun («exec:3» : (_root_.List blockElementStatement)) => (let «blockElementStatement*» : (_root_.List blockElementStatement) := «exec:3»; (.bind (.call ⟨SpecTec.blockElementStatementList, SpecTecCall.«$unflatten_blockElementStatementList» «blockElementStatement*»⟩) (fun («exec:4» : SpecTec.blockElementStatementList) => (let «eval:2» : SpecTec.blockElementStatementList := «exec:4»; (let blockElementStatementList : SpecTec.blockElementStatementList := «eval:2»; (.pure ((((blockStatement.«% `{ % `}» annotationList blockElementStatementList) : blockStatement) : blockStatement)))))))))))))


noncomputable def «$lift_blockStatementIR_clauses» (input0 : blockStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_blockStatementIR:clause:0»  input0)]


noncomputable def «$lift_blockStatementIR:case_1:iter:0:clause:0» (input0 : (_root_.List blockElementStatementIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List blockElementStatement)) : (_root_.List blockElementStatement)))) | _ :: _ => .unmatch)


noncomputable def «$lift_blockStatementIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.blockElementStatementIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let blockElementStatementIR : SpecTec.blockElementStatementIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.blockElementStatementIR) := «exec:1»; (.bind (.call ⟨SpecTec.blockElementStatement, SpecTecCall.«$lift_blockElementStatementIR» blockElementStatementIR⟩) (fun («exec:3» : SpecTec.blockElementStatement) => (let «eval:1» : SpecTec.blockElementStatement := «exec:3»; (let blockElementStatement : SpecTec.blockElementStatement := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.blockElementStatement), SpecTecCall.«$lift_blockStatementIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.blockElementStatement)) => (let «tail:1» : (_root_.List SpecTec.blockElementStatement) := «exec:4»; (.pure (((blockElementStatement :: «tail:1») : (_root_.List SpecTec.blockElementStatement))))))))))))) | [] => .unmatch)


noncomputable def «$lift_blockStatementIR:case_1:iter:0_clauses» (input0 : (_root_.List blockElementStatementIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_blockStatementIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_blockStatementIR:case_1:iter:0:clause:1»  input0)]

end SpecTec
