import SpecTecDecl0313

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_parserLocalDeclarationIR:clause:2» (input0 : SpecTec.parserLocalDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserLocalDeclarationIR : SpecTec.parserLocalDeclarationIR := input0; (.bind (.guard (((«sub:parserLocalDeclarationIR:variableDeclarationIR» parserLocalDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_parserLocalDeclarationIR:case_3:downcast:0» parserLocalDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.variableDeclarationIR := «exec:1»; (let variableDeclarationIR : SpecTec.variableDeclarationIR := «eval:0»; (.bind (.call ⟨variableDeclaration, SpecTecCall.«$lift_variableDeclarationIR» variableDeclarationIR⟩) (fun («exec:2» : variableDeclaration) => (let «eval:1» : variableDeclaration := «exec:2»; (.pure (((«cast:variableDeclaration:parserLocalDeclaration» «eval:1») : parserLocalDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_parserLocalDeclarationIR:clause:3» (input0 : SpecTec.parserLocalDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserLocalDeclarationIR : SpecTec.parserLocalDeclarationIR := input0; (.bind (.guard (((«sub:parserLocalDeclarationIR:valueSetDeclarationIR» parserLocalDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_parserLocalDeclarationIR:case_4:downcast:0» parserLocalDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.valueSetDeclarationIR := «exec:1»; (let valueSetDeclarationIR : SpecTec.valueSetDeclarationIR := «eval:0»; (.bind (.call ⟨valueSetDeclaration, SpecTecCall.«$lift_valueSetDeclarationIR» valueSetDeclarationIR⟩) (fun («exec:2» : valueSetDeclaration) => (let «eval:1» : valueSetDeclaration := «exec:2»; (.pure (((«cast:valueSetDeclaration:parserLocalDeclaration» «eval:1») : parserLocalDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_parserLocalDeclarationIR_clauses» (input0 : parserLocalDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserLocalDeclarationIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_parserLocalDeclarationIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_parserLocalDeclarationIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_parserLocalDeclarationIR:clause:3»  input0)]


noncomputable def «$lift_parserLocalDeclarationListIR:case_1:iter:0:clause:0» (input0 : (_root_.List parserLocalDeclarationIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List parserLocalDeclaration)) : (_root_.List parserLocalDeclaration)))) | _ :: _ => .unmatch)


noncomputable def «$lift_parserLocalDeclarationListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.parserLocalDeclarationIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parserLocalDeclarationIR : SpecTec.parserLocalDeclarationIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parserLocalDeclarationIR) := «exec:1»; (.bind (.call ⟨SpecTec.parserLocalDeclaration, SpecTecCall.«$lift_parserLocalDeclarationIR» parserLocalDeclarationIR⟩) (fun («exec:3» : SpecTec.parserLocalDeclaration) => (let «eval:1» : SpecTec.parserLocalDeclaration := «exec:3»; (let parserLocalDeclaration : SpecTec.parserLocalDeclaration := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.parserLocalDeclaration), SpecTecCall.«$lift_parserLocalDeclarationListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parserLocalDeclaration)) => (let «tail:1» : (_root_.List SpecTec.parserLocalDeclaration) := «exec:4»; (.pure (((parserLocalDeclaration :: «tail:1») : (_root_.List SpecTec.parserLocalDeclaration))))))))))))) | [] => .unmatch)


noncomputable def «$lift_parserLocalDeclarationListIR:case_1:iter:0_clauses» (input0 : (_root_.List parserLocalDeclarationIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserLocalDeclarationListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_parserLocalDeclarationListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_parserLocalDeclarationListIR:clause:0» (input0 : (_root_.List parserLocalDeclarationIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parserLocalDeclarationIR*» : (_root_.List parserLocalDeclarationIR) := input0; (.bind (.call ⟨(_root_.List parserLocalDeclaration), SpecTecCall.«$lift_parserLocalDeclarationListIR:case_1:iter:0» «parserLocalDeclarationIR*»⟩) (fun («exec:1» : (_root_.List parserLocalDeclaration)) => (let «parserLocalDeclaration*» : (_root_.List parserLocalDeclaration) := «exec:1»; (.bind (.call ⟨SpecTec.parserLocalDeclarationList, SpecTecCall.«$unflatten_parserLocalDeclarationList» «parserLocalDeclaration*»⟩) (fun («exec:2» : SpecTec.parserLocalDeclarationList) => (let «eval:2» : SpecTec.parserLocalDeclarationList := «exec:2»; (let parserLocalDeclarationList : SpecTec.parserLocalDeclarationList := «eval:2»; (.pure ((parserLocalDeclarationList : SpecTec.parserLocalDeclarationList)))))))))))


noncomputable def «$lift_parserLocalDeclarationListIR_clauses» (input0 : (_root_.List parserLocalDeclarationIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserLocalDeclarationListIR:clause:0»  input0)]


noncomputable def «$lift_parserDeclarationIR:clause:0» (input0 : parserDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% PARSER % `< % ',' % `> `( % `) `( % `) `{ % % `}» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» «exec:8» => (let annotationList : SpecTec.annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := «exec:3»; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := «exec:4»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:5»; (let «constructorParameterIR*» : (_root_.List constructorParameterIR) := «exec:6»; (let «parserLocalDeclarationIR*» : (_root_.List parserLocalDeclarationIR) := «exec:7»; (let «parserStateIR*» : (_root_.List parserStateIR) := «exec:8»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:9» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:9»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (let «typeParameterIR*» : (_root_.List typeParameterIR) := («typeParameterIR_expl*» ++ «typeParameterIR_impl*»); (.bind (.call ⟨SpecTec.typeParameterListOpt, SpecTecCall.«$lift_typeParameterListIR» «typeParameterIR*»⟩) (fun («exec:10» : SpecTec.typeParameterListOpt) => (let «eval:1» : SpecTec.typeParameterListOpt := «exec:10»; (let typeParameterListOpt : SpecTec.typeParameterListOpt := «eval:1»; (.bind (.call ⟨SpecTec.parameterList, SpecTecCall.«$lift_parameterListIR» «parameterIR*»⟩) (fun («exec:11» : SpecTec.parameterList) => (let «eval:2» : SpecTec.parameterList := «exec:11»; (let parameterList : SpecTec.parameterList := «eval:2»; (.bind (.call ⟨SpecTec.constructorParameterListOpt, SpecTecCall.«$lift_constructorParameterListIR» «constructorParameterIR*»⟩) (fun («exec:12» : SpecTec.constructorParameterListOpt) => (let «eval:3» : SpecTec.constructorParameterListOpt := «exec:12»; (let constructorParameterListOpt : SpecTec.constructorParameterListOpt := «eval:3»; (.bind (.call ⟨SpecTec.parserLocalDeclarationList, SpecTecCall.«$lift_parserLocalDeclarationListIR» «parserLocalDeclarationIR*»⟩) (fun («exec:13» : SpecTec.parserLocalDeclarationList) => (let «eval:4» : SpecTec.parserLocalDeclarationList := «exec:13»; (let parserLocalDeclarationList : SpecTec.parserLocalDeclarationList := «eval:4»; (.bind (.call ⟨SpecTec.parserStateList, SpecTecCall.«$lift_parserStateListIR» «parserStateIR*»⟩) (fun («exec:14» : SpecTec.parserStateList) => (let «eval:5» : SpecTec.parserStateList := «exec:14»; (let parserStateList : SpecTec.parserStateList := «eval:5»; (.pure ((((parserDeclaration.«% PARSER % % `( % `) % `{ % % `}» annotationList name typeParameterListOpt parameterList constructorParameterListOpt parserLocalDeclarationList parserStateList) : parserDeclaration) : parserDeclaration)))))))))))))))))))))))))))))))))))))


noncomputable def «$lift_parserDeclarationIR_clauses» (input0 : parserDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parserDeclarationIR:clause:0»  input0)]


noncomputable def «$lift_tableKeyIR:clause:0» (input0 : tableKeyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% '#' % ':' % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:1»; (let _nameIR : SpecTec.nameIR := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (let annotationList : SpecTec.annotationList := «exec:4»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:5» : SpecTec.expression) => (let «eval:0» : SpecTec.expression := «exec:5»; (let expression : SpecTec.expression := «eval:0»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:6» : nonTypeName) => (let «eval:1» : nonTypeName := «exec:6»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:1»); (.pure ((((tableKey.«% ':' % % ';'» expression name annotationList) : tableKey) : tableKey))))))))))))))))


noncomputable def «$lift_tableKeyIR_clauses» (input0 : tableKeyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableKeyIR:clause:0»  input0)]


noncomputable def «$lift_tableKeyListIR:case_1:iter:0:clause:0» (input0 : (_root_.List tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List tableKey)) : (_root_.List tableKey)))) | _ :: _ => .unmatch)


noncomputable def «$lift_tableKeyListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyIR : SpecTec.tableKeyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyIR) := «exec:1»; (.bind (.call ⟨SpecTec.tableKey, SpecTecCall.«$lift_tableKeyIR» tableKeyIR⟩) (fun («exec:3» : SpecTec.tableKey) => (let «eval:1» : SpecTec.tableKey := «exec:3»; (let tableKey : SpecTec.tableKey := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.tableKey), SpecTecCall.«$lift_tableKeyListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.tableKey)) => (let «tail:1» : (_root_.List SpecTec.tableKey) := «exec:4»; (.pure (((tableKey :: «tail:1») : (_root_.List SpecTec.tableKey))))))))))))) | [] => .unmatch)


noncomputable def «$lift_tableKeyListIR:case_1:iter:0_clauses» (input0 : (_root_.List tableKeyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableKeyListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_tableKeyListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_tableKeyListIR:clause:0» (input0 : (_root_.List tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableKeyIR*» : (_root_.List tableKeyIR) := input0; (.bind (.call ⟨(_root_.List tableKey), SpecTecCall.«$lift_tableKeyListIR:case_1:iter:0» «tableKeyIR*»⟩) (fun («exec:1» : (_root_.List tableKey)) => (let «tableKey*» : (_root_.List tableKey) := «exec:1»; (.bind (.call ⟨SpecTec.tableKeyList, SpecTecCall.«$unflatten_tableKeyList» «tableKey*»⟩) (fun («exec:2» : SpecTec.tableKeyList) => (let «eval:2» : SpecTec.tableKeyList := «exec:2»; (let tableKeyList : SpecTec.tableKeyList := «eval:2»; (.pure ((tableKeyList : SpecTec.tableKeyList)))))))))))


noncomputable def «$lift_tableKeyListIR_clauses» (input0 : (_root_.List tableKeyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableKeyListIR:clause:0»  input0)]


noncomputable def «$lift_tableActionReferenceIR:clause:0» (input0 : tableActionReferenceIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % `( % `)» «exec:1» «exec:2» «exec:3» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:1»; (let _controlPlaneNameIR : controlPlaneNameIR := «exec:2»; (let «argumentIR*» : (_root_.List argumentIR) := «exec:3»; (.bind (.call ⟨SpecTec.prefixedNonTypeName, SpecTecCall.«$lift_prefixedNameIR_as_prefixedNonTypeName» prefixedNameIR⟩) (fun («exec:4» : SpecTec.prefixedNonTypeName) => (let «eval:0» : SpecTec.prefixedNonTypeName := «exec:4»; (let prefixedNonTypeName : SpecTec.prefixedNonTypeName := «eval:0»; (.bind (.call ⟨SpecTec.argumentList, SpecTecCall.«$lift_argumentListIR» «argumentIR*»⟩) (fun («exec:5» : SpecTec.argumentList) => (let «eval:1» : SpecTec.argumentList := «exec:5»; (let argumentList : SpecTec.argumentList := «eval:1»; (.pure ((((tableActionReference.«% `( % `)» prefixedNonTypeName argumentList) : tableActionReference) : tableActionReference)))))))))))))))


noncomputable def «$lift_tableActionReferenceIR_clauses» (input0 : tableActionReferenceIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableActionReferenceIR:clause:0»  input0)]


noncomputable def «$lift_tableActionReferenceIR_as_expression:clause:0» (input0 : tableActionReferenceIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % `( % `)» «exec:1» «exec:2» «exec:3» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:1»; (let _controlPlaneNameIR : controlPlaneNameIR := «exec:2»; (let «argumentIR*» : (_root_.List argumentIR) := «exec:3»; (.bind (.call ⟨SpecTec.prefixedNonTypeName, SpecTecCall.«$lift_prefixedNameIR_as_prefixedNonTypeName» prefixedNameIR⟩) (fun («exec:4» : SpecTec.prefixedNonTypeName) => (let «eval:0» : SpecTec.prefixedNonTypeName := «exec:4»; (let prefixedNonTypeName : SpecTec.prefixedNonTypeName := «eval:0»; (.bind (.call ⟨SpecTec.argumentList, SpecTecCall.«$lift_argumentListIR» «argumentIR*»⟩) (fun («exec:5» : SpecTec.argumentList) => (let «eval:1» : SpecTec.argumentList := «exec:5»; (let argumentList : SpecTec.argumentList := «eval:1»; (.pure ((((expression.«% `( % `)» («cast:prefixedNonTypeName:callTarget» prefixedNonTypeName) argumentList) : expression) : expression)))))))))))))))


noncomputable def «$lift_tableActionReferenceIR_as_expression_clauses» (input0 : tableActionReferenceIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableActionReferenceIR_as_expression:clause:0»  input0)]


noncomputable def «$lift_tableActionIR:clause:0» (input0 : tableActionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % '#' `( % ',' % `) ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:1»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:2»; (let _parameterListIR : parameterListIR := «exec:3»; (let _parameterListIR' : parameterListIR := «exec:4»; (.bind (.call ⟨SpecTec.tableActionReference, SpecTecCall.«$lift_tableActionReferenceIR» tableActionReferenceIR⟩) (fun («exec:5» : SpecTec.tableActionReference) => (let «eval:0» : SpecTec.tableActionReference := «exec:5»; (let tableActionReference : SpecTec.tableActionReference := «eval:0»; (.pure ((((tableAction.«% % ';'» annotationList tableActionReference) : tableAction) : tableAction))))))))))))


noncomputable def «$lift_tableActionIR_clauses» (input0 : tableActionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableActionIR:clause:0»  input0)]


noncomputable def «$lift_tableActionListIR:case_1:iter:0:clause:0» (input0 : (_root_.List tableActionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List tableAction)) : (_root_.List tableAction)))) | _ :: _ => .unmatch)


noncomputable def «$lift_tableActionListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableActionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableActionIR : SpecTec.tableActionIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableActionIR) := «exec:1»; (.bind (.call ⟨SpecTec.tableAction, SpecTecCall.«$lift_tableActionIR» tableActionIR⟩) (fun («exec:3» : SpecTec.tableAction) => (let «eval:1» : SpecTec.tableAction := «exec:3»; (let tableAction : SpecTec.tableAction := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.tableAction), SpecTecCall.«$lift_tableActionListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.tableAction)) => (let «tail:1» : (_root_.List SpecTec.tableAction) := «exec:4»; (.pure (((tableAction :: «tail:1») : (_root_.List SpecTec.tableAction))))))))))))) | [] => .unmatch)


noncomputable def «$lift_tableActionListIR:case_1:iter:0_clauses» (input0 : (_root_.List tableActionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableActionListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_tableActionListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_tableActionListIR:clause:0» (input0 : (_root_.List tableActionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableActionIR*» : (_root_.List tableActionIR) := input0; (.bind (.call ⟨(_root_.List tableAction), SpecTecCall.«$lift_tableActionListIR:case_1:iter:0» «tableActionIR*»⟩) (fun («exec:1» : (_root_.List tableAction)) => (let «tableAction*» : (_root_.List tableAction) := «exec:1»; (.bind (.call ⟨SpecTec.tableActionList, SpecTecCall.«$unflatten_tableActionList» «tableAction*»⟩) (fun («exec:2» : SpecTec.tableActionList) => (let «eval:2» : SpecTec.tableActionList := «exec:2»; (let tableActionList : SpecTec.tableActionList := «eval:2»; (.pure ((tableActionList : SpecTec.tableActionList)))))))))))


noncomputable def «$lift_tableActionListIR_clauses» (input0 : (_root_.List tableActionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableActionListIR:clause:0»  input0)]


noncomputable def «$lift_tableEntryIR:clause:0» (input0 : tableEntryIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % % ':' % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let constOptIR : SpecTec.constOptIR := «exec:1»; (let tableEntryPriorityIR? : (_root_.Option tableEntryPriorityIR) := «exec:2»; (let keysetExpressionIR : SpecTec.keysetExpressionIR := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (let annotationList : SpecTec.annotationList := «exec:5»; (.bind (.guard (((_root_.Option.isNone tableEntryPriorityIR?) = true))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.constOpt, SpecTecCall.«$lift_constOptIR» constOptIR⟩) (fun («exec:6» : SpecTec.constOpt) => (let «eval:0» : SpecTec.constOpt := «exec:6»; (let constOpt : SpecTec.constOpt := «eval:0»; (.bind (.call ⟨SpecTec.keysetExpression, SpecTecCall.«$lift_keysetExpressionIR» keysetExpressionIR⟩) (fun («exec:7» : SpecTec.keysetExpression) => (let «eval:1» : SpecTec.keysetExpression := «exec:7»; (let keysetExpression : SpecTec.keysetExpression := «eval:1»; (.bind (.call ⟨SpecTec.tableActionReference, SpecTecCall.«$lift_tableActionReferenceIR» tableActionReferenceIR⟩) (fun («exec:8» : SpecTec.tableActionReference) => (let «eval:2» : SpecTec.tableActionReference := «exec:8»; (let tableActionReference : SpecTec.tableActionReference := «eval:2»; (.pure ((((tableEntry.«% % ':' % % ';'» constOpt keysetExpression tableActionReference annotationList) : tableEntry) : tableEntry)))))))))))))))))))))))


noncomputable def «$lift_tableEntryIR:clause:1» (input0 : tableEntryIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % % ':' % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let constOptIR : SpecTec.constOptIR := «exec:1»; (let tableEntryPriorityOptIR : SpecTec.tableEntryPriorityOptIR := «exec:2»; (let keysetExpressionIR : SpecTec.keysetExpressionIR := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (let annotationList : SpecTec.annotationList := «exec:5»; (.bind (.guard (((_root_.Option.isSome tableEntryPriorityOptIR) = true))) (fun (_ : Unit) => (match tableEntryPriorityOptIR with | some «exec:6» => (let tableEntryPriorityIR : SpecTec.tableEntryPriorityIR := «exec:6»; (.bind (.call ⟨SpecTec.constOpt, SpecTecCall.«$lift_constOptIR» constOptIR⟩) (fun («exec:7» : SpecTec.constOpt) => (let «eval:0» : SpecTec.constOpt := «exec:7»; (let constOpt : SpecTec.constOpt := «eval:0»; (.bind (.call ⟨SpecTec.tableEntryPriority, SpecTecCall.«$lift_tableEntryPriorityIR» tableEntryPriorityIR⟩) (fun («exec:8» : SpecTec.tableEntryPriority) => (let «eval:1» : SpecTec.tableEntryPriority := «exec:8»; (let tableEntryPriority : SpecTec.tableEntryPriority := «eval:1»; (.bind (.call ⟨SpecTec.keysetExpression, SpecTecCall.«$lift_keysetExpressionIR» keysetExpressionIR⟩) (fun («exec:9» : SpecTec.keysetExpression) => (let «eval:2» : SpecTec.keysetExpression := «exec:9»; (let keysetExpression : SpecTec.keysetExpression := «eval:2»; (.bind (.call ⟨SpecTec.tableActionReference, SpecTecCall.«$lift_tableActionReferenceIR» tableActionReferenceIR⟩) (fun («exec:10» : SpecTec.tableActionReference) => (let «eval:3» : SpecTec.tableActionReference := «exec:10»; (let tableActionReference : SpecTec.tableActionReference := «eval:3»; (.pure ((((tableEntry.«% % % ':' % % ';'» constOpt tableEntryPriority keysetExpression tableActionReference annotationList) : tableEntry) : tableEntry)))))))))))))))))))) | none => .unmatch)))))))))


noncomputable def «$lift_tableEntryIR_clauses» (input0 : tableEntryIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableEntryIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_tableEntryIR:clause:1»  input0)]


noncomputable def «$lift_tableEntryListIR:case_1:iter:0:clause:0» (input0 : (_root_.List tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List tableEntry)) : (_root_.List tableEntry)))) | _ :: _ => .unmatch)

end SpecTec
