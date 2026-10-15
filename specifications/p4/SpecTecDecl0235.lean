import SpecTecDecl0234

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_namedValueListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.namedValueIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let namedValueIR : SpecTec.namedValueIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.namedValueIR) := «exec:1»; (.bind (.call ⟨SpecTec.namedExpression, SpecTecCall.«$lift_namedValueIR» namedValueIR⟩) (fun («exec:3» : SpecTec.namedExpression) => (let «eval:1» : SpecTec.namedExpression := «exec:3»; (let namedExpression : SpecTec.namedExpression := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.namedExpression), SpecTecCall.«$lift_namedValueListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.namedExpression)) => (let «tail:1» : (_root_.List SpecTec.namedExpression) := «exec:4»; (.pure (((namedExpression :: «tail:1») : (_root_.List SpecTec.namedExpression))))))))))))) | [] => .unmatch)


noncomputable def «$lift_namedValueListIR:case_1:iter:0_clauses» (input0 : (_root_.List namedValueIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_namedValueListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_namedValueListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_namedValueListIR:clause:0» (input0 : (_root_.List namedValueIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «namedValueIR*» : (_root_.List namedValueIR) := input0; (.bind (.call ⟨(_root_.List namedExpression), SpecTecCall.«$lift_namedValueListIR:case_1:iter:0» «namedValueIR*»⟩) (fun («exec:1» : (_root_.List namedExpression)) => (let «namedExpression*» : (_root_.List namedExpression) := «exec:1»; (.bind (.call ⟨SpecTec.namedExpressionList, SpecTecCall.«$unflatten_namedExpressionList» «namedExpression*»⟩) (fun («exec:2» : SpecTec.namedExpressionList) => (let «eval:2» : SpecTec.namedExpressionList := «exec:2»; (let namedExpressionList : SpecTec.namedExpressionList := «eval:2»; (.pure ((namedExpressionList : SpecTec.namedExpressionList)))))))))))


noncomputable def «$lift_namedValueListIR_clauses» (input0 : (_root_.List namedValueIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_namedValueListIR:clause:0»  input0)]


noncomputable def «$lift_errorAccessExpressionIR:clause:0» (input0 : errorAccessExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ERROR '.' %» «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨SpecTec.member, SpecTecCall.«$lift_nameIR_as_member» nameIR⟩) (fun («exec:2» : SpecTec.member) => (let «eval:0» : SpecTec.member := «exec:2»; (let member : SpecTec.member := «eval:0»; (.pure ((((errorAccessExpression.«ERROR '.' %» member) : errorAccessExpression) : errorAccessExpression)))))))))


noncomputable def «$lift_errorAccessExpressionIR_clauses» (input0 : errorAccessExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_errorAccessExpressionIR:clause:0»  input0)]


noncomputable def «$lift_errorDeclarationIR:clause:0» (input0 : errorDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ERROR `{ % `}» «exec:1» => (let «nameIR*» : (_root_.List nameIR) := «exec:1»; (.bind (.call ⟨SpecTec.nameList, SpecTecCall.«$lift_nameListIR_as_nonTypeNameList» «nameIR*»⟩) (fun («exec:2» : SpecTec.nameList) => (let «eval:0» : SpecTec.nameList := «exec:2»; (let nameList : SpecTec.nameList := «eval:0»; (.pure ((((errorDeclaration.«ERROR `{ % `}» nameList) : errorDeclaration) : errorDeclaration)))))))))


noncomputable def «$lift_errorDeclarationIR_clauses» (input0 : errorDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_errorDeclarationIR:clause:0»  input0)]


noncomputable def «$lift_matchKindDeclarationIR:clause:0» (input0 : matchKindDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«MATCH_KIND `{ % `}» «exec:1» => (let «nameIR*» : (_root_.List nameIR) := «exec:1»; (.bind (.call ⟨SpecTec.nameList, SpecTecCall.«$lift_nameListIR_as_nonTypeNameList» «nameIR*»⟩) (fun («exec:2» : SpecTec.nameList) => (let «eval:0» : SpecTec.nameList := «exec:2»; (let nameList : SpecTec.nameList := «eval:0»; (.pure ((((matchKindDeclaration.«MATCH_KIND `{ % % `}» nameList ((trailingCommaOpt._EMPTY) : trailingCommaOpt)) : matchKindDeclaration) : matchKindDeclaration)))))))))


noncomputable def «$lift_matchKindDeclarationIR_clauses» (input0 : matchKindDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_matchKindDeclarationIR:clause:0»  input0)]


noncomputable def «$unflatten_nonEmptyParameterList:clause:0» (input0 : (_root_.List parameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameter*» : (_root_.List parameter) := input0; (let «parameter'*» : (_root_.List parameter) := «parameter*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameter'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parameter'*» with | «exec:2» :: «exec:1» => (let parameter_h : parameter := «exec:2»; (let «parameter_t*» : (_root_.List parameter) := «exec:1»; (.bind (.call ⟨nonEmptyParameterList, SpecTecCall.«$unflatten_nonEmptyParameterList'» («cast:parameter:nonEmptyParameterList» parameter_h) «parameter_t*»⟩) (fun («exec:3» : nonEmptyParameterList) => (let «eval:0» : nonEmptyParameterList := «exec:3»; (.pure ((«eval:0» : nonEmptyParameterList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_nonEmptyParameterList_clauses» (input0 : (_root_.List parameter)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_nonEmptyParameterList:clause:0»  input0)]


noncomputable def «$unflatten_parameterList:clause:0» (input0 : (_root_.List parameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameter*» : (_root_.List parameter) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameter*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((((parameterList._EMPTY) : parameterList) : parameterList))))))


noncomputable def «$unflatten_parameterList:clause:1» (input0 : (_root_.List parameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameter*» : (_root_.List parameter) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameter*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parameter*» with | «exec:2» :: «exec:1» => (let parameter_h : parameter := «exec:2»; (let «parameter_t*» : (_root_.List parameter) := «exec:1»; (.bind (.call ⟨nonEmptyParameterList, SpecTecCall.«$unflatten_nonEmptyParameterList» (parameter_h :: «parameter_t*»)⟩) (fun («exec:3» : nonEmptyParameterList) => (let «eval:0» : nonEmptyParameterList := «exec:3»; (.pure (((«cast:nonEmptyParameterList:parameterList» «eval:0») : parameterList)))))))) | [] => .unmatch))))


noncomputable def «$unflatten_parameterList_clauses» (input0 : (_root_.List parameter)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_parameterList:clause:0»  input0), fun (_ : _root_.Unit) => («$unflatten_parameterList:clause:1»  input0)]


noncomputable def «$unflatten_constructorParameterList:clause:0» (input0 : (_root_.List constructorParameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «constructorParameter*» : (_root_.List constructorParameter) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «constructorParameter*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((((constructorParameterListOpt._EMPTY) : constructorParameterListOpt) : constructorParameterListOpt))))))


noncomputable def «$unflatten_constructorParameterList:clause:1» (input0 : (_root_.List constructorParameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «constructorParameter*» : (_root_.List constructorParameter) := input0; (.bind (.guard ((«constructorParameter*» ≠ ([] : (_root_.List constructorParameter))))) (fun (_ : Unit) => (.bind (.call ⟨parameterList, SpecTecCall.«$unflatten_parameterList» «constructorParameter*»⟩) (fun («exec:1» : parameterList) => (let «eval:0» : parameterList := «exec:1»; (.pure ((((constructorParameterListOpt.«`( % `)» «eval:0») : constructorParameterListOpt) : constructorParameterListOpt)))))))))


noncomputable def «$unflatten_constructorParameterList_clauses» (input0 : (_root_.List constructorParameter)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_constructorParameterList:clause:0»  input0), fun (_ : _root_.Unit) => («$unflatten_constructorParameterList:clause:1»  input0)]


noncomputable def «$unflatten_parserStateList:clause:0» (input0 : (_root_.List parserState)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parserState*» : (_root_.List parserState) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parserState*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parserState*» with | «exec:2» :: «exec:1» => (let parserState_h : parserState := «exec:2»; (let «parserState_t*» : (_root_.List parserState) := «exec:1»; (.bind (.call ⟨parserStateList, SpecTecCall.«$unflatten_parserStateList'» («cast:parserState:parserStateList» parserState_h) «parserState_t*»⟩) (fun («exec:3» : parserStateList) => (let «eval:0» : parserStateList := «exec:3»; (.pure ((«eval:0» : parserStateList)))))))) | [] => .unmatch))))


noncomputable def «$unflatten_parserStateList_clauses» (input0 : (_root_.List parserState)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_parserStateList:clause:0»  input0)]


noncomputable def «$unflatten_realTypeArgumentList:clause:0» (input0 : (_root_.List realTypeArgument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «realTypeArgument*» : (_root_.List realTypeArgument) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «realTypeArgument*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «realTypeArgument*» with | «exec:2» :: «exec:1» => (let realTypeArgument_h : realTypeArgument := «exec:2»; (let «realTypeArgument_t*» : (_root_.List realTypeArgument) := «exec:1»; (.bind (.call ⟨realTypeArgumentList, SpecTecCall.«$unflatten_realTypeArgumentList'» («cast:realTypeArgument:realTypeArgumentList» realTypeArgument_h) «realTypeArgument_t*»⟩) (fun («exec:3» : realTypeArgumentList) => (let «eval:0» : realTypeArgumentList := «exec:3»; (.pure ((«eval:0» : realTypeArgumentList)))))))) | [] => .unmatch))))


noncomputable def «$unflatten_realTypeArgumentList_clauses» (input0 : (_root_.List realTypeArgument)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_realTypeArgumentList:clause:0»  input0)]


noncomputable def «$unflatten_simpleKeysetExpressionList:clause:0» (input0 : (_root_.List simpleKeysetExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «simpleKeysetExpression*» : (_root_.List simpleKeysetExpression) := input0; (let «simpleKeysetExpression'*» : (_root_.List simpleKeysetExpression) := «simpleKeysetExpression*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «simpleKeysetExpression'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «simpleKeysetExpression'*» with | «exec:2» :: «exec:1» => (let simpleKeysetExpression_h : simpleKeysetExpression := «exec:2»; (let «simpleKeysetExpression_t*» : (_root_.List simpleKeysetExpression) := «exec:1»; (.bind (.call ⟨simpleKeysetExpressionList, SpecTecCall.«$unflatten_simpleKeysetExpressionList'» («cast:simpleKeysetExpression:simpleKeysetExpressionList» simpleKeysetExpression_h) «simpleKeysetExpression_t*»⟩) (fun («exec:3» : simpleKeysetExpressionList) => (let «eval:0» : simpleKeysetExpressionList := «exec:3»; (.pure ((«eval:0» : simpleKeysetExpressionList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_simpleKeysetExpressionList_clauses» (input0 : (_root_.List simpleKeysetExpression)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_simpleKeysetExpressionList:clause:0»  input0)]


noncomputable def «TableType_ok:rule:iter:6:clause:0» (input0 : SpecTec.tableMetadataEnumTypeIR) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableMetadataEnumTypeIR : SpecTec.tableMetadataEnumTypeIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List varTypeIR)) : (_root_.List varTypeIR)))) | _ :: _ => .unmatch))


noncomputable def «TableType_ok:rule:iter:6:clause:1» (input0 : SpecTec.tableMetadataEnumTypeIR) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableMetadataEnumTypeIR : SpecTec.tableMetadataEnumTypeIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let value_enum_field : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (let varTypeIR_enum_field : varTypeIR := ((varTypeIR.«% % % %» ((direction._EMPTY) : direction) («cast:tableMetadataEnumTypeIR:typeIR» tableMetadataEnumTypeIR) ((ctk.LCTK) : ctk) (_root_.Option.some value_enum_field)) : varTypeIR); (.bind (.call ⟨(_root_.List varTypeIR), SpecTecCall.«TableType_ok:rule:iter:6» tableMetadataEnumTypeIR «tail:0»⟩) (fun («exec:3» : (_root_.List varTypeIR)) => (let «tail:1» : (_root_.List varTypeIR) := «exec:3»; (.pure (((varTypeIR_enum_field :: «tail:1») : (_root_.List varTypeIR)))))))))) | [] => .unmatch))


noncomputable def «TableType_ok:rule:iter:6_clauses» (input0 : tableMetadataEnumTypeIR) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («TableType_ok:rule:iter:6:clause:0»  input0 input1), fun (_ : _root_.Unit) => («TableType_ok:rule:iter:6:clause:1»  input0 input1)]


noncomputable def «$unflatten_typeArgumentList:clause:0» (input0 : (_root_.List typeArgument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeArgument*» : (_root_.List typeArgument) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeArgument*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((((typeArgumentList._EMPTY) : typeArgumentList) : typeArgumentList))))))


noncomputable def «$unflatten_typeArgumentList:clause:1» (input0 : (_root_.List typeArgument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeArgument*» : (_root_.List typeArgument) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeArgument*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeArgument*» with | «exec:2» :: «exec:1» => (let typeArgument_h : typeArgument := «exec:2»; (let «typeArgument_t*» : (_root_.List typeArgument) := «exec:1»; (.bind (.call ⟨typeArgumentList, SpecTecCall.«$unflatten_typeArgumentList'» («cast:typeArgument:typeArgumentList» typeArgument_h) «typeArgument_t*»⟩) (fun («exec:3» : typeArgumentList) => (let «eval:0» : typeArgumentList := «exec:3»; (.pure ((«eval:0» : typeArgumentList)))))))) | [] => .unmatch))))


noncomputable def «$unflatten_typeArgumentList_clauses» (input0 : (_root_.List typeArgument)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_typeArgumentList:clause:0»  input0), fun (_ : _root_.Unit) => («$unflatten_typeArgumentList:clause:1»  input0)]


noncomputable def «$lift_typeParameterIR:clause:0» (input0 : typeParameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeId : SpecTec.typeId := input0; (.bind (.call ⟨typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:1» : typeName) => (let «eval:0» : typeName := «exec:1»; (let typeParameter : SpecTec.typeParameter := («cast:typeIdentifier:name» «eval:0»); (.pure ((typeParameter : SpecTec.typeParameter))))))))


noncomputable def «$lift_typeParameterIR_clauses» (input0 : typeParameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeParameterIR:clause:0»  input0)]

end SpecTec
