import SpecTecDecl0266

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Decl_ok:externObjectDeclaration:iter:14:clause:0» (input0 : (_root_.List externConstructorPrototype)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List constructorId)) : (_root_.List constructorId)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:externObjectDeclaration:iter:14:clause:1» (input0 : (_root_.List SpecTec.externConstructorPrototype)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externConstructorPrototype : SpecTec.externConstructorPrototype := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externConstructorPrototype) := «exec:1»; (.bind (.call ⟨SpecTec.constructorId, SpecTecCall.«$constructorId_of_externConstructorPrototype» externConstructorPrototype⟩) (fun («exec:3» : SpecTec.constructorId) => (let «eval:15» : SpecTec.constructorId := «exec:3»; (let constructorId : SpecTec.constructorId := «eval:15»; (.bind (.call ⟨(_root_.List SpecTec.constructorId), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:14» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.constructorId)) => (let «tail:1» : (_root_.List SpecTec.constructorId) := «exec:4»; (.pure (((constructorId :: «tail:1») : (_root_.List SpecTec.constructorId))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:externObjectDeclaration:iter:14_clauses» (input0 : (_root_.List externConstructorPrototype)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:externObjectDeclaration:iter:14:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:externObjectDeclaration:iter:14:clause:1»  input0)]


noncomputable def «$flatten_parserStateList:clause:0» (input0 : SpecTec.parserStateList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserStateList : SpecTec.parserStateList := input0; (.bind (.guard (((«sub:parserStateList:parserState» parserStateList) = true))) (fun (_ : Unit) => (match («$flatten_parserStateList:case_1:downcast:0» parserStateList) with | some «exec:1» => (let «eval:0» : SpecTec.parserState := «exec:1»; (let parserState : SpecTec.parserState := «eval:0»; (.pure ((([parserState] : (_root_.List SpecTec.parserState)) : (_root_.List SpecTec.parserState)))))) | none => .unmatch))))


noncomputable def «$flatten_parserStateList:clause:1» (input0 : SpecTec.parserStateList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserStateList' : SpecTec.parserStateList := input0; (.bind (.guard (((«exec:match:parserStateList:% %» parserStateList') = true))) (fun (_ : Unit) => (match parserStateList' with | .«% %» «exec:1» «exec:2» => (let parserStateList : SpecTec.parserStateList := «exec:1»; (let parserState : SpecTec.parserState := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.parserState), SpecTecCall.«$flatten_parserStateList» parserStateList⟩) (fun («exec:3» : (_root_.List SpecTec.parserState)) => (let «eval:0» : (_root_.List SpecTec.parserState) := «exec:3»; (.pure (((«eval:0» ++ ([parserState] : (_root_.List SpecTec.parserState))) : (_root_.List SpecTec.parserState))))))))) | _ => .unmatch))))


noncomputable def «$flatten_parserStateList_clauses» (input0 : parserStateList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_parserStateList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_parserStateList:clause:1»  input0)]


noncomputable def «$prefixedNonTypeName:clause:0» (input0 : SpecTec.prefixedNonTypeName) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNonTypeName : SpecTec.prefixedNonTypeName := input0; (.bind (.guard (((«sub:prefixedNonTypeName:nonTypeName» prefixedNonTypeName) = true))) (fun (_ : Unit) => (match («$prefixedNonTypeName:case_1:downcast:0» prefixedNonTypeName) with | some «exec:1» => (let «eval:0» : SpecTec.nonTypeName := «exec:1»; (let nonTypeName : SpecTec.nonTypeName := «eval:0»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» («cast:nonTypeName:name» nonTypeName)⟩) (fun («exec:2» : nameIR) => (let «eval:1» : nameIR := «exec:2»; (.pure ((((prefixedNameIR._BARE «eval:1») : prefixedNameIR) : prefixedNameIR)))))))) | none => .unmatch))))


noncomputable def «$prefixedNonTypeName:clause:1» (input0 : SpecTec.prefixedNonTypeName) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNonTypeName : SpecTec.prefixedNonTypeName := input0; (.bind (.guard (((«exec:match:prefixedNonTypeName:_ID '.' %» prefixedNonTypeName) = true))) (fun (_ : Unit) => (match prefixedNonTypeName with | .«_ID '.' %» «exec:1» => (let nonTypeName : SpecTec.nonTypeName := «exec:1»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» («cast:nonTypeName:name» nonTypeName)⟩) (fun («exec:2» : nameIR) => (let «eval:0» : nameIR := «exec:2»; (.pure ((((prefixedNameIR.«'.' %» «eval:0») : prefixedNameIR) : prefixedNameIR))))))) | _ => .unmatch))))


noncomputable def «$prefixedNonTypeName_clauses» (input0 : prefixedNonTypeName) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$prefixedNonTypeName:clause:0»  input0), fun (_ : _root_.Unit) => («$prefixedNonTypeName:clause:1»  input0)]


noncomputable def «$prefixedTypeName:clause:0» (input0 : SpecTec.prefixedTypeName) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedTypeName : SpecTec.prefixedTypeName := input0; (.bind (.guard (((«sub:prefixedTypeName:typeIdentifier» prefixedTypeName) = true))) (fun (_ : Unit) => (match («$prefixedTypeName:case_1:downcast:0» prefixedTypeName) with | some «exec:1» => (let «eval:0» : SpecTec.typeName := «exec:1»; (let typeName : SpecTec.typeName := «eval:0»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» («cast:typeIdentifier:name» typeName)⟩) (fun («exec:2» : nameIR) => (let «eval:1» : nameIR := «exec:2»; (.pure ((((prefixedNameIR._BARE «eval:1») : prefixedNameIR) : prefixedNameIR)))))))) | none => .unmatch))))


noncomputable def «$prefixedTypeName:clause:1» (input0 : SpecTec.prefixedTypeName) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedTypeName : SpecTec.prefixedTypeName := input0; (.bind (.guard (((«exec:match:prefixedTypeName:_TID '.' %» prefixedTypeName) = true))) (fun (_ : Unit) => (match prefixedTypeName with | .«_TID '.' %» «exec:1» => (let typeName : SpecTec.typeName := «exec:1»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» («cast:typeIdentifier:name» typeName)⟩) (fun («exec:2» : nameIR) => (let «eval:0» : nameIR := «exec:2»; (.pure ((((prefixedNameIR.«'.' %» «eval:0») : prefixedNameIR) : prefixedNameIR))))))) | _ => .unmatch))))


noncomputable def «$prefixedTypeName_clauses» (input0 : prefixedTypeName) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$prefixedTypeName:clause:0»  input0), fun (_ : _root_.Unit) => («$prefixedTypeName:clause:1»  input0)]


noncomputable def «$flatten_realTypeArgumentList:clause:0» (input0 : SpecTec.realTypeArgumentList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let realTypeArgumentList : SpecTec.realTypeArgumentList := input0; (.bind (.guard (((«sub:realTypeArgumentList:realTypeArgument» realTypeArgumentList) = true))) (fun (_ : Unit) => (match («$flatten_realTypeArgumentList:case_1:downcast:0» realTypeArgumentList) with | some «exec:1» => (let «eval:0» : SpecTec.realTypeArgument := «exec:1»; (let realTypeArgument : SpecTec.realTypeArgument := «eval:0»; (.pure ((([realTypeArgument] : (_root_.List SpecTec.realTypeArgument)) : (_root_.List SpecTec.realTypeArgument)))))) | none => .unmatch))))


noncomputable def «$flatten_realTypeArgumentList:clause:1» (input0 : SpecTec.realTypeArgumentList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let realTypeArgumentList' : SpecTec.realTypeArgumentList := input0; (.bind (.guard (((«exec:match:realTypeArgumentList:% ',' %» realTypeArgumentList') = true))) (fun (_ : Unit) => (match realTypeArgumentList' with | .«% ',' %» «exec:1» «exec:2» => (let realTypeArgumentList : SpecTec.realTypeArgumentList := «exec:1»; (let realTypeArgument : SpecTec.realTypeArgument := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.realTypeArgument), SpecTecCall.«$flatten_realTypeArgumentList» realTypeArgumentList⟩) (fun («exec:3» : (_root_.List SpecTec.realTypeArgument)) => (let «eval:0» : (_root_.List SpecTec.realTypeArgument) := «exec:3»; (.pure (((«eval:0» ++ ([realTypeArgument] : (_root_.List SpecTec.realTypeArgument))) : (_root_.List SpecTec.realTypeArgument))))))))) | _ => .unmatch))))


noncomputable def «$flatten_realTypeArgumentList_clauses» (input0 : realTypeArgumentList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_realTypeArgumentList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_realTypeArgumentList:clause:1»  input0)]


noncomputable def «$is_singleton_list_expression:clause:0» (input0 : SpecTec.expression) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expression : SpecTec.expression := input0; (let expression' : SpecTec.expression := expression; (.bind (.guard (((«sub:expression:sequenceOrRecordExpression» expression') = true))) (fun (_ : Unit) => (match («$is_singleton_list_expression:case_1:downcast:0» expression') with | some «exec:1» => (let «eval:0» : sequenceOrRecordExpression := «exec:1»; (match «eval:0» with | .«`{ % % `}» «exec:2» «exec:3» => (let sequenceOrRecordElementExpression : SpecTec.sequenceOrRecordElementExpression := «exec:2»; (let trailingCommaOpt : SpecTec.trailingCommaOpt := «exec:3»; (.bind (.guard (((«sub:sequenceOrRecordElementExpression:expression» sequenceOrRecordElementExpression) = true))) (fun (_ : Unit) => (match («$is_singleton_list_expression:case_1:downcast:1» sequenceOrRecordElementExpression) with | some «exec:4» => (let «eval:1» : SpecTec.expression := «exec:4»; (let expression_elem : SpecTec.expression := «eval:1»; (.bind (.guard (((«exec:match:trailingCommaOpt:_EMPTY» trailingCommaOpt) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))) | none => .unmatch))))))) | none => .unmatch)))))


noncomputable def «$is_singleton_list_expression:clause:1» (input0 : SpecTec.expression) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expression : SpecTec.expression := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_singleton_list_expression_clauses» (input0 : expression) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_singleton_list_expression:clause:0»  input0), fun (_ : _root_.Unit) => («$is_singleton_list_expression:clause:1»  input0)]


noncomputable def «$flatten_simpleKeysetExpressionList:clause:0» (input0 : SpecTec.simpleKeysetExpressionList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let simpleKeysetExpressionList : SpecTec.simpleKeysetExpressionList := input0; (.bind (.guard (((«sub:simpleKeysetExpressionList:simpleKeysetExpression» simpleKeysetExpressionList) = true))) (fun (_ : Unit) => (match («$flatten_simpleKeysetExpressionList:case_1:downcast:0» simpleKeysetExpressionList) with | some «exec:1» => (let «eval:0» : SpecTec.simpleKeysetExpression := «exec:1»; (let simpleKeysetExpression : SpecTec.simpleKeysetExpression := «eval:0»; (.pure ((([simpleKeysetExpression] : (_root_.List SpecTec.simpleKeysetExpression)) : (_root_.List SpecTec.simpleKeysetExpression)))))) | none => .unmatch))))


noncomputable def «$flatten_simpleKeysetExpressionList:clause:1» (input0 : SpecTec.simpleKeysetExpressionList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let simpleKeysetExpressionList' : SpecTec.simpleKeysetExpressionList := input0; (.bind (.guard (((«exec:match:simpleKeysetExpressionList:% ',' %» simpleKeysetExpressionList') = true))) (fun (_ : Unit) => (match simpleKeysetExpressionList' with | .«% ',' %» «exec:1» «exec:2» => (let simpleKeysetExpressionList : SpecTec.simpleKeysetExpressionList := «exec:1»; (let simpleKeysetExpression : SpecTec.simpleKeysetExpression := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.simpleKeysetExpression), SpecTecCall.«$flatten_simpleKeysetExpressionList» simpleKeysetExpressionList⟩) (fun («exec:3» : (_root_.List SpecTec.simpleKeysetExpression)) => (let «eval:0» : (_root_.List SpecTec.simpleKeysetExpression) := «exec:3»; (.pure (((«eval:0» ++ ([simpleKeysetExpression] : (_root_.List SpecTec.simpleKeysetExpression))) : (_root_.List SpecTec.simpleKeysetExpression))))))))) | _ => .unmatch))))


noncomputable def «$flatten_simpleKeysetExpressionList_clauses» (input0 : simpleKeysetExpressionList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_simpleKeysetExpressionList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_simpleKeysetExpressionList:clause:1»  input0)]


noncomputable def «SwitchLabel_table_ok:clause:0» (input0 : typingContext) (input1 : typeId) (input2 : SpecTec.switchLabel) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let typeId_table : typeId := input1; (let switchLabel : SpecTec.switchLabel := input2; (.bind (.guard (((SpecTec.switchLabel.DEFAULT) : SpecTec.switchLabel) = switchLabel)) (fun (_ : Unit) => (.pure ((((switchLabelIR.DEFAULT) : switchLabelIR) : switchLabelIR))))))))


noncomputable def «SwitchLabel_table_ok:clause:1» (input0 : typingContext) (input1 : typeId) (input2 : SpecTec.switchLabel) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let typeId_table : typeId := input1; (let switchLabel : SpecTec.switchLabel := input2; (let switchLabel' : SpecTec.switchLabel := switchLabel; (.bind (.guard (((«sub:switchLabel:prefixedNonTypeName» switchLabel') = true))) (fun (_ : Unit) => (match («SwitchLabel_table_ok:expressionNonBrace-prefixedNonTypeName:downcast:0» switchLabel') with | some «exec:1» => (let «eval:0» : SpecTec.prefixedNonTypeName := «exec:1»; (let prefixedNonTypeName : SpecTec.prefixedNonTypeName := «eval:0»; (.bind (.call ⟨SpecTec.prefixedNameIR, SpecTecCall.«$prefixedNonTypeName» prefixedNonTypeName⟩) (fun («exec:2» : SpecTec.prefixedNameIR) => (let «eval:1» : SpecTec.prefixedNameIR := «exec:2»; (let prefixedNameIR : SpecTec.prefixedNameIR := «eval:1»; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:3» => (let nameIR_label : nameIR := «exec:3»; (.bind (.call ⟨_root_.String, SpecTecCall.«$concat_text» (["action_list(", typeId_table, ")"] : (_root_.List _root_.String))⟩) (fun («exec:4» : _root_.String) => (let «eval:2» : _root_.String := «exec:4»; (let typeId_table_enum : typeId := «eval:2»; (.bind (.call ⟨_root_.String, SpecTecCall.«$concat_text» ([typeId_table_enum, ".", nameIR_label] : (_root_.List typeId))⟩) (fun («exec:5» : _root_.String) => (let «eval:3» : _root_.String := «exec:5»; (let id_label : id := «eval:3»; (.bind (.call ⟨(_root_.Option varTypeIR), SpecTecCall.«$find_var_t» ((SpecTec.prefixedNameIR._BARE id_label) : SpecTec.prefixedNameIR) ((cursor.LOCAL) : cursor) TC⟩) (fun («exec:6» : (_root_.Option varTypeIR)) => (let «eval:4» : (_root_.Option varTypeIR) := «exec:6»; (let varTypeIR? : (_root_.Option varTypeIR) := «eval:4»; (.bind (.guard (((_root_.Option.isSome varTypeIR?) = true))) (fun (_ : Unit) => (match varTypeIR? with | some «exec:7» => (match «exec:7» with | .«% % % %» «exec:8» «exec:9» «exec:10» «exec:11» => (let _direction : direction := «exec:8»; (let typeIR_label : typeIR := «exec:9»; (let ctk_label : ctk := «exec:10»; (let value? : (_root_.Option value) := «exec:11»; (.bind (.guard (((_root_.Option.isSome value?) = true))) (fun (_ : Unit) => (match value? with | some «exec:12» => (let value_label : value := «exec:12»; (.bind (.guard (((value.«TABLE_ENUM % '.' %» typeId_table_enum nameIR_label) : value) = value_label)) (fun (_ : Unit) => (let typedExpressionIR_label : typedExpressionIR := ((typedExpressionIR.«% '#' %» ((expressionIR._BARE nameIR_label) : expressionIR) ((expressionNoteIR.«`( % % `)» typeIR_label ctk_label) : expressionNoteIR)) : typedExpressionIR); (.pure (((«cast:typedExpressionIR:switchLabelIR» typedExpressionIR_label) : switchLabelIR))))))) | none => .unmatch)))))))) | none => .unmatch)))))))))))))))) | _ => .unmatch))))))))) | none => .unmatch)))))))


noncomputable def SwitchLabel_table_ok_clauses (input0 : typingContext) (input1 : typeId) (input2 : switchLabel) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («SwitchLabel_table_ok:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («SwitchLabel_table_ok:clause:1»  input0 input1 input2)]


noncomputable def «$match_switchLabelIR_table:clause:0» (input0 : SpecTec.id) (input1 : SpecTec.switchLabelIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (let switchLabelIR : SpecTec.switchLabelIR := input1; (.bind (.guard (((«exec:match:switchLabelIR:DEFAULT» switchLabelIR) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))


noncomputable def «$match_switchLabelIR_table:clause:1» (input0 : SpecTec.id) (input1 : SpecTec.switchLabelIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (let switchLabelIR : SpecTec.switchLabelIR := input1; (.bind (.guard (((«sub:switchLabelIR:typedExpressionIR» switchLabelIR) = true))) (fun (_ : Unit) => (match («$match_switchLabelIR_table:case_2:downcast:0» switchLabelIR) with | some «exec:1» => (let «eval:0» : typedExpressionIR := «exec:1»; (match «eval:0» with | .«% '#' %» «exec:2» «exec:3» => (let expressionIR : SpecTec.expressionIR := «exec:2»; (let _expressionNoteIR : expressionNoteIR := «exec:3»; (.bind (.guard (((«sub:expressionIR:prefixedNameIR» expressionIR) = true))) (fun (_ : Unit) => (match («$match_switchLabelIR_table:case_2:downcast:1» expressionIR) with | some «exec:4» => (let «eval:1» : SpecTec.prefixedNameIR := «exec:4»; (let prefixedNameIR : SpecTec.prefixedNameIR := «eval:1»; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:5» => (let id' : SpecTec.id := «exec:5»; (.bind (.guard (id' = id)) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch))))) | none => .unmatch))))))) | none => .unmatch)))))


noncomputable def «$match_switchLabelIR_table:clause:2» (input0 : SpecTec.id) (input1 : switchLabelIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (let _switchLabelIR : switchLabelIR := input1; (.pure ((false : _root_.Bool)))))


noncomputable def «$match_switchLabelIR_table_clauses» (input0 : id) (input1 : switchLabelIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_switchLabelIR_table:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$match_switchLabelIR_table:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$match_switchLabelIR_table:clause:2»  input0 input1)]


noncomputable def «SwitchCases_table_eval:clause:0» (input0 : SpecTec.id) (input1 : switchCaseListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (let «switchCaseIR''''*» : (_root_.List switchCaseIR) := input1; (.bind (.guard (([] : (_root_.List switchCaseIR)) = «switchCaseIR''''*»)) (fun (_ : Unit) => (.pure ((((_root_.Option.none) : (_root_.Option blockStatementIR)) : (_root_.Option blockStatementIR))))))))


noncomputable def «SwitchCases_table_eval:clause:1» (input0 : SpecTec.id) (input1 : switchCaseListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (let «switchCaseIR''''*» : (_root_.List switchCaseIR) := input1; (let «switchCaseIR'''''*» : (_root_.List switchCaseIR) := «switchCaseIR''''*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «switchCaseIR'''''*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «switchCaseIR'''''*» with | «exec:2» :: «exec:1» => (let switchCaseIR_h : switchCaseIR := «exec:2»; (let «switchCaseIR_t*» : (_root_.List switchCaseIR) := «exec:1»; (let switchCaseIR'''''' : switchCaseIR := switchCaseIR_h; (.bind (.guard (((«exec:match:switchCaseIR:% ':' %» switchCaseIR'''''') = true))) (fun (_ : Unit) => (match switchCaseIR'''''' with | .«% ':' %» «exec:3» «exec:4» => (let switchLabelIR_h : switchLabelIR := «exec:3»; (let blockStatementIR_h : blockStatementIR := «exec:4»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$match_switchLabelIR_table» id switchLabelIR_h⟩) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some blockStatementIR_h) : (_root_.Option blockStatementIR))))))))))) | _ => .unmatch)))))) | [] => .unmatch))))))


noncomputable def «SwitchCases_table_eval:clause:2» (input0 : SpecTec.id) (input1 : switchCaseListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (let «switchCaseIR''''*» : (_root_.List switchCaseIR) := input1; (let «switchCaseIR'''''*» : (_root_.List switchCaseIR) := «switchCaseIR''''*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «switchCaseIR'''''*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «switchCaseIR'''''*» with | «exec:2» :: «exec:1» => (let switchCaseIR_h : switchCaseIR := «exec:2»; (let «switchCaseIR_t*» : (_root_.List switchCaseIR) := «exec:1»; (let switchCaseIR'''''' : switchCaseIR := switchCaseIR_h; (.bind (.guard (((«exec:match:switchCaseIR:% ':' %» switchCaseIR'''''') = true))) (fun (_ : Unit) => (match switchCaseIR'''''' with | .«% ':' %» «exec:3» «exec:4» => (let switchLabelIR_h : switchLabelIR := «exec:3»; (let blockStatementIR_h : blockStatementIR := «exec:4»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$match_switchLabelIR_table» id switchLabelIR_h⟩) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.Option blockStatementIR), SpecTecCall.SwitchCases_table_eval id «switchCaseIR_t*»⟩) (fun («exec:6» : (_root_.Option blockStatementIR)) => (let blockStatementIR? : (_root_.Option blockStatementIR) := «exec:6»; (.pure ((blockStatementIR? : (_root_.Option blockStatementIR)))))))))))))) | _ => .unmatch)))))) | [] => .unmatch))))))


noncomputable def «SwitchCases_table_eval:clause:3» (input0 : SpecTec.id) (input1 : switchCaseListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (let «switchCaseIR''''*» : (_root_.List switchCaseIR) := input1; (let «switchCaseIR'''''*» : (_root_.List switchCaseIR) := «switchCaseIR''''*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «switchCaseIR'''''*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «switchCaseIR'''''*» with | «exec:2» :: «exec:1» => (let switchCaseIR_h : switchCaseIR := «exec:2»; (let «switchCaseIR_t*» : (_root_.List switchCaseIR) := «exec:1»; (let switchCaseIR'''''' : switchCaseIR := switchCaseIR_h; (.bind (.guard (((«exec:match:switchCaseIR:% ':'» switchCaseIR'''''') = true))) (fun (_ : Unit) => (match switchCaseIR'''''' with | .«% ':'» «exec:3» => (let switchLabelIR_h : switchLabelIR := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$match_switchLabelIR_table» id switchLabelIR_h⟩) (fun («exec:4» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:4»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«SwitchCases_table_eval:cons-fallthrough-match:iter:1» «switchCaseIR_t*»⟩) (fun («exec:5» : (_root_.List _root_.Bool)) => (let «eval:3» : (_root_.List _root_.Bool) := «exec:5»; (.bind (.call ⟨(_root_.List switchCaseIR), SpecTecCall.«$filter_» switchCaseIR «switchCaseIR_t*» «eval:3»⟩) (fun («exec:6» : (_root_.List switchCaseIR)) => (let «eval:4» : (_root_.List switchCaseIR) := «exec:6»; (let «switchCaseIR''''''''*» : (_root_.List switchCaseIR) := «eval:4»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «switchCaseIR''''''''*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «switchCaseIR''''''''*» with | «exec:8» :: «exec:7» => (let switchCaseIR''''''' : switchCaseIR := «exec:8»; (let «_switchCaseIR*» : (_root_.List switchCaseIR) := «exec:7»; (.bind (.guard (((«exec:match:switchCaseIR:% ':' %» switchCaseIR''''''') = true))) (fun (_ : Unit) => (match switchCaseIR''''''' with | .«% ':' %» «exec:9» «exec:10» => (let _switchLabelIR : switchLabelIR := «exec:9»; (let blockStatementIR : SpecTec.blockStatementIR := «exec:10»; (.pure (((_root_.Option.some blockStatementIR) : (_root_.Option SpecTec.blockStatementIR)))))) | _ => .unmatch))))) | [] => .unmatch)))))))))))))))) | _ => .unmatch)))))) | [] => .unmatch))))))

end SpecTec
