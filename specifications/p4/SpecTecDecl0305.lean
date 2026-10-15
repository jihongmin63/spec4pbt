import SpecTecDecl0304

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_unaryExpressionIR_clauses» (input0 : unaryExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_unaryExpressionIR:clause:0»  input0)]


noncomputable def «$lift_binaryExpressionIR:clause:0» (input0 : binaryExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % %» «exec:1» «exec:2» «exec:3» => (let typedExpressionIR_l : typedExpressionIR := «exec:1»; (let binop : SpecTec.binop := «exec:2»; (let typedExpressionIR_r : typedExpressionIR := «exec:3»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_l⟩) (fun («exec:4» : expression) => (let «eval:0» : expression := «exec:4»; (let expression_l : expression := «eval:0»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_r⟩) (fun («exec:5» : expression) => (let «eval:1» : expression := «exec:5»; (let expression_r : expression := «eval:1»; (.pure ((((binaryExpression.«% % %» expression_l binop expression_r) : binaryExpression) : binaryExpression)))))))))))))))


noncomputable def «$lift_binaryExpressionIR_clauses» (input0 : binaryExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_binaryExpressionIR:clause:0»  input0)]


noncomputable def «$lift_ternaryExpressionIR:clause:0» (input0 : ternaryExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% '?' % ':' %» «exec:1» «exec:2» «exec:3» => (let typedExpressionIR_cond : typedExpressionIR := «exec:1»; (let typedExpressionIR_then : typedExpressionIR := «exec:2»; (let typedExpressionIR_else : typedExpressionIR := «exec:3»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_cond⟩) (fun («exec:4» : expression) => (let «eval:0» : expression := «exec:4»; (let expression_cond : expression := «eval:0»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_then⟩) (fun («exec:5» : expression) => (let «eval:1» : expression := «exec:5»; (let expression_then : expression := «eval:1»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_else⟩) (fun («exec:6» : expression) => (let «eval:2» : expression := «exec:6»; (let expression_else : expression := «eval:2»; (.pure ((((ternaryExpression.«% '?' % ':' %» expression_cond expression_then expression_else) : ternaryExpression) : ternaryExpression)))))))))))))))))))


noncomputable def «$lift_ternaryExpressionIR_clauses» (input0 : ternaryExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_ternaryExpressionIR:clause:0»  input0)]


noncomputable def «$lift_castExpressionIR:clause:0» (input0 : castExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`( % `) %» «exec:1» «exec:2» => (let typeIR : SpecTec.typeIR := «exec:1»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:2»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$unroll_typeIR» typeIR⟩) (fun («exec:3» : SpecTec.typeIR) => (let «eval:0» : SpecTec.typeIR := «exec:3»; (let typeIR_unroll : SpecTec.typeIR := «eval:0»; (.bind (.guard (((«sub:typeIR:setTypeIR» typeIR_unroll) = true))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:4» : SpecTec.expression) => (let «eval:1» : SpecTec.expression := «exec:4»; (let expression : SpecTec.expression := «eval:1»; (.pure ((expression : SpecTec.expression))))))))))))))))


noncomputable def «$lift_castExpressionIR:clause:1» (input0 : castExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`( % `) %» «exec:1» «exec:2» => (let typeIR : SpecTec.typeIR := «exec:1»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:2»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$unroll_typeIR» typeIR⟩) (fun («exec:3» : SpecTec.typeIR) => (let «eval:0» : SpecTec.typeIR := «exec:3»; (let typeIR_unroll : SpecTec.typeIR := «eval:0»; (.bind (.guard ((¬ ((«sub:typeIR:setTypeIR» typeIR_unroll) = true)))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:4» : SpecTec.type) => (let «eval:1» : SpecTec.type := «exec:4»; (let type : SpecTec.type := «eval:1»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:5» : SpecTec.expression) => (let «eval:2» : SpecTec.expression := «exec:5»; (let expression : SpecTec.expression := «eval:2»; (.pure ((((SpecTec.expression.«`( % `) %» type expression) : SpecTec.expression) : SpecTec.expression))))))))))))))))))))


noncomputable def «$lift_castExpressionIR_clauses» (input0 : castExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_castExpressionIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_castExpressionIR:clause:1»  input0)]


noncomputable def «$lift_dataExpressionIR:clause:0» (input0 : SpecTec.dataExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataExpressionIR : SpecTec.dataExpressionIR := input0; (.bind (.guard (((«sub:dataExpressionIR:invalidHeaderExpression» dataExpressionIR) = true))) (fun (_ : Unit) => (match («$lift_dataExpressionIR:case_1:downcast:0» dataExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.invalidHeaderExpression := «exec:1»; (let invalidHeaderExpression : SpecTec.invalidHeaderExpression := «eval:0»; (.bind (.guard (((SpecTec.invalidHeaderExpression.«'{#}'») : SpecTec.invalidHeaderExpression) = invalidHeaderExpression)) (fun (_ : Unit) => (.pure ((((dataExpression.«'{#}'») : dataExpression) : dataExpression))))))) | none => .unmatch))))


noncomputable def «$lift_dataExpressionIR:clause:1» (input0 : SpecTec.dataExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataExpressionIR : SpecTec.dataExpressionIR := input0; (.bind (.guard (((«sub:dataExpressionIR:sequenceExpressionIR» dataExpressionIR) = true))) (fun (_ : Unit) => (match («$lift_dataExpressionIR:case_2:downcast:0» dataExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.sequenceExpressionIR := «exec:1»; (let sequenceExpressionIR : SpecTec.sequenceExpressionIR := «eval:0»; (.bind (.guard (((«exec:match:sequenceExpressionIR:SEQ `{ % `}» sequenceExpressionIR) = true))) (fun (_ : Unit) => (match sequenceExpressionIR with | .«SEQ `{ % `}» «exec:2» => (let «typedExpressionIR*» : (_root_.List typedExpressionIR) := «exec:2»; (.bind (.call ⟨SpecTec.expressionList, SpecTecCall.«$lift_typedExpressionListIR» «typedExpressionIR*»⟩) (fun («exec:3» : SpecTec.expressionList) => (let «eval:1» : SpecTec.expressionList := «exec:3»; (let expressionList : SpecTec.expressionList := «eval:1»; (.pure ((((dataExpression.«`{ % % `}» («cast:expressionList:sequenceOrRecordElementExpression» expressionList) ((trailingCommaOpt._EMPTY) : trailingCommaOpt)) : dataExpression) : dataExpression)))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$lift_dataExpressionIR:clause:2» (input0 : SpecTec.dataExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataExpressionIR : SpecTec.dataExpressionIR := input0; (.bind (.guard (((«sub:dataExpressionIR:sequenceExpressionIR» dataExpressionIR) = true))) (fun (_ : Unit) => (match («$lift_dataExpressionIR:case_3:downcast:0» dataExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.sequenceExpressionIR := «exec:1»; (let sequenceExpressionIR : SpecTec.sequenceExpressionIR := «eval:0»; (.bind (.guard (((«exec:match:sequenceExpressionIR:SEQ `{ % ',' '...' `}» sequenceExpressionIR) = true))) (fun (_ : Unit) => (match sequenceExpressionIR with | .«SEQ `{ % ',' '...' `}» «exec:2» => (let «typedExpressionIR*» : (_root_.List typedExpressionIR) := «exec:2»; (.bind (.call ⟨(_root_.List expression), SpecTecCall.«$lift_dataExpressionIR:case_3:iter:1» «typedExpressionIR*»⟩) (fun («exec:3» : (_root_.List expression)) => (let «expression*» : (_root_.List expression) := «exec:3»; (let «expression_with_default*» : (_root_.List expression) := («expression*» ++ ([((expression.«'...'») : expression)] : (_root_.List expression))); (.bind (.call ⟨SpecTec.expressionList, SpecTecCall.«$lift_typedExpressionListIR» «typedExpressionIR*»⟩) (fun («exec:4» : SpecTec.expressionList) => (let «eval:3» : SpecTec.expressionList := «exec:4»; (let expressionList : SpecTec.expressionList := «eval:3»; (.pure ((((dataExpression.«`{ % % `}» («cast:expressionList:sequenceOrRecordElementExpression» expressionList) ((trailingCommaOpt._EMPTY) : trailingCommaOpt)) : dataExpression) : dataExpression)))))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$lift_dataExpressionIR:clause:3» (input0 : SpecTec.dataExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataExpressionIR : SpecTec.dataExpressionIR := input0; (.bind (.guard (((«sub:dataExpressionIR:recordExpressionIR» dataExpressionIR) = true))) (fun (_ : Unit) => (match («$lift_dataExpressionIR:case_4:downcast:0» dataExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.recordExpressionIR := «exec:1»; (let recordExpressionIR : SpecTec.recordExpressionIR := «eval:0»; (.bind (.guard (((«exec:match:recordExpressionIR:RECORD `{ % `}» recordExpressionIR) = true))) (fun (_ : Unit) => (match recordExpressionIR with | .«RECORD `{ % `}» «exec:2» => (let «namedExpressionIR*» : (_root_.List namedExpressionIR) := «exec:2»; (.bind (.call ⟨(_root_.List namedExpression), SpecTecCall.«$lift_dataExpressionIR:case_4:iter:1» «namedExpressionIR*»⟩) (fun («exec:3» : (_root_.List namedExpression)) => (let «namedExpression*» : (_root_.List namedExpression) := «exec:3»; (.bind (.call ⟨SpecTec.recordElementExpression, SpecTecCall.«$unflatten_recordElementExpression» «namedExpression*»⟩) (fun («exec:4» : SpecTec.recordElementExpression) => (let «eval:3» : SpecTec.recordElementExpression := «exec:4»; (let recordElementExpression : SpecTec.recordElementExpression := «eval:3»; (.pure ((((dataExpression.«`{ % % `}» («cast:recordElementExpression:sequenceOrRecordElementExpression» recordElementExpression) ((trailingCommaOpt._EMPTY) : trailingCommaOpt)) : dataExpression) : dataExpression))))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$lift_dataExpressionIR:clause:4» (input0 : SpecTec.dataExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataExpressionIR : SpecTec.dataExpressionIR := input0; (.bind (.guard (((«sub:dataExpressionIR:recordExpressionIR» dataExpressionIR) = true))) (fun (_ : Unit) => (match («$lift_dataExpressionIR:case_5:downcast:0» dataExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.recordExpressionIR := «exec:1»; (let recordExpressionIR : SpecTec.recordExpressionIR := «eval:0»; (.bind (.guard (((«exec:match:recordExpressionIR:RECORD `{ % ',' '...' `}» recordExpressionIR) = true))) (fun (_ : Unit) => (match recordExpressionIR with | .«RECORD `{ % ',' '...' `}» «exec:2» => (let «namedExpressionIR*» : (_root_.List namedExpressionIR) := «exec:2»; (.bind (.call ⟨(_root_.List namedExpression), SpecTecCall.«$lift_dataExpressionIR:case_5:iter:1» «namedExpressionIR*»⟩) (fun («exec:3» : (_root_.List namedExpression)) => (let «namedExpression*» : (_root_.List namedExpression) := «exec:3»; (.bind (.call ⟨SpecTec.recordElementExpression, SpecTecCall.«$unflatten_recordElementExpression_with_default» «namedExpression*»⟩) (fun («exec:4» : SpecTec.recordElementExpression) => (let «eval:3» : SpecTec.recordElementExpression := «exec:4»; (let recordElementExpression : SpecTec.recordElementExpression := «eval:3»; (.pure ((((dataExpression.«`{ % % `}» («cast:recordElementExpression:sequenceOrRecordElementExpression» recordElementExpression) ((trailingCommaOpt._EMPTY) : trailingCommaOpt)) : dataExpression) : dataExpression))))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$lift_dataExpressionIR_clauses» (input0 : dataExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_dataExpressionIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_dataExpressionIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_dataExpressionIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_dataExpressionIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_dataExpressionIR:clause:4»  input0)]


noncomputable def «$lift_dataExpressionIR:case_3:iter:1:clause:0» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List expression)) : (_root_.List expression)))) | _ :: _ => .unmatch)


noncomputable def «$lift_dataExpressionIR:case_3:iter:1:clause:1» (input0 : (_root_.List SpecTec.typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typedExpressionIR) := «exec:1»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:3» : SpecTec.expression) => (let «eval:2» : SpecTec.expression := «exec:3»; (let expression : SpecTec.expression := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.expression), SpecTecCall.«$lift_dataExpressionIR:case_3:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.expression)) => (let «tail:1» : (_root_.List SpecTec.expression) := «exec:4»; (.pure (((expression :: «tail:1») : (_root_.List SpecTec.expression))))))))))))) | [] => .unmatch)


noncomputable def «$lift_dataExpressionIR:case_3:iter:1_clauses» (input0 : (_root_.List typedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_dataExpressionIR:case_3:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_dataExpressionIR:case_3:iter:1:clause:1»  input0)]


noncomputable def «$lift_dataExpressionIR:case_4:iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List namedExpression)) : (_root_.List namedExpression)))) | _ :: _ => .unmatch)


noncomputable def «$lift_dataExpressionIR:case_4:iter:1:clause:1» (input0 : (_root_.List SpecTec.namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let namedExpressionIR : SpecTec.namedExpressionIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.namedExpressionIR) := «exec:1»; (.bind (.call ⟨SpecTec.namedExpression, SpecTecCall.«$lift_namedExpressionIR» namedExpressionIR⟩) (fun («exec:3» : SpecTec.namedExpression) => (let «eval:2» : SpecTec.namedExpression := «exec:3»; (let namedExpression : SpecTec.namedExpression := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.namedExpression), SpecTecCall.«$lift_dataExpressionIR:case_4:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.namedExpression)) => (let «tail:1» : (_root_.List SpecTec.namedExpression) := «exec:4»; (.pure (((namedExpression :: «tail:1») : (_root_.List SpecTec.namedExpression))))))))))))) | [] => .unmatch)


noncomputable def «$lift_dataExpressionIR:case_4:iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_dataExpressionIR:case_4:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_dataExpressionIR:case_4:iter:1:clause:1»  input0)]


noncomputable def «$lift_dataExpressionIR:case_5:iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List namedExpression)) : (_root_.List namedExpression)))) | _ :: _ => .unmatch)


noncomputable def «$lift_dataExpressionIR:case_5:iter:1:clause:1» (input0 : (_root_.List SpecTec.namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let namedExpressionIR : SpecTec.namedExpressionIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.namedExpressionIR) := «exec:1»; (.bind (.call ⟨SpecTec.namedExpression, SpecTecCall.«$lift_namedExpressionIR» namedExpressionIR⟩) (fun («exec:3» : SpecTec.namedExpression) => (let «eval:2» : SpecTec.namedExpression := «exec:3»; (let namedExpression : SpecTec.namedExpression := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.namedExpression), SpecTecCall.«$lift_dataExpressionIR:case_5:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.namedExpression)) => (let «tail:1» : (_root_.List SpecTec.namedExpression) := «exec:4»; (.pure (((namedExpression :: «tail:1») : (_root_.List SpecTec.namedExpression))))))))))))) | [] => .unmatch)


noncomputable def «$lift_dataExpressionIR:case_5:iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_dataExpressionIR:case_5:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_dataExpressionIR:case_5:iter:1:clause:1»  input0)]


noncomputable def «$lift_memberAccessBaseIR:clause:0» (input0 : SpecTec.memberAccessBaseIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let memberAccessBaseIR : SpecTec.memberAccessBaseIR := input0; (.bind (.guard (((«exec:match:memberAccessBaseIR:TYPE» memberAccessBaseIR) = true))) (fun (_ : Unit) => (match memberAccessBaseIR with | .TYPE «exec:1» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:1»; (.bind (.call ⟨prefixedTypeName, SpecTecCall.«$lift_prefixedNameIR_as_prefixedTypeName» prefixedNameIR⟩) (fun («exec:2» : prefixedTypeName) => (let «eval:0» : prefixedTypeName := «exec:2»; (.pure (((«cast:prefixedTypeName:memberAccessBase» «eval:0») : memberAccessBase))))))) | _ => .unmatch))))


noncomputable def «$lift_memberAccessBaseIR:clause:1» (input0 : SpecTec.memberAccessBaseIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let memberAccessBaseIR : SpecTec.memberAccessBaseIR := input0; (.bind (.guard (((«sub:memberAccessBaseIR:typedExpressionIR» memberAccessBaseIR) = true))) (fun (_ : Unit) => (match («$lift_memberAccessBaseIR:case_2:downcast:0» memberAccessBaseIR) with | some «exec:1» => (let «eval:0» : SpecTec.typedExpressionIR := «exec:1»; (let typedExpressionIR : SpecTec.typedExpressionIR := «eval:0»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:2» : expression) => (let «eval:1» : expression := «exec:2»; (.pure (((«cast:expression:memberAccessBase» «eval:1») : memberAccessBase)))))))) | none => .unmatch))))


noncomputable def «$lift_memberAccessBaseIR_clauses» (input0 : memberAccessBaseIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_memberAccessBaseIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_memberAccessBaseIR:clause:1»  input0)]


noncomputable def «$lift_memberAccessExpressionIR:clause:0» (input0 : memberAccessExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% '.' %» «exec:1» «exec:2» => (let memberAccessBaseIR : SpecTec.memberAccessBaseIR := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (.bind (.call ⟨SpecTec.memberAccessBase, SpecTecCall.«$lift_memberAccessBaseIR» memberAccessBaseIR⟩) (fun («exec:3» : SpecTec.memberAccessBase) => (let «eval:0» : SpecTec.memberAccessBase := «exec:3»; (let memberAccessBase : SpecTec.memberAccessBase := «eval:0»; (.bind (.call ⟨SpecTec.member, SpecTecCall.«$lift_nameIR_as_member» nameIR⟩) (fun («exec:4» : SpecTec.member) => (let «eval:1» : SpecTec.member := «exec:4»; (let member : SpecTec.member := «eval:1»; (.pure ((((memberAccessExpression.«% '.' %» memberAccessBase member) : memberAccessExpression) : memberAccessExpression))))))))))))))


noncomputable def «$lift_memberAccessExpressionIR_clauses» (input0 : memberAccessExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_memberAccessExpressionIR:clause:0»  input0)]


noncomputable def «$lift_indexAccessExpressionIR:clause:0» (input0 : indexAccessExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% `[ % `]» «exec:1» «exec:2» => (let typedExpressionIR_base : typedExpressionIR := «exec:1»; (let typedExpressionIR_index : typedExpressionIR := «exec:2»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_base⟩) (fun («exec:3» : expression) => (let «eval:0» : expression := «exec:3»; (let expression_base : expression := «eval:0»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_index⟩) (fun («exec:4» : expression) => (let «eval:1» : expression := «exec:4»; (let expression_index : expression := «eval:1»; (.pure ((((indexAccessExpression.«% `[ % `]» expression_base expression_index) : indexAccessExpression) : indexAccessExpression))))))))))))))


noncomputable def «$lift_indexAccessExpressionIR_clauses» (input0 : indexAccessExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_indexAccessExpressionIR:clause:0»  input0)]


noncomputable def «$lift_sliceAccessExpressionIR:clause:0» (input0 : sliceAccessExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% `[ % % % `]» «exec:1» «exec:2» «exec:3» «exec:4» => (let typedExpressionIR_base : typedExpressionIR := «exec:1»; (let typedExpressionIR_hi : typedExpressionIR := «exec:2»; (let sliceop : SpecTec.sliceop := «exec:3»; (let typedExpressionIR_lo : typedExpressionIR := «exec:4»; (.bind (.guard (((«exec:match:sliceop:':'» sliceop) = true))) (fun (_ : Unit) => (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_base⟩) (fun («exec:5» : expression) => (let «eval:0» : expression := «exec:5»; (let expression_base : expression := «eval:0»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_hi⟩) (fun («exec:6» : expression) => (let «eval:1» : expression := «exec:6»; (let expression_hi : expression := «eval:1»; (.bind (.call ⟨expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR_lo⟩) (fun («exec:7» : expression) => (let «eval:2» : expression := «exec:7»; (let expression_lo : expression := «eval:2»; (.pure ((((sliceAccessExpression.«% `[ % % % `]» expression_base expression_hi ((SpecTec.sliceop.«':'») : SpecTec.sliceop) expression_lo) : sliceAccessExpression) : sliceAccessExpression))))))))))))))))))))))


noncomputable def «$lift_sliceAccessExpressionIR_clauses» (input0 : sliceAccessExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_sliceAccessExpressionIR:clause:0»  input0)]

end SpecTec
