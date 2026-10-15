import SpecTecDecl0163

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_value_clauses» (input0 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_value:clause:0»  input0)]


noncomputable def «$unflatten_typeParameterList':clause:0» (input0 : SpecTec.typeParameterList) (input1 : (_root_.List typeParameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeParameterList : SpecTec.typeParameterList := input0; (let «typeParameter*» : (_root_.List typeParameter) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeParameter*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((typeParameterList : SpecTec.typeParameterList)))))))


noncomputable def «$unflatten_typeParameterList':clause:1» (input0 : SpecTec.typeParameterList) (input1 : (_root_.List typeParameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeParameterList : SpecTec.typeParameterList := input0; (let «typeParameter*» : (_root_.List typeParameter) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeParameter*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeParameter*» with | «exec:2» :: «exec:1» => (let typeParameter_h : typeParameter := «exec:2»; (let «typeParameter_t*» : (_root_.List typeParameter) := «exec:1»; (.bind (.call ⟨SpecTec.typeParameterList, SpecTecCall.«$unflatten_typeParameterList'» ((SpecTec.typeParameterList.«% ',' %» typeParameterList typeParameter_h) : SpecTec.typeParameterList) «typeParameter_t*»⟩) (fun («exec:3» : SpecTec.typeParameterList) => (let «eval:0» : SpecTec.typeParameterList := «exec:3»; (.pure ((«eval:0» : SpecTec.typeParameterList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_typeParameterList'_clauses» (input0 : typeParameterList) (input1 : (_root_.List typeParameter)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_typeParameterList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_typeParameterList':clause:1»  input0 input1)]


noncomputable def «$unflatten_nonEmptyParameterList':clause:0» (input0 : SpecTec.nonEmptyParameterList) (input1 : (_root_.List parameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nonEmptyParameterList : SpecTec.nonEmptyParameterList := input0; (let «parameter*» : (_root_.List parameter) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameter*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((nonEmptyParameterList : SpecTec.nonEmptyParameterList)))))))


noncomputable def «$unflatten_nonEmptyParameterList':clause:1» (input0 : SpecTec.nonEmptyParameterList) (input1 : (_root_.List parameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nonEmptyParameterList : SpecTec.nonEmptyParameterList := input0; (let «parameter*» : (_root_.List parameter) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameter*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parameter*» with | «exec:2» :: «exec:1» => (let parameter_h : parameter := «exec:2»; (let «parameter_t*» : (_root_.List parameter) := «exec:1»; (.bind (.call ⟨SpecTec.nonEmptyParameterList, SpecTecCall.«$unflatten_nonEmptyParameterList'» ((SpecTec.nonEmptyParameterList.«% ',' %» nonEmptyParameterList parameter_h) : SpecTec.nonEmptyParameterList) «parameter_t*»⟩) (fun («exec:3» : SpecTec.nonEmptyParameterList) => (let «eval:0» : SpecTec.nonEmptyParameterList := «exec:3»; (.pure ((«eval:0» : SpecTec.nonEmptyParameterList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_nonEmptyParameterList'_clauses» (input0 : nonEmptyParameterList) (input1 : (_root_.List parameter)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_nonEmptyParameterList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_nonEmptyParameterList':clause:1»  input0 input1)]


noncomputable def «$lift_constantInitializerIR_as_initializer:clause:0» (input0 : constantInitializerIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«'=' _VALUE %» «exec:1» => (let value : SpecTec.value := «exec:1»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_value» value⟩) (fun («exec:2» : SpecTec.expression) => (let «eval:0» : SpecTec.expression := «exec:2»; (let expression : SpecTec.expression := «eval:0»; (.pure ((((initializer.«'=' %» expression) : initializer) : initializer)))))))))


noncomputable def «$lift_constantInitializerIR_as_initializer_clauses» (input0 : constantInitializerIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_constantInitializerIR_as_initializer:clause:0»  input0)]


noncomputable def «$unflatten_namedExpressionList':clause:0» (input0 : SpecTec.namedExpressionList) (input1 : (_root_.List namedExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let namedExpressionList : SpecTec.namedExpressionList := input0; (let «namedExpression*» : (_root_.List namedExpression) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «namedExpression*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((namedExpressionList : SpecTec.namedExpressionList)))))))


noncomputable def «$unflatten_namedExpressionList':clause:1» (input0 : SpecTec.namedExpressionList) (input1 : (_root_.List namedExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let namedExpressionList : SpecTec.namedExpressionList := input0; (let «namedExpression*» : (_root_.List namedExpression) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «namedExpression*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «namedExpression*» with | «exec:2» :: «exec:1» => (let namedExpression_h : namedExpression := «exec:2»; (let «namedExpression_t*» : (_root_.List namedExpression) := «exec:1»; (.bind (.call ⟨SpecTec.namedExpressionList, SpecTecCall.«$unflatten_namedExpressionList'» ((SpecTec.namedExpressionList.«% ',' %» namedExpressionList namedExpression_h) : SpecTec.namedExpressionList) «namedExpression_t*»⟩) (fun («exec:3» : SpecTec.namedExpressionList) => (let «eval:0» : SpecTec.namedExpressionList := «exec:3»; (.pure ((«eval:0» : SpecTec.namedExpressionList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_namedExpressionList'_clauses» (input0 : namedExpressionList) (input1 : (_root_.List namedExpression)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_namedExpressionList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_namedExpressionList':clause:1»  input0 input1)]


noncomputable def «$lift_literalExpressionIR:clause:0» (input0 : literalExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let literalExpression : SpecTec.literalExpression := input0; (.pure ((literalExpression : SpecTec.literalExpression))))


noncomputable def «$lift_literalExpressionIR_clauses» (input0 : literalExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_literalExpressionIR:clause:0»  input0)]


noncomputable def «$lift_defaultExpressionIR:clause:0» (input0 : defaultExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let defaultExpression : SpecTec.defaultExpression := input0; (.bind (.guard (((SpecTec.defaultExpression.«'...'») : SpecTec.defaultExpression) = defaultExpression)) (fun (_ : Unit) => (.pure ((((SpecTec.defaultExpression.«'...'») : SpecTec.defaultExpression) : SpecTec.defaultExpression))))))


noncomputable def «$lift_defaultExpressionIR_clauses» (input0 : defaultExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_defaultExpressionIR:clause:0»  input0)]


noncomputable def «$unflatten_expressionList':clause:0» (input0 : SpecTec.expressionList) (input1 : (_root_.List expression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionList : SpecTec.expressionList := input0; (let «expression*» : (_root_.List expression) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «expression*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((expressionList : SpecTec.expressionList)))))))


noncomputable def «$unflatten_expressionList':clause:1» (input0 : SpecTec.expressionList) (input1 : (_root_.List expression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionList : SpecTec.expressionList := input0; (let «expression*» : (_root_.List expression) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «expression*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «expression*» with | «exec:2» :: «exec:1» => (let expression_h : expression := «exec:2»; (let «expression_t*» : (_root_.List expression) := «exec:1»; (.bind (.call ⟨SpecTec.expressionList, SpecTecCall.«$unflatten_expressionList'» ((SpecTec.expressionList.«% ',' %» expressionList expression_h) : SpecTec.expressionList) «expression_t*»⟩) (fun («exec:3» : SpecTec.expressionList) => (let «eval:0» : SpecTec.expressionList := «exec:3»; (.pure ((«eval:0» : SpecTec.expressionList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_expressionList'_clauses» (input0 : expressionList) (input1 : (_root_.List expression)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_expressionList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_expressionList':clause:1»  input0 input1)]


noncomputable def «$unflatten_simpleKeysetExpressionList':clause:0» (input0 : SpecTec.simpleKeysetExpressionList) (input1 : (_root_.List simpleKeysetExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let simpleKeysetExpressionList : SpecTec.simpleKeysetExpressionList := input0; (let «simpleKeysetExpression*» : (_root_.List simpleKeysetExpression) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «simpleKeysetExpression*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((simpleKeysetExpressionList : SpecTec.simpleKeysetExpressionList)))))))


noncomputable def «$unflatten_simpleKeysetExpressionList':clause:1» (input0 : SpecTec.simpleKeysetExpressionList) (input1 : (_root_.List simpleKeysetExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let simpleKeysetExpressionList : SpecTec.simpleKeysetExpressionList := input0; (let «simpleKeysetExpression*» : (_root_.List simpleKeysetExpression) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «simpleKeysetExpression*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «simpleKeysetExpression*» with | «exec:2» :: «exec:1» => (let simpleKeysetExpression_h : simpleKeysetExpression := «exec:2»; (let «simpleKeysetExpression_t*» : (_root_.List simpleKeysetExpression) := «exec:1»; (.bind (.call ⟨SpecTec.simpleKeysetExpressionList, SpecTecCall.«$unflatten_simpleKeysetExpressionList'» ((SpecTec.simpleKeysetExpressionList.«% ',' %» simpleKeysetExpressionList simpleKeysetExpression_h) : SpecTec.simpleKeysetExpressionList) «simpleKeysetExpression_t*»⟩) (fun («exec:3» : SpecTec.simpleKeysetExpressionList) => (let «eval:0» : SpecTec.simpleKeysetExpressionList := «exec:3»; (.pure ((«eval:0» : SpecTec.simpleKeysetExpressionList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_simpleKeysetExpressionList'_clauses» (input0 : simpleKeysetExpressionList) (input1 : (_root_.List simpleKeysetExpression)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_simpleKeysetExpressionList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_simpleKeysetExpressionList':clause:1»  input0 input1)]


noncomputable def «$unflatten_realTypeArgumentList':clause:0» (input0 : SpecTec.realTypeArgumentList) (input1 : (_root_.List realTypeArgument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let realTypeArgumentList : SpecTec.realTypeArgumentList := input0; (let «realTypeArgument*» : (_root_.List realTypeArgument) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «realTypeArgument*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((realTypeArgumentList : SpecTec.realTypeArgumentList)))))))


noncomputable def «$unflatten_realTypeArgumentList':clause:1» (input0 : SpecTec.realTypeArgumentList) (input1 : (_root_.List realTypeArgument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let realTypeArgumentList : SpecTec.realTypeArgumentList := input0; (let «realTypeArgument*» : (_root_.List realTypeArgument) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «realTypeArgument*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «realTypeArgument*» with | «exec:2» :: «exec:1» => (let realTypeArgument_h : realTypeArgument := «exec:2»; (let «realTypeArgument_t*» : (_root_.List realTypeArgument) := «exec:1»; (.bind (.call ⟨SpecTec.realTypeArgumentList, SpecTecCall.«$unflatten_realTypeArgumentList'» ((SpecTec.realTypeArgumentList.«% ',' %» realTypeArgumentList realTypeArgument_h) : SpecTec.realTypeArgumentList) «realTypeArgument_t*»⟩) (fun («exec:3» : SpecTec.realTypeArgumentList) => (let «eval:0» : SpecTec.realTypeArgumentList := «exec:3»; (.pure ((«eval:0» : SpecTec.realTypeArgumentList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_realTypeArgumentList'_clauses» (input0 : realTypeArgumentList) (input1 : (_root_.List realTypeArgument)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_realTypeArgumentList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_realTypeArgumentList':clause:1»  input0 input1)]


noncomputable def «$unflatten_typeArgumentList':clause:0» (input0 : SpecTec.typeArgumentList) (input1 : (_root_.List typeArgument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeArgumentList : SpecTec.typeArgumentList := input0; (let «typeArgument*» : (_root_.List typeArgument) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeArgument*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((typeArgumentList : SpecTec.typeArgumentList)))))))


noncomputable def «$unflatten_typeArgumentList':clause:1» (input0 : SpecTec.typeArgumentList) (input1 : (_root_.List typeArgument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeArgumentList : SpecTec.typeArgumentList := input0; (let «typeArgument*» : (_root_.List typeArgument) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeArgument*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeArgument*» with | «exec:2» :: «exec:1» => (let typeArgument_h : typeArgument := «exec:2»; (let «typeArgument_t*» : (_root_.List typeArgument) := «exec:1»; (.bind (.call ⟨SpecTec.typeArgumentList, SpecTecCall.«$unflatten_typeArgumentList'» ((SpecTec.typeArgumentList.«% ',' %» typeArgumentList typeArgument_h) : SpecTec.typeArgumentList) «typeArgument_t*»⟩) (fun («exec:3» : SpecTec.typeArgumentList) => (let «eval:0» : SpecTec.typeArgumentList := «exec:3»; (.pure ((«eval:0» : SpecTec.typeArgumentList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_typeArgumentList'_clauses» (input0 : typeArgumentList) (input1 : (_root_.List typeArgument)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_typeArgumentList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_typeArgumentList':clause:1»  input0 input1)]


noncomputable def «$unflatten_argumentListNonEmpty':clause:0» (input0 : SpecTec.argumentListNonEmpty) (input1 : (_root_.List argument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentListNonEmpty : SpecTec.argumentListNonEmpty := input0; (let «argument*» : (_root_.List argument) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «argument*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((argumentListNonEmpty : SpecTec.argumentListNonEmpty)))))))


noncomputable def «$unflatten_argumentListNonEmpty':clause:1» (input0 : SpecTec.argumentListNonEmpty) (input1 : (_root_.List argument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentListNonEmpty : SpecTec.argumentListNonEmpty := input0; (let «argument*» : (_root_.List argument) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «argument*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «argument*» with | «exec:2» :: «exec:1» => (let argument_h : argument := «exec:2»; (let «argument_t*» : (_root_.List argument) := «exec:1»; (.bind (.call ⟨SpecTec.argumentListNonEmpty, SpecTecCall.«$unflatten_argumentListNonEmpty'» ((SpecTec.argumentListNonEmpty.«% ',' %» argumentListNonEmpty argument_h) : SpecTec.argumentListNonEmpty) «argument_t*»⟩) (fun («exec:3» : SpecTec.argumentListNonEmpty) => (let «eval:0» : SpecTec.argumentListNonEmpty := «exec:3»; (.pure ((«eval:0» : SpecTec.argumentListNonEmpty)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_argumentListNonEmpty'_clauses» (input0 : argumentListNonEmpty) (input1 : (_root_.List argument)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_argumentListNonEmpty':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_argumentListNonEmpty':clause:1»  input0 input1)]


noncomputable def «$lift_emptyStatementIR:clause:0» (input0 : emptyStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let emptyStatement : SpecTec.emptyStatement := input0; (.bind (.guard (((SpecTec.emptyStatement.«';'») : SpecTec.emptyStatement) = emptyStatement)) (fun (_ : Unit) => (.pure ((((SpecTec.emptyStatement.«';'») : SpecTec.emptyStatement) : SpecTec.emptyStatement))))))

end SpecTec
