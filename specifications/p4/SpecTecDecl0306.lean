import SpecTecDecl0305

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_accessExpressionIR:clause:0» (input0 : SpecTec.accessExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let accessExpressionIR : SpecTec.accessExpressionIR := input0; (.bind (.guard (((«sub:accessExpressionIR:errorAccessExpressionIR» accessExpressionIR) = true))) (fun (_ : Unit) => (match («$lift_accessExpressionIR:case_1:downcast:0» accessExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.errorAccessExpressionIR := «exec:1»; (let errorAccessExpressionIR : SpecTec.errorAccessExpressionIR := «eval:0»; (.bind (.call ⟨errorAccessExpression, SpecTecCall.«$lift_errorAccessExpressionIR» errorAccessExpressionIR⟩) (fun («exec:2» : errorAccessExpression) => (let «eval:1» : errorAccessExpression := «exec:2»; (.pure (((«cast:errorAccessExpression:accessExpression» «eval:1») : accessExpression)))))))) | none => .unmatch))))


noncomputable def «$lift_accessExpressionIR:clause:1» (input0 : SpecTec.accessExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let accessExpressionIR : SpecTec.accessExpressionIR := input0; (.bind (.guard (((«sub:accessExpressionIR:memberAccessExpressionIR» accessExpressionIR) = true))) (fun (_ : Unit) => (match («$lift_accessExpressionIR:case_2:downcast:0» accessExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.memberAccessExpressionIR := «exec:1»; (let memberAccessExpressionIR : SpecTec.memberAccessExpressionIR := «eval:0»; (.bind (.call ⟨memberAccessExpression, SpecTecCall.«$lift_memberAccessExpressionIR» memberAccessExpressionIR⟩) (fun («exec:2» : memberAccessExpression) => (let «eval:1» : memberAccessExpression := «exec:2»; (.pure (((«cast:memberAccessExpression:accessExpression» «eval:1») : accessExpression)))))))) | none => .unmatch))))


noncomputable def «$lift_accessExpressionIR:clause:2» (input0 : SpecTec.accessExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let accessExpressionIR : SpecTec.accessExpressionIR := input0; (.bind (.guard (((«sub:accessExpressionIR:indexAccessExpressionIR» accessExpressionIR) = true))) (fun (_ : Unit) => (match («$lift_accessExpressionIR:case_3:downcast:0» accessExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.indexAccessExpressionIR := «exec:1»; (let indexAccessExpressionIR : SpecTec.indexAccessExpressionIR := «eval:0»; (.bind (.call ⟨indexAccessExpression, SpecTecCall.«$lift_indexAccessExpressionIR» indexAccessExpressionIR⟩) (fun («exec:2» : indexAccessExpression) => (let «eval:1» : indexAccessExpression := «exec:2»; (.pure (((«cast:indexAccessExpression:accessExpression» «eval:1») : accessExpression)))))))) | none => .unmatch))))


noncomputable def «$lift_accessExpressionIR:clause:3» (input0 : SpecTec.accessExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let accessExpressionIR : SpecTec.accessExpressionIR := input0; (.bind (.guard (((«sub:accessExpressionIR:sliceAccessExpressionIR» accessExpressionIR) = true))) (fun (_ : Unit) => (match («$lift_accessExpressionIR:case_4:downcast:0» accessExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.sliceAccessExpressionIR := «exec:1»; (let sliceAccessExpressionIR : SpecTec.sliceAccessExpressionIR := «eval:0»; (.bind (.call ⟨sliceAccessExpression, SpecTecCall.«$lift_sliceAccessExpressionIR» sliceAccessExpressionIR⟩) (fun («exec:2» : sliceAccessExpression) => (let «eval:1» : sliceAccessExpression := «exec:2»; (.pure (((«cast:sliceAccessExpression:accessExpression» «eval:1») : accessExpression)))))))) | none => .unmatch))))


noncomputable def «$lift_accessExpressionIR_clauses» (input0 : accessExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_accessExpressionIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_accessExpressionIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_accessExpressionIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_accessExpressionIR:clause:3»  input0)]


noncomputable def «$lift_argumentListIR:clause:0» (input0 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «argumentIR*» : (_root_.List argumentIR) := input0; (.bind (.call ⟨(_root_.List argument), SpecTecCall.«$lift_argumentListIR:case_1:iter:0» «argumentIR*»⟩) (fun («exec:1» : (_root_.List argument)) => (let «argument*» : (_root_.List argument) := «exec:1»; (.bind (.call ⟨SpecTec.argumentList, SpecTecCall.«$unflatten_argumentList» «argument*»⟩) (fun («exec:2» : SpecTec.argumentList) => (let «eval:2» : SpecTec.argumentList := «exec:2»; (let argumentList : SpecTec.argumentList := «eval:2»; (.pure ((argumentList : SpecTec.argumentList)))))))))))


noncomputable def «$lift_argumentListIR_clauses» (input0 : (_root_.List argumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_argumentListIR:clause:0»  input0)]


noncomputable def «$lift_argumentListIR:case_1:iter:0:clause:0» (input0 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List argument)) : (_root_.List argument)))) | _ :: _ => .unmatch)


noncomputable def «$lift_argumentListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let argumentIR : SpecTec.argumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.argumentIR) := «exec:1»; (.bind (.call ⟨SpecTec.argument, SpecTecCall.«$lift_argumentIR» argumentIR⟩) (fun («exec:3» : SpecTec.argument) => (let «eval:1» : SpecTec.argument := «exec:3»; (let argument : SpecTec.argument := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.argument), SpecTecCall.«$lift_argumentListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.argument)) => (let «tail:1» : (_root_.List SpecTec.argument) := «exec:4»; (.pure (((argument :: «tail:1») : (_root_.List SpecTec.argument))))))))))))) | [] => .unmatch)


noncomputable def «$lift_argumentListIR:case_1:iter:0_clauses» (input0 : (_root_.List argumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_argumentListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_argumentListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_callableTargetIR_as_expression:clause:0» (input0 : SpecTec.callableTargetIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTargetIR : SpecTec.callableTargetIR := input0; (.bind (.guard (((SpecTec.callableTargetIR._BARE "this") : SpecTec.callableTargetIR) = callableTargetIR)) (fun (_ : Unit) => (.pure ((((expression.THIS) : expression) : expression))))))


noncomputable def «$lift_callableTargetIR_as_expression:clause:1» (input0 : SpecTec.callableTargetIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTargetIR : SpecTec.callableTargetIR := input0; (.bind (.guard (((«sub:callableTargetIR:prefixedNameIR» callableTargetIR) = true))) (fun (_ : Unit) => (match («$lift_callableTargetIR_as_expression:case_2:downcast:0» callableTargetIR) with | some «exec:1» => (let «eval:0» : SpecTec.prefixedNameIR := «exec:1»; (let prefixedNameIR : SpecTec.prefixedNameIR := «eval:0»; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:2» => (let nameIR : SpecTec.nameIR := «exec:2»; (.bind (.guard ((nameIR ≠ "this"))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:3» : SpecTec.nonTypeName) => (let «eval:1» : SpecTec.nonTypeName := «exec:3»; (let nonTypeName : SpecTec.nonTypeName := «eval:1»; (.pure (((«cast:nonTypeName:expression» nonTypeName) : expression)))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$lift_callableTargetIR_as_expression:clause:2» (input0 : SpecTec.callableTargetIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTargetIR : SpecTec.callableTargetIR := input0; (.bind (.guard (((«sub:callableTargetIR:prefixedNameIR» callableTargetIR) = true))) (fun (_ : Unit) => (match («$lift_callableTargetIR_as_expression:case_3:downcast:0» callableTargetIR) with | some «exec:1» => (let «eval:0» : SpecTec.prefixedNameIR := «exec:1»; (let prefixedNameIR : SpecTec.prefixedNameIR := «eval:0»; (.bind (.guard (((«exec:match:prefixedNameIR:'.' %» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | .«'.' %» «exec:2» => (let nameIR : SpecTec.nameIR := «exec:2»; (.bind (.call ⟨SpecTec.nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:3» : SpecTec.nonTypeName) => (let «eval:1» : SpecTec.nonTypeName := «exec:3»; (let nonTypeName : SpecTec.nonTypeName := «eval:1»; (.pure ((((expression.«_ID '.' %» nonTypeName) : expression) : expression)))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$lift_callableTargetIR_as_expression:clause:3» (input0 : SpecTec.callableTargetIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTargetIR : SpecTec.callableTargetIR := input0; (.bind (.guard (((«exec:match:callableTargetIR:% '.' %» callableTargetIR) = true))) (fun (_ : Unit) => (match callableTargetIR with | .«% '.' %» «exec:1» «exec:2» => (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:3» : SpecTec.expression) => (let «eval:0» : SpecTec.expression := «exec:3»; (let expression : SpecTec.expression := «eval:0»; (.bind (.call ⟨SpecTec.member, SpecTecCall.«$lift_nameIR_as_member» nameIR⟩) (fun («exec:4» : SpecTec.member) => (let «eval:1» : SpecTec.member := «exec:4»; (let member : SpecTec.member := «eval:1»; (.pure ((((SpecTec.expression.«% '.' %» («cast:expression:memberAccessBase» expression) member) : SpecTec.expression) : SpecTec.expression))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_callableTargetIR_as_expression:clause:4» (input0 : SpecTec.callableTargetIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTargetIR : SpecTec.callableTargetIR := input0; (.bind (.guard (((«exec:match:callableTargetIR:TYPE % '.' %» callableTargetIR) = true))) (fun (_ : Unit) => (match callableTargetIR with | .«TYPE % '.' %» «exec:1» «exec:2» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (.bind (.guard (((SpecTec.prefixedNameIR._BARE "this") : SpecTec.prefixedNameIR) = prefixedNameIR)) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.member, SpecTecCall.«$lift_nameIR_as_member» nameIR⟩) (fun («exec:3» : SpecTec.member) => (let «eval:0» : SpecTec.member := «exec:3»; (let member : SpecTec.member := «eval:0»; (.pure ((((expression.«% '.' %» ((memberAccessBase.THIS) : memberAccessBase) member) : expression) : expression))))))))))) | _ => .unmatch))))


noncomputable def «$lift_callableTargetIR_as_expression:clause:5» (input0 : SpecTec.callableTargetIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTargetIR : SpecTec.callableTargetIR := input0; (.bind (.guard (((«exec:match:callableTargetIR:TYPE % '.' %» callableTargetIR) = true))) (fun (_ : Unit) => (match callableTargetIR with | .«TYPE % '.' %» «exec:1» «exec:2» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:1»; (let nameIR_field : SpecTec.nameIR := «exec:2»; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:3» => (let nameIR : SpecTec.nameIR := «exec:3»; (.bind (.guard ((nameIR ≠ "this"))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:4» : SpecTec.nonTypeName) => (let «eval:0» : SpecTec.nonTypeName := «exec:4»; (let nonTypeName : SpecTec.nonTypeName := «eval:0»; (.bind (.call ⟨SpecTec.member, SpecTecCall.«$lift_nameIR_as_member» nameIR_field⟩) (fun («exec:5» : SpecTec.member) => (let «eval:1» : SpecTec.member := «exec:5»; (let member : SpecTec.member := «eval:1»; (.pure ((((expression.«% '.' %» («cast:nonTypeName:memberAccessBase» nonTypeName) member) : expression) : expression)))))))))))))) | _ => .unmatch))))) | _ => .unmatch))))


noncomputable def «$lift_callableTargetIR_as_expression:clause:6» (input0 : SpecTec.callableTargetIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTargetIR : SpecTec.callableTargetIR := input0; (.bind (.guard (((«exec:match:callableTargetIR:TYPE % '.' %» callableTargetIR) = true))) (fun (_ : Unit) => (match callableTargetIR with | .«TYPE % '.' %» «exec:1» «exec:2» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:1»; (let nameIR_field : SpecTec.nameIR := «exec:2»; (.bind (.guard (((«exec:match:prefixedNameIR:'.' %» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | .«'.' %» «exec:3» => (let nameIR : SpecTec.nameIR := «exec:3»; (.bind (.call ⟨SpecTec.nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:4» : SpecTec.nonTypeName) => (let «eval:0» : SpecTec.nonTypeName := «exec:4»; (let nonTypeName : SpecTec.nonTypeName := «eval:0»; (.bind (.call ⟨SpecTec.member, SpecTecCall.«$lift_nameIR_as_member» nameIR_field⟩) (fun («exec:5» : SpecTec.member) => (let «eval:1» : SpecTec.member := «exec:5»; (let member : SpecTec.member := «eval:1»; (.pure ((((expression.«% '.' %» ((memberAccessBase.«_ID '.' %» nonTypeName) : memberAccessBase) member) : expression) : expression)))))))))))) | _ => .unmatch))))) | _ => .unmatch))))


noncomputable def «$lift_callableTargetIR_as_expression:clause:7» (input0 : SpecTec.callableTargetIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTargetIR' : SpecTec.callableTargetIR := input0; (.bind (.guard (((«exec:match:callableTargetIR:`( % `)» callableTargetIR') = true))) (fun (_ : Unit) => (match callableTargetIR' with | .«`( % `)» «exec:1» => (let callableTargetIR : SpecTec.callableTargetIR := «exec:1»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_callableTargetIR_as_expression» callableTargetIR⟩) (fun («exec:2» : SpecTec.expression) => (let «eval:0» : SpecTec.expression := «exec:2»; (let expression : SpecTec.expression := «eval:0»; (.pure ((((SpecTec.expression.«`( % `)» expression) : SpecTec.expression) : SpecTec.expression)))))))) | _ => .unmatch))))


noncomputable def «$lift_callableTargetIR_as_expression_clauses» (input0 : callableTargetIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_callableTargetIR_as_expression:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_callableTargetIR_as_expression:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_callableTargetIR_as_expression:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_callableTargetIR_as_expression:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_callableTargetIR_as_expression:clause:4»  input0), fun (_ : _root_.Unit) => («$lift_callableTargetIR_as_expression:clause:5»  input0), fun (_ : _root_.Unit) => («$lift_callableTargetIR_as_expression:clause:6»  input0), fun (_ : _root_.Unit) => («$lift_callableTargetIR_as_expression:clause:7»  input0)]


noncomputable def «$lift_callExpressionIR:clause:0» (input0 : SpecTec.callExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callExpressionIR : SpecTec.callExpressionIR := input0; (.bind (.guard (((«exec:match:callExpressionIR:% `( % `)» callExpressionIR) = true))) (fun (_ : Unit) => (match callExpressionIR with | .«% `( % `)» «exec:1» «exec:2» => (let constructorTargetIR : SpecTec.constructorTargetIR := «exec:1»; (let «argumentIR*» : (_root_.List argumentIR) := «exec:2»; (match constructorTargetIR with | .«% `< % `>» «exec:3» «exec:4» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:3»; (let «typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:4»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeArgumentIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.prefixedTypeName, SpecTecCall.«$lift_prefixedNameIR_as_prefixedTypeName» prefixedNameIR⟩) (fun («exec:5» : SpecTec.prefixedTypeName) => (let «eval:0» : SpecTec.prefixedTypeName := «exec:5»; (let prefixedTypeName : SpecTec.prefixedTypeName := «eval:0»; (let namedType : SpecTec.namedType := («cast:prefixedTypeName:namedType» prefixedTypeName); (.bind (.call ⟨SpecTec.argumentList, SpecTecCall.«$lift_argumentListIR» «argumentIR*»⟩) (fun («exec:6» : SpecTec.argumentList) => (let «eval:1» : SpecTec.argumentList := «exec:6»; (let argumentList : SpecTec.argumentList := «eval:1»; (.pure ((((callExpression.«% `( % `)» («cast:namedType:callTarget» namedType) argumentList) : callExpression) : callExpression))))))))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_callExpressionIR:clause:1» (input0 : SpecTec.callExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callExpressionIR : SpecTec.callExpressionIR := input0; (.bind (.guard (((«exec:match:callExpressionIR:% `( % `)» callExpressionIR) = true))) (fun (_ : Unit) => (match callExpressionIR with | .«% `( % `)» «exec:1» «exec:2» => (let constructorTargetIR : SpecTec.constructorTargetIR := «exec:1»; (let «argumentIR*» : (_root_.List argumentIR) := «exec:2»; (match constructorTargetIR with | .«% `< % `>» «exec:3» «exec:4» => (let prefixedNameIR : SpecTec.prefixedNameIR := «exec:3»; (let «typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:4»; (.bind (.guard ((«typeArgumentIR*» ≠ ([] : (_root_.List typeArgumentIR))))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.prefixedTypeName, SpecTecCall.«$lift_prefixedNameIR_as_prefixedTypeName» prefixedNameIR⟩) (fun («exec:5» : SpecTec.prefixedTypeName) => (let «eval:0» : SpecTec.prefixedTypeName := «exec:5»; (let prefixedTypeName : SpecTec.prefixedTypeName := «eval:0»; (.bind (.call ⟨SpecTec.typeArgumentList, SpecTecCall.«$lift_typeArgumentListIR» «typeArgumentIR*»⟩) (fun («exec:6» : SpecTec.typeArgumentList) => (let «eval:1» : SpecTec.typeArgumentList := «exec:6»; (let typeArgumentList : SpecTec.typeArgumentList := «eval:1»; (let namedType : SpecTec.namedType := ((SpecTec.namedType.«% `< % `>» prefixedTypeName typeArgumentList) : SpecTec.namedType); (.bind (.call ⟨SpecTec.argumentList, SpecTecCall.«$lift_argumentListIR» «argumentIR*»⟩) (fun («exec:7» : SpecTec.argumentList) => (let «eval:2» : SpecTec.argumentList := «exec:7»; (let argumentList : SpecTec.argumentList := «eval:2»; (.pure ((((callExpression.«% `( % `)» («cast:namedType:callTarget» namedType) argumentList) : callExpression) : callExpression))))))))))))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_callExpressionIR:clause:2» (input0 : SpecTec.callExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callExpressionIR : SpecTec.callExpressionIR := input0; (.bind (.guard (((«exec:match:callExpressionIR:% `< % `> `( % `)» callExpressionIR) = true))) (fun (_ : Unit) => (match callExpressionIR with | .«% `< % `> `( % `)» «exec:1» «exec:2» «exec:3» => (let callableTargetIR : SpecTec.callableTargetIR := «exec:1»; (let «typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:2»; (let «argumentIR*» : (_root_.List argumentIR) := «exec:3»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeArgumentIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_callableTargetIR_as_expression» callableTargetIR⟩) (fun («exec:4» : SpecTec.expression) => (let «eval:0» : SpecTec.expression := «exec:4»; (let expression : SpecTec.expression := «eval:0»; (.bind (.call ⟨SpecTec.argumentList, SpecTecCall.«$lift_argumentListIR» «argumentIR*»⟩) (fun («exec:5» : SpecTec.argumentList) => (let «eval:1» : SpecTec.argumentList := «exec:5»; (let argumentList : SpecTec.argumentList := «eval:1»; (.pure ((((callExpression.«% `( % `)» («cast:expression:callTarget» expression) argumentList) : callExpression) : callExpression)))))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_callExpressionIR:clause:3» (input0 : SpecTec.callExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callExpressionIR : SpecTec.callExpressionIR := input0; (.bind (.guard (((«exec:match:callExpressionIR:% `< % `> `( % `)» callExpressionIR) = true))) (fun (_ : Unit) => (match callExpressionIR with | .«% `< % `> `( % `)» «exec:1» «exec:2» «exec:3» => (let callableTargetIR : SpecTec.callableTargetIR := «exec:1»; (let «typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:2»; (let «argumentIR*» : (_root_.List argumentIR) := «exec:3»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_callableTargetIR_as_expression» callableTargetIR⟩) (fun («exec:4» : SpecTec.expression) => (let «eval:0» : SpecTec.expression := «exec:4»; (let expression : SpecTec.expression := «eval:0»; (.bind (.guard ((«typeArgumentIR*» ≠ ([] : (_root_.List typeArgumentIR))))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.realTypeArgumentList, SpecTecCall.«$lift_typeArgumentListIR_as_realTypeArgumentList» «typeArgumentIR*»⟩) (fun («exec:5» : SpecTec.realTypeArgumentList) => (let «eval:1» : SpecTec.realTypeArgumentList := «exec:5»; (let realTypeArgumentList : SpecTec.realTypeArgumentList := «eval:1»; (.bind (.call ⟨SpecTec.argumentList, SpecTecCall.«$lift_argumentListIR» «argumentIR*»⟩) (fun («exec:6» : SpecTec.argumentList) => (let «eval:2» : SpecTec.argumentList := «exec:6»; (let argumentList : SpecTec.argumentList := «eval:2»; (.pure ((((callExpression.«% `< % `> `( % `)» expression realTypeArgumentList argumentList) : callExpression) : callExpression)))))))))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_callExpressionIR_clauses» (input0 : callExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_callExpressionIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_callExpressionIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_callExpressionIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_callExpressionIR:clause:3»  input0)]


noncomputable def «$lift_parenthesizedExpressionIR:clause:0» (input0 : parenthesizedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`( % `)» «exec:1» => (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:1»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:2» : SpecTec.expression) => (let «eval:0» : SpecTec.expression := «exec:2»; (let expression : SpecTec.expression := «eval:0»; (.pure ((((parenthesizedExpression.«`( % `)» expression) : parenthesizedExpression) : parenthesizedExpression)))))))))


noncomputable def «$lift_parenthesizedExpressionIR_clauses» (input0 : parenthesizedExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_parenthesizedExpressionIR:clause:0»  input0)]


noncomputable def «$lift_expressionIR:clause:0» (input0 : SpecTec.expressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionIR : SpecTec.expressionIR := input0; (.bind (.guard (((«sub:expressionIR:literalExpression» expressionIR) = true))) (fun (_ : Unit) => (match («$lift_expressionIR:case_1:downcast:0» expressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.literalExpressionIR := «exec:1»; (let literalExpressionIR : SpecTec.literalExpressionIR := «eval:0»; (.bind (.call ⟨literalExpression, SpecTecCall.«$lift_literalExpressionIR» literalExpressionIR⟩) (fun («exec:2» : literalExpression) => (let «eval:1» : literalExpression := «exec:2»; (.pure (((«cast:literalExpression:expression» «eval:1») : expression)))))))) | none => .unmatch))))


noncomputable def «$lift_expressionIR:clause:1» (input0 : SpecTec.expressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionIR : SpecTec.expressionIR := input0; (.bind (.guard (((«sub:expressionIR:prefixedNameIR» expressionIR) = true))) (fun (_ : Unit) => (match («$lift_expressionIR:case_2:downcast:0» expressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.referenceExpressionIR := «exec:1»; (let referenceExpressionIR : SpecTec.referenceExpressionIR := «eval:0»; (.bind (.call ⟨referenceExpression, SpecTecCall.«$lift_referenceExpressionIR» referenceExpressionIR⟩) (fun («exec:2» : referenceExpression) => (let «eval:1» : referenceExpression := «exec:2»; (.pure (((«cast:referenceExpression:expression» «eval:1») : expression)))))))) | none => .unmatch))))


noncomputable def «$lift_expressionIR:clause:2» (input0 : SpecTec.expressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionIR : SpecTec.expressionIR := input0; (.bind (.guard (((«sub:expressionIR:defaultExpression» expressionIR) = true))) (fun (_ : Unit) => (match («$lift_expressionIR:case_3:downcast:0» expressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.defaultExpressionIR := «exec:1»; (let defaultExpressionIR : SpecTec.defaultExpressionIR := «eval:0»; (.bind (.call ⟨defaultExpression, SpecTecCall.«$lift_defaultExpressionIR» defaultExpressionIR⟩) (fun («exec:2» : defaultExpression) => (let «eval:1» : defaultExpression := «exec:2»; (.pure (((«cast:defaultExpression:expression» «eval:1») : expression)))))))) | none => .unmatch))))


noncomputable def «$lift_expressionIR:clause:3» (input0 : SpecTec.expressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionIR : SpecTec.expressionIR := input0; (.bind (.guard (((«sub:expressionIR:unaryExpressionIR» expressionIR) = true))) (fun (_ : Unit) => (match («$lift_expressionIR:case_4:downcast:0» expressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.unaryExpressionIR := «exec:1»; (let unaryExpressionIR : SpecTec.unaryExpressionIR := «eval:0»; (.bind (.call ⟨unaryExpression, SpecTecCall.«$lift_unaryExpressionIR» unaryExpressionIR⟩) (fun («exec:2» : unaryExpression) => (let «eval:1» : unaryExpression := «exec:2»; (.pure (((«cast:unaryExpression:expression» «eval:1») : expression)))))))) | none => .unmatch))))


noncomputable def «$lift_expressionIR:clause:4» (input0 : SpecTec.expressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionIR : SpecTec.expressionIR := input0; (.bind (.guard (((«sub:expressionIR:binaryExpressionIR» expressionIR) = true))) (fun (_ : Unit) => (match («$lift_expressionIR:case_5:downcast:0» expressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.binaryExpressionIR := «exec:1»; (let binaryExpressionIR : SpecTec.binaryExpressionIR := «eval:0»; (.bind (.call ⟨binaryExpression, SpecTecCall.«$lift_binaryExpressionIR» binaryExpressionIR⟩) (fun («exec:2» : binaryExpression) => (let «eval:1» : binaryExpression := «exec:2»; (.pure (((«cast:binaryExpression:expression» «eval:1») : expression)))))))) | none => .unmatch))))


noncomputable def «$lift_expressionIR:clause:5» (input0 : SpecTec.expressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionIR : SpecTec.expressionIR := input0; (.bind (.guard (((«sub:expressionIR:ternaryExpressionIR» expressionIR) = true))) (fun (_ : Unit) => (match («$lift_expressionIR:case_6:downcast:0» expressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.ternaryExpressionIR := «exec:1»; (let ternaryExpressionIR : SpecTec.ternaryExpressionIR := «eval:0»; (.bind (.call ⟨ternaryExpression, SpecTecCall.«$lift_ternaryExpressionIR» ternaryExpressionIR⟩) (fun («exec:2» : ternaryExpression) => (let «eval:1» : ternaryExpression := «exec:2»; (.pure (((«cast:ternaryExpression:expression» «eval:1») : expression)))))))) | none => .unmatch))))

end SpecTec
