import SpecTecDecl0200

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Lvalue_ok:headerTypeIR:iter:5:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × typeIR))) : (_root_.List (_root_.String × typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Lvalue_ok:headerTypeIR:iter:5:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Lvalue_ok:headerTypeIR:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × typeIR))) => (let «tail:2» : (_root_.List (_root_.String × typeIR)) := «exec:5»; (.pure ((((nameIR_field, typeIR_field) :: «tail:2») : (_root_.List (_root_.String × typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Lvalue_ok:headerTypeIR:iter:5_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Lvalue_ok:headerTypeIR:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Lvalue_ok:headerTypeIR:iter:5:clause:1»  input0 input1)]


noncomputable def «Lvalue_ok:headerUnionTypeIR:pattern-iter:2:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Lvalue_ok:headerUnionTypeIR:pattern-iter:2:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Lvalue_ok:headerUnionTypeIR:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Lvalue_ok:headerUnionTypeIR:pattern-iter:2_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Lvalue_ok:headerUnionTypeIR:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Lvalue_ok:headerUnionTypeIR:pattern-iter:2:clause:1»  input0)]


noncomputable def «Lvalue_ok:headerUnionTypeIR:iter:5:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × typeIR))) : (_root_.List (_root_.String × typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Lvalue_ok:headerUnionTypeIR:iter:5:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Lvalue_ok:headerUnionTypeIR:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × typeIR))) => (let «tail:2» : (_root_.List (_root_.String × typeIR)) := «exec:5»; (.pure ((((nameIR_field, typeIR_field) :: «tail:2») : (_root_.List (_root_.String × typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Lvalue_ok:headerUnionTypeIR:iter:5_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Lvalue_ok:headerUnionTypeIR:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Lvalue_ok:headerUnionTypeIR:iter:5:clause:1»  input0 input1)]


noncomputable def «Stmt_ok:callStatement-no-typeArgumentList-static_assert:iter:1:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «Stmt_ok:callStatement-no-typeArgumentList-static_assert:iter:1:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_impl : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«Stmt_ok:callStatement-no-typeArgumentList-static_assert:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeId_impl) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «Stmt_ok:callStatement-no-typeArgumentList-static_assert:iter:1_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Stmt_ok:callStatement-no-typeArgumentList-static_assert:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Stmt_ok:callStatement-no-typeArgumentList-static_assert:iter:1:clause:1»  input0)]


noncomputable def «Stmt_ok:callStatement-no-typeArgumentList:iter:1:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «Stmt_ok:callStatement-no-typeArgumentList:iter:1:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_impl : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«Stmt_ok:callStatement-no-typeArgumentList:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeId_impl) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «Stmt_ok:callStatement-no-typeArgumentList:iter:1_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Stmt_ok:callStatement-no-typeArgumentList:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Stmt_ok:callStatement-no-typeArgumentList:iter:1:clause:1»  input0)]


noncomputable def «Stmt_ok:callStatement-typeArgumentList:iter:1:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «Stmt_ok:callStatement-typeArgumentList:iter:1:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_inserted : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«Stmt_ok:callStatement-typeArgumentList:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeId_inserted) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «Stmt_ok:callStatement-typeArgumentList:iter:1_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Stmt_ok:callStatement-typeArgumentList:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Stmt_ok:callStatement-typeArgumentList:iter:1:clause:1»  input0)]


noncomputable def «ParserSelect_ok:rule:iter:4:clause:0» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «ParserSelect_ok:rule:iter:4:clause:1» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typedExpressionIR_key_reduced : typedExpressionIR := «exec:2»; (let «tail:0» : (_root_.List typedExpressionIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$type_of_typedExpressionIR» typedExpressionIR_key_reduced⟩) (fun («exec:3» : typeIR) => (let «eval:5» : typeIR := «exec:3»; (let typeIR_key_reduced : typeIR := «eval:5»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«ParserSelect_ok:rule:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_key_reduced :: «tail:1») : (_root_.List typeIR))))))))))))) | [] => .unmatch)


noncomputable def «ParserSelect_ok:rule:iter:4_clauses» (input0 : (_root_.List typedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ParserSelect_ok:rule:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («ParserSelect_ok:rule:iter:4:clause:1»  input0)]


noncomputable def «ParserStateList_ok:rule:iter:1:clause:0» (input0 : (_root_.List parserState)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List parserBlockElementStatementList)), (([] : (_root_.List transitionStatement)), ([] : (_root_.List name))))) : ((_root_.List annotationList) × ((_root_.List parserBlockElementStatementList) × ((_root_.List transitionStatement) × (_root_.List name))))))) | _ :: _ => .unmatch)


noncomputable def «ParserStateList_ok:rule:iter:1:clause:1» (input0 : (_root_.List SpecTec.parserState)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parserState : SpecTec.parserState := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parserState) := «exec:1»; (match parserState with | .«% STATE % `{ % % `}» «exec:3» «exec:4» «exec:5» «exec:6» => (let _annotationList : annotationList := «exec:3»; (let name_state : name := «exec:4»; (let _parserBlockElementStatementList : parserBlockElementStatementList := «exec:5»; (let _transitionStatement : transitionStatement := «exec:6»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List parserBlockElementStatementList) × ((_root_.List transitionStatement) × (_root_.List name)))), SpecTecCall.«ParserStateList_ok:rule:iter:1» «tail:0»⟩) (fun («exec:7» : ((_root_.List annotationList) × ((_root_.List parserBlockElementStatementList) × ((_root_.List transitionStatement) × (_root_.List name))))) => (let «tail:1» : (_root_.List annotationList) := («exec:7»).1; (let «tail:2» : (_root_.List parserBlockElementStatementList) := ((«exec:7»).2).1; (let «tail:3» : (_root_.List transitionStatement) := (((«exec:7»).2).2).1; (let «tail:4» : (_root_.List name) := (((«exec:7»).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_parserBlockElementStatementList :: «tail:2»), ((_transitionStatement :: «tail:3»), (name_state :: «tail:4»)))) : ((_root_.List annotationList) × ((_root_.List parserBlockElementStatementList) × ((_root_.List transitionStatement) × (_root_.List name)))))))))))))))))))) | [] => .unmatch)


noncomputable def «ParserStateList_ok:rule:iter:1_clauses» (input0 : (_root_.List parserState)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ParserStateList_ok:rule:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («ParserStateList_ok:rule:iter:1:clause:1»  input0)]


noncomputable def «ParserStateList_ok:rule:iter:2:clause:0» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List nameIR)) : (_root_.List nameIR)))) | _ :: _ => .unmatch)


noncomputable def «ParserStateList_ok:rule:iter:2:clause:1» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let name_state : name := «exec:2»; (let «tail:0» : (_root_.List name) := «exec:1»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» name_state⟩) (fun («exec:3» : nameIR) => (let «eval:3» : nameIR := «exec:3»; (let nameIR_state : nameIR := «eval:3»; (.bind (.call ⟨(_root_.List nameIR), SpecTecCall.«ParserStateList_ok:rule:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List nameIR)) => (let «tail:1» : (_root_.List nameIR) := «exec:4»; (.pure (((nameIR_state :: «tail:1») : (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «ParserStateList_ok:rule:iter:2_clauses» (input0 : (_root_.List name)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ParserStateList_ok:rule:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («ParserStateList_ok:rule:iter:2:clause:1»  input0)]


noncomputable def «TableDefaultAction_ok:prefixedNonTypeName-argumentList:iter:4:clause:0» (input0 : (_root_.List argumentIR)) (input1 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «TableDefaultAction_ok:prefixedNonTypeName-argumentList:iter:4:clause:1» (input0 : (_root_.List argumentIR)) (input1 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let argumentIR_action_data : argumentIR := «exec:2»; (let «tail:0» : (_root_.List argumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let argumentIR_cast_data : argumentIR := «exec:4»; (let «tail:1» : (_root_.List argumentIR) := «exec:3»; (.bind (.guard (argumentIR_cast_data = argumentIR_action_data)) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«TableDefaultAction_ok:prefixedNonTypeName-argumentList:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «TableDefaultAction_ok:prefixedNonTypeName-argumentList:iter:4_clauses» (input0 : (_root_.List argumentIR)) (input1 : (_root_.List argumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («TableDefaultAction_ok:prefixedNonTypeName-argumentList:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («TableDefaultAction_ok:prefixedNonTypeName-argumentList:iter:4:clause:1»  input0 input1)]


noncomputable def «TableEntry_action_ok:prefixedNonTypeName-argumentList:iter:2:clause:0» (input0 : (_root_.List argumentIR)) (input1 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «TableEntry_action_ok:prefixedNonTypeName-argumentList:iter:2:clause:1» (input0 : (_root_.List argumentIR)) (input1 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let argumentIR_action_data : argumentIR := «exec:2»; (let «tail:0» : (_root_.List argumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let argumentIR_cast_data : argumentIR := «exec:4»; (let «tail:1» : (_root_.List argumentIR) := «exec:3»; (.bind (.guard (argumentIR_cast_data = argumentIR_action_data)) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«TableEntry_action_ok:prefixedNonTypeName-argumentList:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)

end SpecTec
