import SpecTecDecl0162

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$find_non_overloaded:clause:0» (V_T : Type) (input0 : (map callableId V_T)) (input1 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «eval:1» : (_root_.List (pair callableId V_T)) := «exec:1»; (let nameIR_f : nameIR := input1; (.bind (.call ⟨((_root_.List V_T) × (_root_.List callableId)), SpecTecCall.«$find_non_overloaded:case_1:pattern-iter:0» V_T «eval:1»⟩) (fun («exec:2» : ((_root_.List V_T) × (_root_.List callableId))) => (let «V*» : (_root_.List V_T) := («exec:2»).1; (let «callableId*» : (_root_.List callableId) := («exec:2»).2; (.bind (.call ⟨(_root_.List (pair callTargetId V_T)), SpecTecCall.«$find_non_overloaded:case_1:iter:2» V_T «V*» «callableId*»⟩) (fun («exec:3» : (_root_.List (pair callTargetId V_T))) => (let «eval:3» : (_root_.List (pair callableId V_T)) := «exec:3»; (.bind (.call ⟨(_root_.List (callableId × V_T)), SpecTecCall.«$find_non_overloadeds» V_T ((set.«`{ % `}» «eval:3») : (set (pair callableId V_T))) nameIR_f⟩) (fun («exec:4» : (_root_.List (callableId × V_T))) => (let «eval:4» : (_root_.List (callableId × V_T)) := «exec:4»; (let «(callableId, V)*» : (_root_.List (callableId × V_T)) := «eval:4»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «(callableId, V)*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «(callableId, V)*» with | «exec:6» :: «exec:5» => (let callableId_found : callableId := («exec:6»).1; (let V_found : V_T := («exec:6»).2; (match «exec:5» with | [] => (.pure (((_root_.Option.some (callableId_found, V_found)) : (_root_.Option (callableId × V_T))))) | _ :: _ => .unmatch))) | [] => .unmatch)))))))))))))))))


noncomputable def «$find_non_overloaded:clause:1» (V_T : Type) (input0 : (map callableId V_T)) (input1 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «eval:1» : (_root_.List (pair callableId V_T)) := «exec:1»; (let nameIR_f : nameIR := input1; (.bind (.call ⟨((_root_.List V_T) × (_root_.List callableId)), SpecTecCall.«$find_non_overloaded:case_2:pattern-iter:0» V_T «eval:1»⟩) (fun («exec:2» : ((_root_.List V_T) × (_root_.List callableId))) => (let «V*» : (_root_.List V_T) := («exec:2»).1; (let «callableId*» : (_root_.List callableId) := («exec:2»).2; (.pure ((((_root_.Option.none) : (_root_.Option (callableId × V_T))) : (_root_.Option (callableId × V_T))))))))))))


noncomputable def «$find_non_overloaded_clauses» (V_T : Type) (input0 : (map callableId V_T)) (input1 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_non_overloaded:clause:0» V_T input0 input1), fun (_ : _root_.Unit) => («$find_non_overloaded:clause:1» V_T input0 input1)]


noncomputable def «$name_annotation:case_1:iter:3:clause:0» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List _root_.String))) : (_root_.List (_root_.List _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$name_annotation:case_1:iter:3:clause:1» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_opt? : (_root_.Option nameIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option nameIR)) := «exec:1»; (.bind (.call ⟨(_root_.List nameIR), SpecTecCall.«$opt_as_seq_» nameIR nameIR_opt?⟩) (fun («exec:3» : (_root_.List nameIR)) => (let «eval:4» : (_root_.List nameIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List _root_.String)), SpecTecCall.«$name_annotation:case_1:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List _root_.String))) => (let «tail:1» : (_root_.List (_root_.List _root_.String)) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List (_root_.List _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$name_annotation:case_1:iter:3_clauses» (input0 : (_root_.List (_root_.Option nameIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$name_annotation:case_1:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$name_annotation:case_1:iter:3:clause:1»  input0)]


noncomputable def «$subexpressions_of_expressionIR:case_7:pattern-iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List typedExpressionIR))) : ((_root_.List nameIR) × (_root_.List typedExpressionIR))))) | _ :: _ => .unmatch)


noncomputable def «$subexpressions_of_expressionIR:case_7:pattern-iter:1:clause:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:4»; (let «pattern-tail:0» : (_root_.List namedExpressionIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR)), SpecTecCall.«$subexpressions_of_expressionIR:case_7:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typedExpressionIR) := («exec:5»).2; (.pure ((((nameIR :: «pattern-tail:1»), (typedExpressionIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))))))))))))) | [] => .unmatch)


noncomputable def «$subexpressions_of_expressionIR:case_7:pattern-iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subexpressions_of_expressionIR:case_7:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$subexpressions_of_expressionIR:case_7:pattern-iter:1:clause:1»  input0)]


noncomputable def «$subexpressions_of_expressionIR:case_8:pattern-iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List typedExpressionIR))) : ((_root_.List nameIR) × (_root_.List typedExpressionIR))))) | _ :: _ => .unmatch)


noncomputable def «$subexpressions_of_expressionIR:case_8:pattern-iter:1:clause:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:4»; (let «pattern-tail:0» : (_root_.List namedExpressionIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR)), SpecTecCall.«$subexpressions_of_expressionIR:case_8:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typedExpressionIR) := («exec:5»).2; (.pure ((((nameIR :: «pattern-tail:1»), (typedExpressionIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))))))))))))) | [] => .unmatch)


noncomputable def «$subexpressions_of_expressionIR:case_8:pattern-iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subexpressions_of_expressionIR:case_8:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$subexpressions_of_expressionIR:case_8:pattern-iter:1:clause:1»  input0)]


noncomputable def «$sink_clauses» (T : Type) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  []


noncomputable def «$lift_nameIR_as_identifier:clause:0» (input0 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (.pure ((((identifier._ID nameIR) : identifier) : identifier))))


noncomputable def «$lift_nameIR_as_identifier_clauses» (input0 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_nameIR_as_identifier:clause:0»  input0)]


noncomputable def «$lift_nameIR_as_typeIdentifier:clause:0» (input0 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (.pure ((((typeIdentifier._TID nameIR) : typeIdentifier) : typeIdentifier))))


noncomputable def «$lift_nameIR_as_typeIdentifier_clauses» (input0 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_nameIR_as_typeIdentifier:clause:0»  input0)]


noncomputable def «$lift_nameIR_as_nonTypeName:clause:0» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("apply" = t)) (fun (_ : Unit) => (.pure ((((nonTypeName.APPLY) : nonTypeName) : nonTypeName))))))


noncomputable def «$lift_nameIR_as_nonTypeName:clause:1» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("key" = t)) (fun (_ : Unit) => (.pure ((((nonTypeName.KEY) : nonTypeName) : nonTypeName))))))


noncomputable def «$lift_nameIR_as_nonTypeName:clause:2» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("actions" = t)) (fun (_ : Unit) => (.pure ((((nonTypeName.ACTIONS) : nonTypeName) : nonTypeName))))))


noncomputable def «$lift_nameIR_as_nonTypeName:clause:3» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("state" = t)) (fun (_ : Unit) => (.pure ((((nonTypeName.STATE) : nonTypeName) : nonTypeName))))))


noncomputable def «$lift_nameIR_as_nonTypeName:clause:4» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("entries" = t)) (fun (_ : Unit) => (.pure ((((nonTypeName.ENTRIES) : nonTypeName) : nonTypeName))))))


noncomputable def «$lift_nameIR_as_nonTypeName:clause:5» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("type" = t)) (fun (_ : Unit) => (.pure ((((nonTypeName.TYPE) : nonTypeName) : nonTypeName))))))


noncomputable def «$lift_nameIR_as_nonTypeName:clause:6» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("priority" = t)) (fun (_ : Unit) => (.pure ((((nonTypeName.PRIORITY) : nonTypeName) : nonTypeName))))))


noncomputable def «$lift_nameIR_as_nonTypeName:clause:7» (input0 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (.pure ((((nonTypeName._ID nameIR) : nonTypeName) : nonTypeName))))


noncomputable def «$lift_nameIR_as_nonTypeName_clauses» (input0 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_nameIR_as_nonTypeName:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_nameIR_as_nonTypeName:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_nameIR_as_nonTypeName:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_nameIR_as_nonTypeName:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_nameIR_as_nonTypeName:clause:4»  input0), fun (_ : _root_.Unit) => («$lift_nameIR_as_nonTypeName:clause:5»  input0), fun (_ : _root_.Unit) => («$lift_nameIR_as_nonTypeName:clause:6»  input0), fun (_ : _root_.Unit) => («$lift_nameIR_as_nonTypeName:clause:7»  input0)]


noncomputable def «$lift_nameIR_as_typeName:clause:0» (input0 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (.bind (.call ⟨typeIdentifier, SpecTecCall.«$lift_nameIR_as_typeIdentifier» nameIR⟩) (fun («exec:1» : typeIdentifier) => (let «eval:0» : typeIdentifier := «exec:1»; (.pure ((«eval:0» : typeName)))))))


noncomputable def «$lift_nameIR_as_typeName_clauses» (input0 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_nameIR_as_typeName:clause:0»  input0)]


noncomputable def «$unflatten_nameList':clause:0» (input0 : SpecTec.nameList) (input1 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameList : SpecTec.nameList := input0; (let «name*» : (_root_.List name) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «name*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((nameList : SpecTec.nameList)))))))


noncomputable def «$unflatten_nameList':clause:1» (input0 : SpecTec.nameList) (input1 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameList : SpecTec.nameList := input0; (let «name*» : (_root_.List name) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «name*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «name*» with | «exec:2» :: «exec:1» => (let name_h : name := «exec:2»; (let «name_t*» : (_root_.List name) := «exec:1»; (.bind (.call ⟨SpecTec.nameList, SpecTecCall.«$unflatten_nameList'» ((SpecTec.nameList.«% ',' %» nameList name_h) : SpecTec.nameList) «name_t*»⟩) (fun («exec:3» : SpecTec.nameList) => (let «eval:0» : SpecTec.nameList := «exec:3»; (.pure ((«eval:0» : SpecTec.nameList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_nameList'_clauses» (input0 : nameList) (input1 : (_root_.List name)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_nameList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_nameList':clause:1»  input0 input1)]


noncomputable def «$lift_value:clause:0» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.call ⟨expression, SpecTecCall.«$sink» expression⟩) (fun («exec:1» : expression) => (let «eval:0» : expression := «exec:1»; (.pure ((«eval:0» : expression)))))))

end SpecTec
