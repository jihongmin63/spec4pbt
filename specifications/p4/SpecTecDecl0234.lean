import SpecTecDecl0233

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_nameIR_as_tableCustomName:clause:2» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("type" = t)) (fun (_ : Unit) => (.pure ((((tableCustomName.TYPE) : tableCustomName) : tableCustomName))))))


noncomputable def «$lift_nameIR_as_tableCustomName:clause:3» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("priority" = t)) (fun (_ : Unit) => (.pure ((((tableCustomName.PRIORITY) : tableCustomName) : tableCustomName))))))


noncomputable def «$lift_nameIR_as_tableCustomName:clause:4» (input0 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (.bind (.call ⟨identifier, SpecTecCall.«$lift_nameIR_as_identifier» nameIR⟩) (fun («exec:1» : identifier) => (let «eval:0» : identifier := «exec:1»; (.pure (((«cast:identifier:tableCustomName» «eval:0») : tableCustomName)))))))


noncomputable def «$lift_nameIR_as_tableCustomName_clauses» (input0 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_nameIR_as_tableCustomName:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_nameIR_as_tableCustomName:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_nameIR_as_tableCustomName:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_nameIR_as_tableCustomName:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_nameIR_as_tableCustomName:clause:4»  input0)]


noncomputable def «$lift_constantInitializerOptIR_as_initializerOpt:clause:0» (input0 : (_root_.Option constantInitializerIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constantInitializerIR? : (_root_.Option constantInitializerIR) := input0; (.bind (.guard (((_root_.Option.isNone constantInitializerIR?) = true))) (fun (_ : Unit) => (.pure ((((initializerOpt._EMPTY) : initializerOpt) : initializerOpt))))))


noncomputable def «$lift_constantInitializerOptIR_as_initializerOpt:clause:1» (input0 : (_root_.Option SpecTec.constantInitializerIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constantInitializerIR'? : (_root_.Option SpecTec.constantInitializerIR) := input0; (.bind (.guard (((_root_.Option.isSome constantInitializerIR'?) = true))) (fun (_ : Unit) => (match constantInitializerIR'? with | some «exec:1» => (let constantInitializerIR : SpecTec.constantInitializerIR := «exec:1»; (.bind (.call ⟨initializer, SpecTecCall.«$lift_constantInitializerIR_as_initializer» constantInitializerIR⟩) (fun («exec:2» : initializer) => (let «eval:0» : initializer := «exec:2»; (.pure (((«cast:initializer:initializerOpt» «eval:0») : initializerOpt))))))) | none => .unmatch))))


noncomputable def «$lift_constantInitializerOptIR_as_initializerOpt_clauses» (input0 : (_root_.Option constantInitializerIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_constantInitializerOptIR_as_initializerOpt:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_constantInitializerOptIR_as_initializerOpt:clause:1»  input0)]


noncomputable def «$unflatten_nameList:clause:0» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «name*» : (_root_.List name) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «name*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «name*» with | «exec:2» :: «exec:1» => (let name_h : name := «exec:2»; (let «name_t*» : (_root_.List name) := «exec:1»; (.bind (.call ⟨nameList, SpecTecCall.«$unflatten_nameList'» («cast:name:nameList» name_h) «name_t*»⟩) (fun («exec:3» : nameList) => (let «eval:0» : nameList := «exec:3»; (.pure ((«eval:0» : nameList)))))))) | [] => .unmatch))))


noncomputable def «$unflatten_nameList_clauses» (input0 : (_root_.List name)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_nameList:clause:0»  input0)]


noncomputable def «$unflatten_typeParameterList:clause:0» (input0 : (_root_.List typeParameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeParameter*» : (_root_.List typeParameter) := input0; (let «typeParameter'*» : (_root_.List typeParameter) := «typeParameter*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeParameter'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeParameter'*» with | «exec:2» :: «exec:1» => (let typeParameter_h : typeParameter := «exec:2»; (let «typeParameter_t*» : (_root_.List typeParameter) := «exec:1»; (.bind (.call ⟨typeParameterList, SpecTecCall.«$unflatten_typeParameterList'» («cast:name:typeParameterList» typeParameter_h) «typeParameter_t*»⟩) (fun («exec:3» : typeParameterList) => (let «eval:0» : typeParameterList := «exec:3»; (.pure ((«eval:0» : typeParameterList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_typeParameterList_clauses» (input0 : (_root_.List typeParameter)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_typeParameterList:clause:0»  input0)]


noncomputable def «$unflatten_typeParameterListOpt:clause:0» (input0 : (_root_.List typeParameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeParameter*» : (_root_.List typeParameter) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeParameter*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((((typeParameterListOpt._EMPTY) : typeParameterListOpt) : typeParameterListOpt))))))


noncomputable def «$unflatten_typeParameterListOpt:clause:1» (input0 : (_root_.List typeParameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeParameter*» : (_root_.List typeParameter) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeParameter*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeParameter*» with | «exec:2» :: «exec:1» => (let typeParameter_h : typeParameter := «exec:2»; (let «typeParameter_t*» : (_root_.List typeParameter) := «exec:1»; (.bind (.call ⟨typeParameterList, SpecTecCall.«$unflatten_typeParameterList» (typeParameter_h :: «typeParameter_t*»)⟩) (fun («exec:3» : typeParameterList) => (let «eval:0» : typeParameterList := «exec:3»; (.pure ((((typeParameterListOpt.«`< % `>» «eval:0») : typeParameterListOpt) : typeParameterListOpt)))))))) | [] => .unmatch))))


noncomputable def «$unflatten_typeParameterListOpt_clauses» (input0 : (_root_.List typeParameter)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_typeParameterListOpt:clause:0»  input0), fun (_ : _root_.Unit) => («$unflatten_typeParameterListOpt:clause:1»  input0)]


noncomputable def «$unflatten_namedExpressionList:clause:0» (input0 : (_root_.List namedExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «namedExpression*» : (_root_.List namedExpression) := input0; (let «namedExpression'*» : (_root_.List namedExpression) := «namedExpression*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «namedExpression'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «namedExpression'*» with | «exec:2» :: «exec:1» => (let namedExpression_h : namedExpression := «exec:2»; (let «namedExpression_t*» : (_root_.List namedExpression) := «exec:1»; (.bind (.call ⟨namedExpressionList, SpecTecCall.«$unflatten_namedExpressionList'» («cast:namedExpression:namedExpressionList» namedExpression_h) «namedExpression_t*»⟩) (fun («exec:3» : namedExpressionList) => (let «eval:0» : namedExpressionList := «exec:3»; (.pure ((«eval:0» : namedExpressionList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_namedExpressionList_clauses» (input0 : (_root_.List namedExpression)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_namedExpressionList:clause:0»  input0)]


noncomputable def «$unflatten_recordElementExpression:clause:0» (input0 : (_root_.List namedExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «namedExpression*» : (_root_.List namedExpression) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «namedExpression*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «namedExpression*» with | «exec:2» :: «exec:1» => (let namedExpression_h : namedExpression := «exec:2»; (match «exec:1» with | [] => (match namedExpression_h with | .«% '=' %» «exec:3» «exec:4» => (let name_h : name := «exec:3»; (let expression_h : expression := «exec:4»; (.pure ((((recordElementExpression.«% '=' %» name_h expression_h) : recordElementExpression) : recordElementExpression)))))) | _ :: _ => .unmatch)) | [] => .unmatch))))


noncomputable def «$unflatten_recordElementExpression:clause:1» (input0 : (_root_.List namedExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «namedExpression*» : (_root_.List namedExpression) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «namedExpression*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «namedExpression*» with | «exec:2» :: «exec:1» => (let namedExpression_h : namedExpression := «exec:2»; (let «namedExpression_t*» : (_root_.List namedExpression) := «exec:1»; (.bind (.guard ((«namedExpression_t*» ≠ ([] : (_root_.List namedExpression))))) (fun (_ : Unit) => (match namedExpression_h with | .«% '=' %» «exec:3» «exec:4» => (let name_h : name := «exec:3»; (let expression_h : expression := «exec:4»; (.bind (.call ⟨SpecTec.namedExpressionList, SpecTecCall.«$unflatten_namedExpressionList» «namedExpression_t*»⟩) (fun («exec:5» : SpecTec.namedExpressionList) => (let «eval:0» : SpecTec.namedExpressionList := «exec:5»; (let namedExpressionList : SpecTec.namedExpressionList := «eval:0»; (.pure ((((recordElementExpression.«% '=' % ',' %» name_h expression_h namedExpressionList) : recordElementExpression) : recordElementExpression)))))))))))))) | [] => .unmatch))))


noncomputable def «$unflatten_recordElementExpression_clauses» (input0 : (_root_.List namedExpression)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_recordElementExpression:clause:0»  input0), fun (_ : _root_.Unit) => («$unflatten_recordElementExpression:clause:1»  input0)]


noncomputable def «$unflatten_recordElementExpression_with_default:clause:0» (input0 : (_root_.List namedExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «namedExpression*» : (_root_.List namedExpression) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «namedExpression*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «namedExpression*» with | «exec:2» :: «exec:1» => (let namedExpression_h : namedExpression := «exec:2»; (match «exec:1» with | [] => (match namedExpression_h with | .«% '=' %» «exec:3» «exec:4» => (let name_h : name := «exec:3»; (let expression_h : expression := «exec:4»; (.pure ((((recordElementExpression.«% '=' % ',' '...'» name_h expression_h) : recordElementExpression) : recordElementExpression)))))) | _ :: _ => .unmatch)) | [] => .unmatch))))


noncomputable def «$unflatten_recordElementExpression_with_default:clause:1» (input0 : (_root_.List namedExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «namedExpression*» : (_root_.List namedExpression) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «namedExpression*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «namedExpression*» with | «exec:2» :: «exec:1» => (let namedExpression_h : namedExpression := «exec:2»; (let «namedExpression_t*» : (_root_.List namedExpression) := «exec:1»; (.bind (.guard ((«namedExpression_t*» ≠ ([] : (_root_.List namedExpression))))) (fun (_ : Unit) => (match namedExpression_h with | .«% '=' %» «exec:3» «exec:4» => (let name_h : name := «exec:3»; (let expression_h : expression := «exec:4»; (.bind (.call ⟨SpecTec.namedExpressionList, SpecTecCall.«$unflatten_namedExpressionList» «namedExpression_t*»⟩) (fun («exec:5» : SpecTec.namedExpressionList) => (let «eval:0» : SpecTec.namedExpressionList := «exec:5»; (let namedExpressionList : SpecTec.namedExpressionList := «eval:0»; (.pure ((((recordElementExpression.«% '=' % ',' % ',' '...'» name_h expression_h namedExpressionList) : recordElementExpression) : recordElementExpression)))))))))))))) | [] => .unmatch))))


noncomputable def «$unflatten_recordElementExpression_with_default_clauses» (input0 : (_root_.List namedExpression)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_recordElementExpression_with_default:clause:0»  input0), fun (_ : _root_.Unit) => («$unflatten_recordElementExpression_with_default:clause:1»  input0)]


noncomputable def «$lift_nameListIR_as_nonTypeNameList:case_1:iter:0:clause:0» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List name)) : (_root_.List name)))) | _ :: _ => .unmatch)


noncomputable def «$lift_nameListIR_as_nonTypeNameList:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:3» : nonTypeName) => (let «eval:1» : nonTypeName := «exec:3»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:1»); (.bind (.call ⟨(_root_.List SpecTec.name), SpecTecCall.«$lift_nameListIR_as_nonTypeNameList:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.name)) => (let «tail:1» : (_root_.List SpecTec.name) := «exec:4»; (.pure (((name :: «tail:1») : (_root_.List SpecTec.name))))))))))))) | [] => .unmatch)


noncomputable def «$lift_nameListIR_as_nonTypeNameList:case_1:iter:0_clauses» (input0 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_nameListIR_as_nonTypeNameList:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_nameListIR_as_nonTypeNameList:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_nameListIR_as_nonTypeNameList:clause:0» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «nameIR*» : (_root_.List nameIR) := input0; (.bind (.call ⟨(_root_.List name), SpecTecCall.«$lift_nameListIR_as_nonTypeNameList:case_1:iter:0» «nameIR*»⟩) (fun («exec:1» : (_root_.List name)) => (let «name*» : (_root_.List name) := «exec:1»; (.bind (.call ⟨SpecTec.nameList, SpecTecCall.«$unflatten_nameList» «name*»⟩) (fun («exec:2» : SpecTec.nameList) => (let «eval:2» : SpecTec.nameList := «exec:2»; (let nameList : SpecTec.nameList := «eval:2»; (.pure ((nameList : SpecTec.nameList)))))))))))


noncomputable def «$lift_nameListIR_as_nonTypeNameList_clauses» (input0 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_nameListIR_as_nonTypeNameList:clause:0»  input0)]


noncomputable def «$lift_nameIR_as_member:clause:0» (input0 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:1» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:1»; (.pure (((«cast:nonTypeName:name» «eval:0») : member)))))))


noncomputable def «$lift_nameIR_as_member_clauses» (input0 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_nameIR_as_member:clause:0»  input0)]


noncomputable def «$lift_namedValueIR:clause:0» (input0 : namedValueIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% '=' %» «exec:1» «exec:2» => (let nameIR : SpecTec.nameIR := «exec:1»; (let value : SpecTec.value := «exec:2»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:3» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:3»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_value» value⟩) (fun («exec:4» : SpecTec.expression) => (let «eval:1» : SpecTec.expression := «exec:4»; (let expression : SpecTec.expression := «eval:1»; (.pure ((((namedExpression.«% '=' %» name expression) : namedExpression) : namedExpression))))))))))))))


noncomputable def «$lift_namedValueIR_clauses» (input0 : namedValueIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_namedValueIR:clause:0»  input0)]


noncomputable def «$lift_namedValueListIR:case_1:iter:0:clause:0» (input0 : (_root_.List namedValueIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List namedExpression)) : (_root_.List namedExpression)))) | _ :: _ => .unmatch)

end SpecTec
