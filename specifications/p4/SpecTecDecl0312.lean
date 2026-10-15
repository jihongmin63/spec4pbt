import SpecTecDecl0311

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_externMethodPrototypeIR_clauses» (input0 : externMethodPrototypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_externMethodPrototypeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_externMethodPrototypeIR:clause:1»  input0)]


noncomputable def «$lift_externObjectDeclarationIR:case_1:iter:2:clause:0» (input0 : (_root_.List externConstructorPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List externConstructorPrototype)) : (_root_.List externConstructorPrototype)))) | _ :: _ => .unmatch)


noncomputable def «$lift_externObjectDeclarationIR:case_1:iter:2:clause:1» (input0 : (_root_.List SpecTec.externConstructorPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externConstructorPrototypeIR : SpecTec.externConstructorPrototypeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externConstructorPrototypeIR) := «exec:1»; (.bind (.call ⟨SpecTec.externConstructorPrototype, SpecTecCall.«$lift_externConstructorPrototypeIR» externConstructorPrototypeIR⟩) (fun («exec:3» : SpecTec.externConstructorPrototype) => (let «eval:3» : SpecTec.externConstructorPrototype := «exec:3»; (let externConstructorPrototype : SpecTec.externConstructorPrototype := «eval:3»; (.bind (.call ⟨(_root_.List SpecTec.externConstructorPrototype), SpecTecCall.«$lift_externObjectDeclarationIR:case_1:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.externConstructorPrototype)) => (let «tail:1» : (_root_.List SpecTec.externConstructorPrototype) := «exec:4»; (.pure (((externConstructorPrototype :: «tail:1») : (_root_.List SpecTec.externConstructorPrototype))))))))))))) | [] => .unmatch)


noncomputable def «$lift_externObjectDeclarationIR:case_1:iter:2_clauses» (input0 : (_root_.List externConstructorPrototypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_externObjectDeclarationIR:case_1:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_externObjectDeclarationIR:case_1:iter:2:clause:1»  input0)]


noncomputable def «$lift_externObjectDeclarationIR:case_1:iter:4:clause:0» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List externMethodPrototype)) : (_root_.List externMethodPrototype)))) | _ :: _ => .unmatch)


noncomputable def «$lift_externObjectDeclarationIR:case_1:iter:4:clause:1» (input0 : (_root_.List SpecTec.externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externMethodPrototypeIR) := «exec:1»; (.bind (.call ⟨SpecTec.externMethodPrototype, SpecTecCall.«$lift_externMethodPrototypeIR» externMethodPrototypeIR⟩) (fun («exec:3» : SpecTec.externMethodPrototype) => (let «eval:5» : SpecTec.externMethodPrototype := «exec:3»; (let externMethodPrototype : SpecTec.externMethodPrototype := «eval:5»; (.bind (.call ⟨(_root_.List SpecTec.externMethodPrototype), SpecTecCall.«$lift_externObjectDeclarationIR:case_1:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.externMethodPrototype)) => (let «tail:1» : (_root_.List SpecTec.externMethodPrototype) := «exec:4»; (.pure (((externMethodPrototype :: «tail:1») : (_root_.List SpecTec.externMethodPrototype))))))))))))) | [] => .unmatch)


noncomputable def «$lift_externObjectDeclarationIR:case_1:iter:4_clauses» (input0 : (_root_.List externMethodPrototypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_externObjectDeclarationIR:case_1:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_externObjectDeclarationIR:case_1:iter:4:clause:1»  input0)]


noncomputable def «$lift_externObjectDeclarationIR:clause:0» (input0 : externObjectDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% EXTERN % `< % ',' `> `{ % % `}» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let «typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «externConstructorPrototypeIR*» : (_root_.List externConstructorPrototypeIR) := «exec:4»; (let «externMethodPrototypeIR*» : (_root_.List externMethodPrototypeIR) := «exec:5»; (.bind (.call ⟨SpecTec.nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:6» : SpecTec.nonTypeName) => (let «eval:0» : SpecTec.nonTypeName := «exec:6»; (let nonTypeName : SpecTec.nonTypeName := «eval:0»; (.bind (.call ⟨SpecTec.typeParameterListOpt, SpecTecCall.«$lift_typeParameterListIR» «typeParameterIR*»⟩) (fun («exec:7» : SpecTec.typeParameterListOpt) => (let «eval:1» : SpecTec.typeParameterListOpt := «exec:7»; (let typeParameterListOpt : SpecTec.typeParameterListOpt := «eval:1»; (.bind (.call ⟨(_root_.List externConstructorPrototype), SpecTecCall.«$lift_externObjectDeclarationIR:case_1:iter:2» «externConstructorPrototypeIR*»⟩) (fun («exec:8» : (_root_.List externConstructorPrototype)) => (let «externConstructorPrototype*» : (_root_.List externConstructorPrototype) := «exec:8»; (.bind (.call ⟨(_root_.List externMethodPrototype), SpecTecCall.«$lift_externObjectDeclarationIR:case_1:iter:4» «externMethodPrototypeIR*»⟩) (fun («exec:9» : (_root_.List externMethodPrototype)) => (let «externMethodPrototype*» : (_root_.List externMethodPrototype) := «exec:9»; (let «externConstructorOrMethodPrototype*» : (_root_.List externConstructorOrMethodPrototype) := ((_root_.List.map (fun («cast:item» : externConstructorPrototype) => («cast:externConstructorPrototype:externConstructorOrMethodPrototype» «cast:item»)) «externConstructorPrototype*») ++ (_root_.List.map (fun («cast:item» : externMethodPrototype) => («cast:externMethodPrototype:externConstructorOrMethodPrototype» «cast:item»)) «externMethodPrototype*»)); (.bind (.call ⟨SpecTec.externConstructorOrMethodPrototypeList, SpecTecCall.«$unflatten_externConstructorOrMethodPrototypeList» «externConstructorOrMethodPrototype*»⟩) (fun («exec:10» : SpecTec.externConstructorOrMethodPrototypeList) => (let «eval:6» : SpecTec.externConstructorOrMethodPrototypeList := «exec:10»; (let externConstructorOrMethodPrototypeList : SpecTec.externConstructorOrMethodPrototypeList := «eval:6»; (.pure ((((externObjectDeclaration.«% EXTERN % % `{ % `}» annotationList nonTypeName typeParameterListOpt externConstructorOrMethodPrototypeList) : externObjectDeclaration) : externObjectDeclaration))))))))))))))))))))))))))))


noncomputable def «$lift_externObjectDeclarationIR_clauses» (input0 : externObjectDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_externObjectDeclarationIR:clause:0»  input0)]


noncomputable def «$lift_externDeclarationIR:clause:0» (input0 : SpecTec.externDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externDeclarationIR : SpecTec.externDeclarationIR := input0; (.bind (.guard (((«sub:externDeclarationIR:externFunctionDeclarationIR» externDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_externDeclarationIR:case_1:downcast:0» externDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.externFunctionDeclarationIR := «exec:1»; (let externFunctionDeclarationIR : SpecTec.externFunctionDeclarationIR := «eval:0»; (.bind (.call ⟨externFunctionDeclaration, SpecTecCall.«$lift_externFunctionDeclarationIR» externFunctionDeclarationIR⟩) (fun («exec:2» : externFunctionDeclaration) => (let «eval:1» : externFunctionDeclaration := «exec:2»; (.pure (((«cast:externFunctionDeclaration:externDeclaration» «eval:1») : externDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_externDeclarationIR:clause:1» (input0 : SpecTec.externDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externDeclarationIR : SpecTec.externDeclarationIR := input0; (.bind (.guard (((«sub:externDeclarationIR:externObjectDeclarationIR» externDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_externDeclarationIR:case_2:downcast:0» externDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.externObjectDeclarationIR := «exec:1»; (let externObjectDeclarationIR : SpecTec.externObjectDeclarationIR := «eval:0»; (.bind (.call ⟨externObjectDeclaration, SpecTecCall.«$lift_externObjectDeclarationIR» externObjectDeclarationIR⟩) (fun («exec:2» : externObjectDeclaration) => (let «eval:1» : externObjectDeclaration := «exec:2»; (.pure (((«cast:externObjectDeclaration:externDeclaration» «eval:1») : externDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_externDeclarationIR_clauses» (input0 : externDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_externDeclarationIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_externDeclarationIR:clause:1»  input0)]


noncomputable def «$lift_selectCaseIR:clause:0» (input0 : selectCaseIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% ':' % ';'» «exec:1» «exec:2» => (let keysetExpressionIR : SpecTec.keysetExpressionIR := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (.bind (.call ⟨SpecTec.keysetExpression, SpecTecCall.«$lift_keysetExpressionIR» keysetExpressionIR⟩) (fun («exec:3» : SpecTec.keysetExpression) => (let «eval:0» : SpecTec.keysetExpression := «exec:3»; (let keysetExpression : SpecTec.keysetExpression := «eval:0»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:4» : nonTypeName) => (let «eval:1» : nonTypeName := «exec:4»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:1»); (.pure ((((selectCase.«% ':' % ';'» keysetExpression name) : selectCase) : selectCase))))))))))))))


noncomputable def «$lift_selectCaseIR_clauses» (input0 : selectCaseIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_selectCaseIR:clause:0»  input0)]


noncomputable def «$lift_selectCaseListIR:case_1:iter:0:clause:0» (input0 : (_root_.List selectCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List selectCase)) : (_root_.List selectCase)))) | _ :: _ => .unmatch)


noncomputable def «$lift_selectCaseListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.selectCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let selectCaseIR : SpecTec.selectCaseIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.selectCaseIR) := «exec:1»; (.bind (.call ⟨SpecTec.selectCase, SpecTecCall.«$lift_selectCaseIR» selectCaseIR⟩) (fun («exec:3» : SpecTec.selectCase) => (let «eval:1» : SpecTec.selectCase := «exec:3»; (let selectCase : SpecTec.selectCase := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.selectCase), SpecTecCall.«$lift_selectCaseListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.selectCase)) => (let «tail:1» : (_root_.List SpecTec.selectCase) := «exec:4»; (.pure (((selectCase :: «tail:1») : (_root_.List SpecTec.selectCase))))))))))))) | [] => .unmatch)


noncomputable def «$lift_selectCaseListIR:case_1:iter:0_clauses» (input0 : (_root_.List selectCaseIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_selectCaseListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_selectCaseListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_selectCaseListIR:clause:0» (input0 : (_root_.List selectCaseIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «selectCaseIR*» : (_root_.List selectCaseIR) := input0; (.bind (.call ⟨(_root_.List selectCase), SpecTecCall.«$lift_selectCaseListIR:case_1:iter:0» «selectCaseIR*»⟩) (fun («exec:1» : (_root_.List selectCase)) => (let «selectCase*» : (_root_.List selectCase) := «exec:1»; (.bind (.call ⟨SpecTec.selectCaseList, SpecTecCall.«$unflatten_selectCaseList» «selectCase*»⟩) (fun («exec:2» : SpecTec.selectCaseList) => (let «eval:2» : SpecTec.selectCaseList := «exec:2»; (let selectCaseList : SpecTec.selectCaseList := «eval:2»; (.pure ((selectCaseList : SpecTec.selectCaseList)))))))))))


noncomputable def «$lift_selectCaseListIR_clauses» (input0 : (_root_.List selectCaseIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_selectCaseListIR:clause:0»  input0)]


noncomputable def «$lift_selectExpressionIR:clause:0» (input0 : selectExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«SELECT `( % `) `{ % `}» «exec:1» «exec:2» => (let typedExpressionListIR : SpecTec.typedExpressionListIR := «exec:1»; (let «selectCaseIR*» : (_root_.List selectCaseIR) := «exec:2»; (.bind (.call ⟨SpecTec.expressionList, SpecTecCall.«$lift_typedExpressionListIR» typedExpressionListIR⟩) (fun («exec:3» : SpecTec.expressionList) => (let «eval:0» : SpecTec.expressionList := «exec:3»; (let expressionList : SpecTec.expressionList := «eval:0»; (.bind (.call ⟨SpecTec.selectCaseList, SpecTecCall.«$lift_selectCaseListIR» «selectCaseIR*»⟩) (fun («exec:4» : SpecTec.selectCaseList) => (let «eval:1» : SpecTec.selectCaseList := «exec:4»; (let selectCaseList : SpecTec.selectCaseList := «eval:1»; (.pure ((((selectExpression.«SELECT `( % `) `{ % `}» expressionList selectCaseList) : selectExpression) : selectExpression))))))))))))))


noncomputable def «$lift_selectExpressionIR_clauses» (input0 : selectExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_selectExpressionIR:clause:0»  input0)]


noncomputable def «$lift_stateExpressionIR:clause:0» (input0 : SpecTec.stateExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let stateExpressionIR : SpecTec.stateExpressionIR := input0; (.bind (.guard (((«exec:match:stateExpressionIR:% ';'» stateExpressionIR) = true))) (fun (_ : Unit) => (match stateExpressionIR with | .«% ';'» «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:2» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:2»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (.pure ((((stateExpression.«% ';'» name) : stateExpression) : stateExpression)))))))) | _ => .unmatch))))


noncomputable def «$lift_stateExpressionIR:clause:1» (input0 : SpecTec.stateExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let stateExpressionIR : SpecTec.stateExpressionIR := input0; (.bind (.guard (((«sub:stateExpressionIR:selectExpressionIR» stateExpressionIR) = true))) (fun (_ : Unit) => (match («$lift_stateExpressionIR:case_2:downcast:0» stateExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.selectExpressionIR := «exec:1»; (let selectExpressionIR : SpecTec.selectExpressionIR := «eval:0»; (.bind (.call ⟨selectExpression, SpecTecCall.«$lift_selectExpressionIR» selectExpressionIR⟩) (fun («exec:2» : selectExpression) => (let «eval:1» : selectExpression := «exec:2»; (.pure (((«cast:selectExpression:stateExpression» «eval:1») : stateExpression)))))))) | none => .unmatch))))


noncomputable def «$lift_stateExpressionIR_clauses» (input0 : stateExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_stateExpressionIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_stateExpressionIR:clause:1»  input0)]


noncomputable def «$lift_transitionStatementIR:clause:0» (input0 : transitionStatementIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TRANSITION «exec:1» => (let stateExpressionIR : SpecTec.stateExpressionIR := «exec:1»; (.bind (.call ⟨SpecTec.stateExpression, SpecTecCall.«$lift_stateExpressionIR» stateExpressionIR⟩) (fun («exec:2» : SpecTec.stateExpression) => (let «eval:0» : SpecTec.stateExpression := «exec:2»; (let stateExpression : SpecTec.stateExpression := «eval:0»; (.pure ((((transitionStatement.TRANSITION stateExpression) : transitionStatement) : transitionStatement)))))))))


noncomputable def «$lift_transitionStatementIR_clauses» (input0 : transitionStatementIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_transitionStatementIR:clause:0»  input0)]


noncomputable def «$lift_typeIR_as_valueSetType:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨SpecTec.type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:1» : SpecTec.type) => (let «eval:0» : SpecTec.type := «exec:1»; (let type : SpecTec.type := «eval:0»; (.bind (.guard (((«sub:type:baseType» type) = true))) (fun (_ : Unit) => (match («$lift_typeIR_as_valueSetType:case_1:downcast:1» type) with | some «exec:2» => (let «eval:1» : SpecTec.baseType := «exec:2»; (let baseType : SpecTec.baseType := «eval:1»; (.pure (((«cast:baseType:valueSetType» baseType) : valueSetType))))) | none => .unmatch))))))))


noncomputable def «$lift_typeIR_as_valueSetType:clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨SpecTec.type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:1» : SpecTec.type) => (let «eval:0» : SpecTec.type := «exec:1»; (let type : SpecTec.type := «eval:0»; (.bind (.guard (((«sub:type:tupleType» type) = true))) (fun (_ : Unit) => (match («$lift_typeIR_as_valueSetType:case_2:downcast:1» type) with | some «exec:2» => (let «eval:1» : SpecTec.tupleType := «exec:2»; (let tupleType : SpecTec.tupleType := «eval:1»; (.pure (((«cast:tupleType:valueSetType» tupleType) : valueSetType))))) | none => .unmatch))))))))


noncomputable def «$lift_typeIR_as_valueSetType:clause:2» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨SpecTec.type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:1» : SpecTec.type) => (let «eval:0» : SpecTec.type := «exec:1»; (let type : SpecTec.type := «eval:0»; (.bind (.guard (((«sub:type:prefixedTypeName» type) = true))) (fun (_ : Unit) => (match («$lift_typeIR_as_valueSetType:case_3:downcast:1» type) with | some «exec:2» => (let «eval:1» : SpecTec.prefixedTypeName := «exec:2»; (let prefixedTypeName : SpecTec.prefixedTypeName := «eval:1»; (.pure (((«cast:prefixedTypeName:valueSetType» prefixedTypeName) : valueSetType))))) | none => .unmatch))))))))


noncomputable def «$lift_typeIR_as_valueSetType_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeIR_as_valueSetType:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typeIR_as_valueSetType:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_typeIR_as_valueSetType:clause:2»  input0)]


noncomputable def «$lift_valueSetDeclarationIR:clause:0» (input0 : valueSetDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% VALUE_SET `< % `> `( % `) % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:3»; (let nameIR : SpecTec.nameIR := «exec:4»; (.bind (.call ⟨SpecTec.valueSetType, SpecTecCall.«$lift_typeIR_as_valueSetType» typeIR⟩) (fun («exec:5» : SpecTec.valueSetType) => (let «eval:0» : SpecTec.valueSetType := «exec:5»; (let valueSetType : SpecTec.valueSetType := «eval:0»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_typedExpressionIR» typedExpressionIR⟩) (fun («exec:6» : SpecTec.expression) => (let «eval:1» : SpecTec.expression := «exec:6»; (let expression : SpecTec.expression := «eval:1»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:7» : nonTypeName) => (let «eval:2» : nonTypeName := «exec:7»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:2»); (.pure ((((valueSetDeclaration.«% VALUE_SET `< % `> `( % `) % ';'» annotationList valueSetType expression name) : valueSetDeclaration) : valueSetDeclaration))))))))))))))))))))


noncomputable def «$lift_valueSetDeclarationIR_clauses» (input0 : valueSetDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_valueSetDeclarationIR:clause:0»  input0)]

end SpecTec
