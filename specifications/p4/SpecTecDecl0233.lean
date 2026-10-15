import SpecTecDecl0232

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$V1Model_meta_fields_of_index:case_1:pattern-iter:4_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$V1Model_meta_fields_of_index:case_1:pattern-iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («$V1Model_meta_fields_of_index:case_1:pattern-iter:4:clause:1»  input0)]


noncomputable def «$V1Model_meta_fields_of_index:case_1:pattern-iter:7:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List typeIR)), ([] : (_root_.List nameIR)))) : ((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List nameIR)))))) | _ :: _ => .unmatch)


noncomputable def «$V1Model_meta_fields_of_index:case_1:pattern-iter:7:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList' : annotationList := «exec:3»; (let _typeIR' : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List nameIR))), SpecTecCall.«$V1Model_meta_fields_of_index:case_1:pattern-iter:7» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List nameIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List typeIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List nameIR) := ((«exec:6»).2).2; (.pure ((((_annotationList' :: «pattern-tail:1»), ((_typeIR' :: «pattern-tail:2»), (nameIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List nameIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$V1Model_meta_fields_of_index:case_1:pattern-iter:7_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$V1Model_meta_fields_of_index:case_1:pattern-iter:7:clause:0»  input0), fun (_ : _root_.Unit) => («$V1Model_meta_fields_of_index:case_1:pattern-iter:7:clause:1»  input0)]


noncomputable def «Call_eval:controlApplyMethodCallee-copyin-exit:iter:4:clause:0» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId callableDef))) : (_root_.List (pair callTargetId callableDef))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-copyin-exit:iter:4:clause:1» (input0 : (_root_.List SpecTec.actionDef)) (input1 : (_root_.List SpecTec.callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let actionDef : SpecTec.actionDef := «exec:2»; (let «tail:0» : (_root_.List SpecTec.actionDef) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId : SpecTec.callableId := «exec:4»; (let «tail:1» : (_root_.List SpecTec.callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId callableDef)), SpecTecCall.«Call_eval:controlApplyMethodCallee-copyin-exit:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId callableDef))) => (let «tail:2» : (_root_.List (pair callTargetId callableDef)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId («cast:actionDef:callableDef» actionDef)) : (pair SpecTec.callableId callableDef)) :: «tail:2») : (_root_.List (pair callTargetId callableDef)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-copyin-exit:iter:4_clauses» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-copyin-exit:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-copyin-exit:iter:4:clause:1»  input0 input1)]


noncomputable def «Call_eval:controlApplyMethodCallee-localDecl-exit:iter:4:clause:0» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId callableDef))) : (_root_.List (pair callTargetId callableDef))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-localDecl-exit:iter:4:clause:1» (input0 : (_root_.List SpecTec.actionDef)) (input1 : (_root_.List SpecTec.callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let actionDef : SpecTec.actionDef := «exec:2»; (let «tail:0» : (_root_.List SpecTec.actionDef) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId : SpecTec.callableId := «exec:4»; (let «tail:1» : (_root_.List SpecTec.callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId callableDef)), SpecTecCall.«Call_eval:controlApplyMethodCallee-localDecl-exit:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId callableDef))) => (let «tail:2» : (_root_.List (pair callTargetId callableDef)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId («cast:actionDef:callableDef» actionDef)) : (pair SpecTec.callableId callableDef)) :: «tail:2») : (_root_.List (pair callTargetId callableDef)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-localDecl-exit:iter:4_clauses» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-localDecl-exit:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-localDecl-exit:iter:4:clause:1»  input0 input1)]


noncomputable def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:iter:4:clause:0» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId callableDef))) : (_root_.List (pair callTargetId callableDef))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:iter:4:clause:1» (input0 : (_root_.List SpecTec.actionDef)) (input1 : (_root_.List SpecTec.callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let actionDef : SpecTec.actionDef := «exec:2»; (let «tail:0» : (_root_.List SpecTec.actionDef) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId : SpecTec.callableId := «exec:4»; (let «tail:1» : (_root_.List SpecTec.callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId callableDef)), SpecTecCall.«Call_eval:controlApplyMethodCallee-controlBodyIR-exit:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId callableDef))) => (let «tail:2» : (_root_.List (pair callTargetId callableDef)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId («cast:actionDef:callableDef» actionDef)) : (pair SpecTec.callableId callableDef)) :: «tail:2») : (_root_.List (pair callTargetId callableDef)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:iter:4_clauses» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-controlBodyIR-exit:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-controlBodyIR-exit:iter:4:clause:1»  input0 input1)]


noncomputable def «Call_eval:controlApplyMethodCallee-cont:iter:4:clause:0» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId callableDef))) : (_root_.List (pair callTargetId callableDef))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-cont:iter:4:clause:1» (input0 : (_root_.List SpecTec.actionDef)) (input1 : (_root_.List SpecTec.callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let actionDef : SpecTec.actionDef := «exec:2»; (let «tail:0» : (_root_.List SpecTec.actionDef) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId : SpecTec.callableId := «exec:4»; (let «tail:1» : (_root_.List SpecTec.callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId callableDef)), SpecTecCall.«Call_eval:controlApplyMethodCallee-cont:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId callableDef))) => (let «tail:2» : (_root_.List (pair callTargetId callableDef)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId («cast:actionDef:callableDef» actionDef)) : (pair SpecTec.callableId callableDef)) :: «tail:2») : (_root_.List (pair callTargetId callableDef)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Call_eval:controlApplyMethodCallee-cont:iter:4_clauses» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-cont:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_eval:controlApplyMethodCallee-cont:iter:4:clause:1»  input0 input1)]


noncomputable def «$unflatten_argumentListNonEmpty:clause:0» (input0 : (_root_.List argument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «argument*» : (_root_.List argument) := input0; (let «argument'*» : (_root_.List argument) := «argument*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «argument'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «argument'*» with | «exec:2» :: «exec:1» => (let argument_h : argument := «exec:2»; (let «argument_t*» : (_root_.List argument) := «exec:1»; (.bind (.call ⟨argumentListNonEmpty, SpecTecCall.«$unflatten_argumentListNonEmpty'» («cast:argument:argumentListNonEmpty» argument_h) «argument_t*»⟩) (fun («exec:3» : argumentListNonEmpty) => (let «eval:0» : argumentListNonEmpty := «exec:3»; (.pure ((«eval:0» : argumentListNonEmpty)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_argumentListNonEmpty_clauses» (input0 : (_root_.List argument)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_argumentListNonEmpty:clause:0»  input0)]


noncomputable def «$unflatten_argumentList:clause:0» (input0 : (_root_.List argument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «argument*» : (_root_.List argument) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «argument*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((((argumentList._EMPTY) : argumentList) : argumentList))))))


noncomputable def «$unflatten_argumentList:clause:1» (input0 : (_root_.List argument)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «argument*» : (_root_.List argument) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «argument*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «argument*» with | «exec:2» :: «exec:1» => (let argument_h : argument := «exec:2»; (let «argument_t*» : (_root_.List argument) := «exec:1»; (.bind (.call ⟨argumentListNonEmpty, SpecTecCall.«$unflatten_argumentListNonEmpty» (argument_h :: «argument_t*»)⟩) (fun («exec:3» : argumentListNonEmpty) => (let «eval:0» : argumentListNonEmpty := «exec:3»; (.pure (((«cast:argumentListNonEmpty:argumentList» «eval:0») : argumentList)))))))) | [] => .unmatch))))


noncomputable def «$unflatten_argumentList_clauses» (input0 : (_root_.List argument)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_argumentList:clause:0»  input0), fun (_ : _root_.Unit) => («$unflatten_argumentList:clause:1»  input0)]


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:9:clause:0» (input0 : SpecTec.enumTypeDefIR) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let enumTypeDefIR : SpecTec.enumTypeDefIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List varTypeIR)) : (_root_.List varTypeIR)))) | _ :: _ => .unmatch))


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:9:clause:1» (input0 : SpecTec.enumTypeDefIR) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let enumTypeDefIR : SpecTec.enumTypeDefIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let value_field : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (let varTypeIR : SpecTec.varTypeIR := ((SpecTec.varTypeIR.«% % % %» ((direction._EMPTY) : direction) («cast:enumTypeIR:typeIR» enumTypeDefIR) ((ctk.LCTK) : ctk) (_root_.Option.some value_field)) : SpecTec.varTypeIR); (.bind (.call ⟨(_root_.List SpecTec.varTypeIR), SpecTecCall.«Decl_ok:enumTypeDeclaration-non-serializable:iter:9» enumTypeDefIR «tail:0»⟩) (fun («exec:3» : (_root_.List SpecTec.varTypeIR)) => (let «tail:1» : (_root_.List SpecTec.varTypeIR) := «exec:3»; (.pure (((varTypeIR :: «tail:1») : (_root_.List SpecTec.varTypeIR)))))))))) | [] => .unmatch))


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:9_clauses» (input0 : enumTypeDefIR) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-non-serializable:iter:9:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-non-serializable:iter:9:clause:1»  input0 input1)]


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:7:clause:0» (input0 : SpecTec.enumTypeDefIR) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let enumTypeDefIR : SpecTec.enumTypeDefIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List varTypeIR)) : (_root_.List varTypeIR)))) | _ :: _ => .unmatch))


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:7:clause:1» (input0 : SpecTec.enumTypeDefIR) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let enumTypeDefIR : SpecTec.enumTypeDefIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let value_field : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (let varTypeIR : SpecTec.varTypeIR := ((SpecTec.varTypeIR.«% % % %» ((direction._EMPTY) : direction) («cast:enumTypeIR:typeIR» enumTypeDefIR) ((ctk.LCTK) : ctk) (_root_.Option.some value_field)) : SpecTec.varTypeIR); (.bind (.call ⟨(_root_.List SpecTec.varTypeIR), SpecTecCall.«Decl_ok:enumTypeDeclaration-serializable:iter:7» enumTypeDefIR «tail:0»⟩) (fun («exec:3» : (_root_.List SpecTec.varTypeIR)) => (let «tail:1» : (_root_.List SpecTec.varTypeIR) := «exec:3»; (.pure (((varTypeIR :: «tail:1») : (_root_.List SpecTec.varTypeIR)))))))))) | [] => .unmatch))


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:7_clauses» (input0 : enumTypeDefIR) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-serializable:iter:7:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-serializable:iter:7:clause:1»  input0 input1)]


noncomputable def «$unflatten_expressionList:clause:0» (input0 : (_root_.List expression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «expression*» : (_root_.List expression) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «expression*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((((expressionList._EMPTY) : expressionList) : expressionList))))))


noncomputable def «$unflatten_expressionList:clause:1» (input0 : (_root_.List expression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «expression*» : (_root_.List expression) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «expression*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «expression*» with | «exec:2» :: «exec:1» => (let expression_h : expression := «exec:2»; (let «expression_t*» : (_root_.List expression) := «exec:1»; (.bind (.call ⟨expressionList, SpecTecCall.«$unflatten_expressionList'» («cast:expression:expressionList» expression_h) «expression_t*»⟩) (fun («exec:3» : expressionList) => (let «eval:0» : expressionList := «exec:3»; (.pure ((«eval:0» : expressionList)))))))) | [] => .unmatch))))


noncomputable def «$unflatten_expressionList_clauses» (input0 : (_root_.List expression)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_expressionList:clause:0»  input0), fun (_ : _root_.Unit) => («$unflatten_expressionList:clause:1»  input0)]


noncomputable def «$lift_nameIR_as_tableCustomName:clause:0» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("apply" = t)) (fun (_ : Unit) => (.pure ((((tableCustomName.APPLY) : tableCustomName) : tableCustomName))))))


noncomputable def «$lift_nameIR_as_tableCustomName:clause:1» (input0 : nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard ("state" = t)) (fun (_ : Unit) => (.pure ((((tableCustomName.STATE) : tableCustomName) : tableCustomName))))))

end SpecTec
