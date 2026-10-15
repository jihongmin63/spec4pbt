import SpecTecDecl0314

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_tableEntryListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableEntryIR : SpecTec.tableEntryIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableEntryIR) := «exec:1»; (.bind (.call ⟨SpecTec.tableEntry, SpecTecCall.«$lift_tableEntryIR» tableEntryIR⟩) (fun («exec:3» : SpecTec.tableEntry) => (let «eval:1» : SpecTec.tableEntry := «exec:3»; (let tableEntry : SpecTec.tableEntry := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.tableEntry), SpecTecCall.«$lift_tableEntryListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.tableEntry)) => (let «tail:1» : (_root_.List SpecTec.tableEntry) := «exec:4»; (.pure (((tableEntry :: «tail:1») : (_root_.List SpecTec.tableEntry))))))))))))) | [] => .unmatch)


noncomputable def «$lift_tableEntryListIR:case_1:iter:0_clauses» (input0 : (_root_.List tableEntryIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableEntryListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_tableEntryListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_tableEntryListIR:clause:0» (input0 : (_root_.List tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableEntryIR*» : (_root_.List tableEntryIR) := input0; (.bind (.call ⟨(_root_.List tableEntry), SpecTecCall.«$lift_tableEntryListIR:case_1:iter:0» «tableEntryIR*»⟩) (fun («exec:1» : (_root_.List tableEntry)) => (let «tableEntry*» : (_root_.List tableEntry) := «exec:1»; (.bind (.call ⟨SpecTec.tableEntryList, SpecTecCall.«$unflatten_tableEntryList» «tableEntry*»⟩) (fun («exec:2» : SpecTec.tableEntryList) => (let «eval:2» : SpecTec.tableEntryList := «exec:2»; (let tableEntryList : SpecTec.tableEntryList := «eval:2»; (.pure ((tableEntryList : SpecTec.tableEntryList)))))))))))


noncomputable def «$lift_tableEntryListIR_clauses» (input0 : (_root_.List tableEntryIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableEntryListIR:clause:0»  input0)]


noncomputable def «$lift_tableCustomPropertyIR:clause:0» (input0 : SpecTec.tableCustomPropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableCustomPropertyIR : SpecTec.tableCustomPropertyIR := input0; (.bind (.guard (((«exec:match:tableCustomPropertyIR:% % CUSTOM % % ';'» tableCustomPropertyIR) = true))) (fun (_ : Unit) => (match tableCustomPropertyIR with | .«% % CUSTOM % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:1»; (let constOptIR : SpecTec.constOptIR := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (let initializerIR : SpecTec.initializerIR := «exec:4»; (.bind (.call ⟨SpecTec.constOpt, SpecTecCall.«$lift_constOptIR» constOptIR⟩) (fun («exec:5» : SpecTec.constOpt) => (let «eval:0» : SpecTec.constOpt := «exec:5»; (let constOpt : SpecTec.constOpt := «eval:0»; (.bind (.call ⟨SpecTec.tableCustomName, SpecTecCall.«$lift_nameIR_as_tableCustomName» nameIR⟩) (fun («exec:6» : SpecTec.tableCustomName) => (let «eval:1» : SpecTec.tableCustomName := «exec:6»; (let tableCustomName : SpecTec.tableCustomName := «eval:1»; (.bind (.call ⟨SpecTec.initializer, SpecTecCall.«$lift_initializerIR» initializerIR⟩) (fun («exec:7» : SpecTec.initializer) => (let «eval:2» : SpecTec.initializer := «exec:7»; (let initializer : SpecTec.initializer := «eval:2»; (.pure ((((tableProperty.«% % % % ';'» annotationList constOpt tableCustomName initializer) : tableProperty) : tableProperty))))))))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_tableCustomPropertyIR_clauses» (input0 : tableCustomPropertyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableCustomPropertyIR:clause:0»  input0)]


noncomputable def «$lift_tableKeysPropertyIR:clause:0» (input0 : tableKeysPropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«KEY '=' `{ % `}» «exec:1» => (let «tableKeyIR*» : (_root_.List tableKeyIR) := «exec:1»; (.bind (.call ⟨SpecTec.tableKeyList, SpecTecCall.«$lift_tableKeyListIR» «tableKeyIR*»⟩) (fun («exec:2» : SpecTec.tableKeyList) => (let «eval:0» : SpecTec.tableKeyList := «exec:2»; (let tableKeyList : SpecTec.tableKeyList := «eval:0»; (.pure ((((tableProperty.«KEY '=' `{ % `}» tableKeyList) : tableProperty) : tableProperty)))))))))


noncomputable def «$lift_tableKeysPropertyIR_clauses» (input0 : tableKeysPropertyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableKeysPropertyIR:clause:0»  input0)]


noncomputable def «$lift_tableActionsPropertyIR:clause:0» (input0 : tableActionsPropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ACTIONS '=' `{ % `}» «exec:1» => (let «tableActionIR*» : (_root_.List tableActionIR) := «exec:1»; (.bind (.call ⟨SpecTec.tableActionList, SpecTecCall.«$lift_tableActionListIR» «tableActionIR*»⟩) (fun («exec:2» : SpecTec.tableActionList) => (let «eval:0» : SpecTec.tableActionList := «exec:2»; (let tableActionList : SpecTec.tableActionList := «eval:0»; (.pure ((((tableProperty.«ACTIONS '=' `{ % `}» tableActionList) : tableProperty) : tableProperty)))))))))


noncomputable def «$lift_tableActionsPropertyIR_clauses» (input0 : tableActionsPropertyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableActionsPropertyIR:clause:0»  input0)]


noncomputable def «$lift_tableDefaultActionPropertyIR:clause:0» (input0 : tableDefaultActionPropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % DEFAULT_ACTION '=' % ';'» «exec:1» «exec:2» «exec:3» => (let annotationList : SpecTec.annotationList := «exec:1»; (let constOptIR : SpecTec.constOptIR := «exec:2»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:3»; (.bind (.call ⟨SpecTec.constOpt, SpecTecCall.«$lift_constOptIR» constOptIR⟩) (fun («exec:4» : SpecTec.constOpt) => (let «eval:0» : SpecTec.constOpt := «exec:4»; (let constOpt : SpecTec.constOpt := «eval:0»; (.bind (.call ⟨SpecTec.expression, SpecTecCall.«$lift_tableActionReferenceIR_as_expression» tableActionReferenceIR⟩) (fun («exec:5» : SpecTec.expression) => (let «eval:1» : SpecTec.expression := «exec:5»; (let expression : SpecTec.expression := «eval:1»; (.pure ((((tableProperty.«% % % % ';'» annotationList constOpt ((tableCustomName._ID "default_action") : tableCustomName) ((initializer.«'=' %» expression) : initializer)) : tableProperty) : tableProperty)))))))))))))))


noncomputable def «$lift_tableDefaultActionPropertyIR_clauses» (input0 : tableDefaultActionPropertyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableDefaultActionPropertyIR:clause:0»  input0)]


noncomputable def «$lift_tableEntriesPropertyIR:clause:0» (input0 : tableEntriesPropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % ENTRIES '=' `{ % `}» «exec:1» «exec:2» «exec:3» => (let annotationList : SpecTec.annotationList := «exec:1»; (let constOptIR : SpecTec.constOptIR := «exec:2»; (let «tableEntryIR*» : (_root_.List tableEntryIR) := «exec:3»; (.bind (.call ⟨SpecTec.constOpt, SpecTecCall.«$lift_constOptIR» constOptIR⟩) (fun («exec:4» : SpecTec.constOpt) => (let «eval:0» : SpecTec.constOpt := «exec:4»; (let constOpt : SpecTec.constOpt := «eval:0»; (.bind (.call ⟨SpecTec.tableEntryList, SpecTecCall.«$lift_tableEntryListIR» «tableEntryIR*»⟩) (fun («exec:5» : SpecTec.tableEntryList) => (let «eval:1» : SpecTec.tableEntryList := «exec:5»; (let tableEntryList : SpecTec.tableEntryList := «eval:1»; (.pure ((((tableProperty.«% % ENTRIES '=' `{ % `}» annotationList constOpt tableEntryList) : tableProperty) : tableProperty)))))))))))))))


noncomputable def «$lift_tableEntriesPropertyIR_clauses» (input0 : tableEntriesPropertyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableEntriesPropertyIR:clause:0»  input0)]


noncomputable def «$lift_tablePropertyIR:clause:0» (input0 : SpecTec.tablePropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tablePropertyIR : SpecTec.tablePropertyIR := input0; (.bind (.guard (((«sub:tablePropertyIR:tableKeysPropertyIR» tablePropertyIR) = true))) (fun (_ : Unit) => (match («$lift_tablePropertyIR:case_1:downcast:0» tablePropertyIR) with | some «exec:1» => (let «eval:0» : SpecTec.tableKeysPropertyIR := «exec:1»; (let tableKeysPropertyIR : SpecTec.tableKeysPropertyIR := «eval:0»; (.bind (.call ⟨tableProperty, SpecTecCall.«$lift_tableKeysPropertyIR» tableKeysPropertyIR⟩) (fun («exec:2» : tableProperty) => (let «eval:1» : tableProperty := «exec:2»; (.pure ((«eval:1» : tableProperty)))))))) | none => .unmatch))))


noncomputable def «$lift_tablePropertyIR:clause:1» (input0 : SpecTec.tablePropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tablePropertyIR : SpecTec.tablePropertyIR := input0; (.bind (.guard (((«sub:tablePropertyIR:tableActionsPropertyIR» tablePropertyIR) = true))) (fun (_ : Unit) => (match («$lift_tablePropertyIR:case_2:downcast:0» tablePropertyIR) with | some «exec:1» => (let «eval:0» : SpecTec.tableActionsPropertyIR := «exec:1»; (let tableActionsPropertyIR : SpecTec.tableActionsPropertyIR := «eval:0»; (.bind (.call ⟨tableProperty, SpecTecCall.«$lift_tableActionsPropertyIR» tableActionsPropertyIR⟩) (fun («exec:2» : tableProperty) => (let «eval:1» : tableProperty := «exec:2»; (.pure ((«eval:1» : tableProperty)))))))) | none => .unmatch))))


noncomputable def «$lift_tablePropertyIR:clause:2» (input0 : SpecTec.tablePropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tablePropertyIR : SpecTec.tablePropertyIR := input0; (.bind (.guard (((«sub:tablePropertyIR:tableDefaultActionPropertyIR» tablePropertyIR) = true))) (fun (_ : Unit) => (match («$lift_tablePropertyIR:case_3:downcast:0» tablePropertyIR) with | some «exec:1» => (let «eval:0» : SpecTec.tableDefaultActionPropertyIR := «exec:1»; (let tableDefaultActionPropertyIR : SpecTec.tableDefaultActionPropertyIR := «eval:0»; (.bind (.call ⟨tableProperty, SpecTecCall.«$lift_tableDefaultActionPropertyIR» tableDefaultActionPropertyIR⟩) (fun («exec:2» : tableProperty) => (let «eval:1» : tableProperty := «exec:2»; (.pure ((«eval:1» : tableProperty)))))))) | none => .unmatch))))


noncomputable def «$lift_tablePropertyIR:clause:3» (input0 : SpecTec.tablePropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tablePropertyIR : SpecTec.tablePropertyIR := input0; (.bind (.guard (((«sub:tablePropertyIR:tableEntriesPropertyIR» tablePropertyIR) = true))) (fun (_ : Unit) => (match («$lift_tablePropertyIR:case_4:downcast:0» tablePropertyIR) with | some «exec:1» => (let «eval:0» : SpecTec.tableEntriesPropertyIR := «exec:1»; (let tableEntriesPropertyIR : SpecTec.tableEntriesPropertyIR := «eval:0»; (.bind (.call ⟨tableProperty, SpecTecCall.«$lift_tableEntriesPropertyIR» tableEntriesPropertyIR⟩) (fun («exec:2» : tableProperty) => (let «eval:1» : tableProperty := «exec:2»; (.pure ((«eval:1» : tableProperty)))))))) | none => .unmatch))))


noncomputable def «$lift_tablePropertyIR:clause:4» (input0 : SpecTec.tablePropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tablePropertyIR : SpecTec.tablePropertyIR := input0; (.bind (.guard (((«sub:tablePropertyIR:tableCustomPropertyIR» tablePropertyIR) = true))) (fun (_ : Unit) => (match («$lift_tablePropertyIR:case_5:downcast:0» tablePropertyIR) with | some «exec:1» => (let «eval:0» : SpecTec.tableCustomPropertyIR := «exec:1»; (let tableCustomPropertyIR : SpecTec.tableCustomPropertyIR := «eval:0»; (.bind (.call ⟨tableProperty, SpecTecCall.«$lift_tableCustomPropertyIR» tableCustomPropertyIR⟩) (fun («exec:2» : tableProperty) => (let «eval:1» : tableProperty := «exec:2»; (.pure ((«eval:1» : tableProperty)))))))) | none => .unmatch))))


noncomputable def «$lift_tablePropertyIR_clauses» (input0 : tablePropertyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tablePropertyIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_tablePropertyIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_tablePropertyIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_tablePropertyIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_tablePropertyIR:clause:4»  input0)]


noncomputable def «$lift_tablePropertyListIR:case_1:iter:0:clause:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List tableProperty)) : (_root_.List tableProperty)))) | _ :: _ => .unmatch)


noncomputable def «$lift_tablePropertyListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tablePropertyIR : SpecTec.tablePropertyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tablePropertyIR) := «exec:1»; (.bind (.call ⟨SpecTec.tableProperty, SpecTecCall.«$lift_tablePropertyIR» tablePropertyIR⟩) (fun («exec:3» : SpecTec.tableProperty) => (let «eval:1» : SpecTec.tableProperty := «exec:3»; (let tableProperty : SpecTec.tableProperty := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.tableProperty), SpecTecCall.«$lift_tablePropertyListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.tableProperty)) => (let «tail:1» : (_root_.List SpecTec.tableProperty) := «exec:4»; (.pure (((tableProperty :: «tail:1») : (_root_.List SpecTec.tableProperty))))))))))))) | [] => .unmatch)


noncomputable def «$lift_tablePropertyListIR:case_1:iter:0_clauses» (input0 : (_root_.List tablePropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tablePropertyListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_tablePropertyListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_tablePropertyListIR:clause:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tablePropertyIR*» : (_root_.List tablePropertyIR) := input0; (.bind (.call ⟨(_root_.List tableProperty), SpecTecCall.«$lift_tablePropertyListIR:case_1:iter:0» «tablePropertyIR*»⟩) (fun («exec:1» : (_root_.List tableProperty)) => (let «tableProperty*» : (_root_.List tableProperty) := «exec:1»; (.bind (.call ⟨SpecTec.tablePropertyList, SpecTecCall.«$unflatten_tablePropertyList» «tableProperty*»⟩) (fun («exec:2» : SpecTec.tablePropertyList) => (let «eval:2» : SpecTec.tablePropertyList := «exec:2»; (let tablePropertyList : SpecTec.tablePropertyList := «eval:2»; (.pure ((tablePropertyList : SpecTec.tablePropertyList)))))))))))


noncomputable def «$lift_tablePropertyListIR_clauses» (input0 : (_root_.List tablePropertyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tablePropertyListIR:clause:0»  input0)]


noncomputable def «$lift_tableDeclarationIR:clause:0» (input0 : tableDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% TABLE % % `{ % `}» «exec:1» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (let «tablePropertyIR*» : (_root_.List tablePropertyIR) := «exec:4»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:5» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:5»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (.bind (.call ⟨SpecTec.tablePropertyList, SpecTecCall.«$lift_tablePropertyListIR» «tablePropertyIR*»⟩) (fun («exec:6» : SpecTec.tablePropertyList) => (let «eval:1» : SpecTec.tablePropertyList := «exec:6»; (let tablePropertyList : SpecTec.tablePropertyList := «eval:1»; (.pure ((((tableDeclaration.«% TABLE % `{ % `}» annotationList name tablePropertyList) : tableDeclaration) : tableDeclaration))))))))))))))))


noncomputable def «$lift_tableDeclarationIR_clauses» (input0 : tableDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableDeclarationIR:clause:0»  input0)]


noncomputable def «$lift_controlTypeDeclarationIR:clause:0» (input0 : controlTypeDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% CONTROL % `< % ',' % `> `( % `) ';'» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := «exec:3»; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := «exec:4»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:5»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:6» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:6»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (let «typeParameterIR*» : (_root_.List typeParameterIR) := («typeParameterIR_expl*» ++ «typeParameterIR_impl*»); (.bind (.call ⟨SpecTec.typeParameterListOpt, SpecTecCall.«$lift_typeParameterListIR» «typeParameterIR*»⟩) (fun («exec:7» : SpecTec.typeParameterListOpt) => (let «eval:1» : SpecTec.typeParameterListOpt := «exec:7»; (let typeParameterListOpt : SpecTec.typeParameterListOpt := «eval:1»; (.bind (.call ⟨SpecTec.parameterList, SpecTecCall.«$lift_parameterListIR» «parameterIR*»⟩) (fun («exec:8» : SpecTec.parameterList) => (let «eval:2» : SpecTec.parameterList := «exec:8»; (let parameterList : SpecTec.parameterList := «eval:2»; (.pure ((((controlTypeDeclaration.«% CONTROL % % `( % `) ';'» annotationList name typeParameterListOpt parameterList) : controlTypeDeclaration) : controlTypeDeclaration))))))))))))))))))))))


noncomputable def «$lift_controlTypeDeclarationIR_clauses» (input0 : controlTypeDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_controlTypeDeclarationIR:clause:0»  input0)]


noncomputable def «$lift_controlBodyIR:clause:0» (input0 : SpecTec.controlBodyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlBodyIR : SpecTec.controlBodyIR := input0; (.bind (.call ⟨blockStatement, SpecTecCall.«$lift_blockStatementIR» controlBodyIR⟩) (fun («exec:1» : blockStatement) => (let «eval:0» : blockStatement := «exec:1»; (.pure ((«eval:0» : controlBody)))))))


noncomputable def «$lift_controlBodyIR_clauses» (input0 : controlBodyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_controlBodyIR:clause:0»  input0)]


noncomputable def «$lift_controlLocalDeclarationIR:clause:0» (input0 : SpecTec.controlLocalDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlLocalDeclarationIR : SpecTec.controlLocalDeclarationIR := input0; (.bind (.guard (((«sub:controlLocalDeclarationIR:constantDeclarationIR» controlLocalDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_controlLocalDeclarationIR:case_1:downcast:0» controlLocalDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.constantDeclarationIR := «exec:1»; (let constantDeclarationIR : SpecTec.constantDeclarationIR := «eval:0»; (.bind (.call ⟨constantDeclaration, SpecTecCall.«$lift_constantDeclarationIR» constantDeclarationIR⟩) (fun («exec:2» : constantDeclaration) => (let «eval:1» : constantDeclaration := «exec:2»; (.pure (((«cast:constantDeclaration:controlLocalDeclaration» «eval:1») : controlLocalDeclaration)))))))) | none => .unmatch))))

end SpecTec
