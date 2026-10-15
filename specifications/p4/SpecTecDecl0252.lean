import SpecTecDecl0251

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$is_tableKeysProperty:clause:0» (input0 : SpecTec.tableProperty) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableProperty : SpecTec.tableProperty := input0; (.bind (.guard (((«exec:match:tableProperty:KEY '=' `{ % `}» tableProperty) = true))) (fun (_ : Unit) => (match tableProperty with | .«KEY '=' `{ % `}» «exec:1» => (let _tableKeyList : tableKeyList := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch))))


noncomputable def «$is_tableKeysProperty:clause:1» (input0 : tableProperty) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _tableProperty : tableProperty := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_tableKeysProperty_clauses» (input0 : tableProperty) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_tableKeysProperty:clause:0»  input0), fun (_ : _root_.Unit) => («$is_tableKeysProperty:clause:1»  input0)]


noncomputable def «Table_ok:zero-default-action:iter:0:clause:0» (input0 : (_root_.List tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «Table_ok:zero-default-action:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableProperty : SpecTec.tableProperty := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableProperty) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_tableKeysProperty» tableProperty⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:zero-default-action:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:1» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «Table_ok:zero-default-action:iter:0_clauses» (input0 : (_root_.List tableProperty)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Table_ok:zero-default-action:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («Table_ok:zero-default-action:iter:0:clause:1»  input0)]


noncomputable def «Table_ok:one-default-action:iter:0:clause:0» (input0 : (_root_.List tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «Table_ok:one-default-action:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableProperty : SpecTec.tableProperty := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableProperty) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_tableKeysProperty» tableProperty⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:one-default-action:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:1» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «Table_ok:one-default-action:iter:0_clauses» (input0 : (_root_.List tableProperty)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Table_ok:one-default-action:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («Table_ok:one-default-action:iter:0:clause:1»  input0)]


noncomputable def «$flatten_tablePropertyList:clause:0» (input0 : SpecTec.tablePropertyList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tablePropertyList : SpecTec.tablePropertyList := input0; (.bind (.guard (((«exec:match:tablePropertyList:_EMPTY» tablePropertyList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List tableProperty)) : (_root_.List tableProperty)))))))


noncomputable def «$flatten_tablePropertyList:clause:1» (input0 : SpecTec.tablePropertyList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tablePropertyList' : SpecTec.tablePropertyList := input0; (.bind (.guard (((«exec:match:tablePropertyList:% %» tablePropertyList') = true))) (fun (_ : Unit) => (match tablePropertyList' with | .«% %» «exec:1» «exec:2» => (let tablePropertyList : SpecTec.tablePropertyList := «exec:1»; (let tableProperty : SpecTec.tableProperty := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.tableProperty), SpecTecCall.«$flatten_tablePropertyList» tablePropertyList⟩) (fun («exec:3» : (_root_.List SpecTec.tableProperty)) => (let «eval:0» : (_root_.List SpecTec.tableProperty) := «exec:3»; (.pure (((«eval:0» ++ ([tableProperty] : (_root_.List SpecTec.tableProperty))) : (_root_.List SpecTec.tableProperty))))))))) | _ => .unmatch))))


noncomputable def «$flatten_tablePropertyList_clauses» (input0 : tablePropertyList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_tablePropertyList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_tablePropertyList:clause:1»  input0)]


noncomputable def «$flatten_typeFieldList:clause:0» (input0 : SpecTec.typeFieldList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeFieldList : SpecTec.typeFieldList := input0; (.bind (.guard (((«exec:match:typeFieldList:_EMPTY» typeFieldList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List typeField)) : (_root_.List typeField)))))))


noncomputable def «$flatten_typeFieldList:clause:1» (input0 : SpecTec.typeFieldList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeFieldList' : SpecTec.typeFieldList := input0; (.bind (.guard (((«exec:match:typeFieldList:% %» typeFieldList') = true))) (fun (_ : Unit) => (match typeFieldList' with | .«% %» «exec:1» «exec:2» => (let typeFieldList : SpecTec.typeFieldList := «exec:1»; (let typeField : SpecTec.typeField := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.typeField), SpecTecCall.«$flatten_typeFieldList» typeFieldList⟩) (fun («exec:3» : (_root_.List SpecTec.typeField)) => (let «eval:0» : (_root_.List SpecTec.typeField) := «exec:3»; (.pure (((«eval:0» ++ ([typeField] : (_root_.List SpecTec.typeField))) : (_root_.List SpecTec.typeField))))))))) | _ => .unmatch))))


noncomputable def «$flatten_typeFieldList_clauses» (input0 : typeFieldList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_typeFieldList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_typeFieldList:clause:1»  input0)]


noncomputable def «$lift_aliasTypeIR:clause:0» (input0 : SpecTec.aliasTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let aliasTypeIR : SpecTec.aliasTypeIR := input0; (.bind (.guard (((«sub:aliasTypeIR:typedefTypeIR» aliasTypeIR) = true))) (fun (_ : Unit) => (match («$lift_aliasTypeIR:case_1:downcast:0» aliasTypeIR) with | some «exec:1» => (let «eval:0» : typedefTypeIR := «exec:1»; (match «eval:0» with | .TYPEDEF «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let _typeIR : typeIR := «exec:3»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:4» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:4»; (let typeName : SpecTec.typeName := «eval:1»; (.pure (((«cast:typeIdentifier:type» typeName) : type))))))))))) | none => .unmatch))))


noncomputable def «$lift_aliasTypeIR:clause:1» (input0 : SpecTec.aliasTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let aliasTypeIR : SpecTec.aliasTypeIR := input0; (.bind (.guard (((«sub:aliasTypeIR:newTypeIR» aliasTypeIR) = true))) (fun (_ : Unit) => (match («$lift_aliasTypeIR:case_2:downcast:0» aliasTypeIR) with | some «exec:1» => (let «eval:0» : newTypeIR := «exec:1»; (match «eval:0» with | .TYPE «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let _typeIR : typeIR := «exec:3»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:4» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:4»; (let typeName : SpecTec.typeName := «eval:1»; (.pure (((«cast:typeIdentifier:type» typeName) : type))))))))))) | none => .unmatch))))


noncomputable def «$lift_aliasTypeIR_clauses» (input0 : aliasTypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_aliasTypeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_aliasTypeIR:clause:1»  input0)]


noncomputable def «$flatten_annotationList:clause:0» (input0 : SpecTec.annotationList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let annotationList : SpecTec.annotationList := input0; (.bind (.guard (((«exec:match:annotationList:_EMPTY» annotationList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List annotation)) : (_root_.List annotation)))))))


noncomputable def «$flatten_annotationList:clause:1» (input0 : SpecTec.annotationList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let annotationList : SpecTec.annotationList := input0; (.bind (.guard (((«sub:annotationList:annotation» annotationList) = true))) (fun (_ : Unit) => (match («$flatten_annotationList:case_2:downcast:0» annotationList) with | some «exec:1» => (let «eval:0» : SpecTec.annotation := «exec:1»; (let annotation : SpecTec.annotation := «eval:0»; (.pure ((([annotation] : (_root_.List SpecTec.annotation)) : (_root_.List SpecTec.annotation)))))) | none => .unmatch))))


noncomputable def «$flatten_annotationList:clause:2» (input0 : SpecTec.annotationList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let annotationList : SpecTec.annotationList := input0; (.bind (.guard (((«sub:annotationList:annotationListNonEmpty» annotationList) = true))) (fun (_ : Unit) => (match («$flatten_annotationList:case_3:downcast:0» annotationList) with | some «exec:1» => (let «eval:0» : SpecTec.annotationListNonEmpty := «exec:1»; (let annotationListNonEmpty' : SpecTec.annotationListNonEmpty := «eval:0»; (.bind (.guard (((«exec:match:annotationListNonEmpty:% %» annotationListNonEmpty') = true))) (fun (_ : Unit) => (match annotationListNonEmpty' with | .«% %» «exec:2» «exec:3» => (let annotationListNonEmpty : SpecTec.annotationListNonEmpty := «exec:2»; (let annotation : SpecTec.annotation := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.annotation), SpecTecCall.«$flatten_annotationList» («cast:annotationListNonEmpty:annotationList» annotationListNonEmpty)⟩) (fun («exec:4» : (_root_.List SpecTec.annotation)) => (let «eval:1» : (_root_.List SpecTec.annotation) := «exec:4»; (.pure (((«eval:1» ++ ([annotation] : (_root_.List SpecTec.annotation))) : (_root_.List SpecTec.annotation))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$flatten_annotationList_clauses» (input0 : annotationList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_annotationList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_annotationList:clause:1»  input0), fun (_ : _root_.Unit) => («$flatten_annotationList:clause:2»  input0)]


noncomputable def «$optional_annotation_of_parameterIR':clause:0» (input0 : SpecTec.annotationList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let annotationList : SpecTec.annotationList := input0; (.bind (.call ⟨(_root_.List annotation), SpecTecCall.«$flatten_annotationList» annotationList⟩) (fun («exec:1» : (_root_.List annotation)) => (let «eval:0» : (_root_.List annotation) := «exec:1»; (let «annotation*» : (_root_.List annotation) := «eval:0»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$optional_annotation_of_parameterIR':case_1:iter:1» «annotation*»⟩) (fun («exec:2» : (_root_.List _root_.Bool)) => (let «b*» : (_root_.List _root_.Bool) := «exec:2»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$exists_» «b*»⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.pure ((«eval:3» : _root_.Bool))))))))))))))


noncomputable def «$optional_annotation_of_parameterIR'_clauses» (input0 : annotationList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$optional_annotation_of_parameterIR':clause:0»  input0)]


noncomputable def «$optional_annotation_of_parameterIR:clause:0» (input0 : SpecTec.parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parameterIR : SpecTec.parameterIR := input0; (.bind (.call ⟨SpecTec.annotationList, SpecTecCall.«$annotationList_of_parameterIR» parameterIR⟩) (fun («exec:1» : SpecTec.annotationList) => (let «eval:0» : SpecTec.annotationList := «exec:1»; (let annotationList : SpecTec.annotationList := «eval:0»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$optional_annotation_of_parameterIR'» annotationList⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.pure ((«eval:1» : _root_.Bool)))))))))))


noncomputable def «$optional_annotation_of_parameterIR_clauses» (input0 : parameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$optional_annotation_of_parameterIR:clause:0»  input0)]


noncomputable def «$is_optional_parameterIR:clause:0» (input0 : SpecTec.parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parameterIR : SpecTec.parameterIR := input0; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$optional_annotation_of_parameterIR» parameterIR⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((«eval:0» : _root_.Bool)))))))


noncomputable def «$is_optional_parameterIR_clauses» (input0 : parameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_optional_parameterIR:clause:0»  input0)]


noncomputable def «$match_overloaded_named:case_2:iter:5:clause:0» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_named:case_2:iter:5:clause:1» (V_T : Type) (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_optional_parameterIR» parameterIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:6» : _root_.Bool := «exec:3»; (let b_optional : _root_.Bool := «eval:6»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_named:case_2:iter:5» V_T «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((b_optional :: «tail:1») : (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$match_overloaded_named:case_2:iter:5_clauses» (V_T : Type) (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:5:clause:0» V_T input0), fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:5:clause:1» V_T input0)]


noncomputable def «$match_overloaded_named:case_2:iter:14:clause:0» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)

end SpecTec
