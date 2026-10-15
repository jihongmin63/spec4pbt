import SpecTecDecl0269

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$typeParameterListIR_of_typeDefIR_clauses» (input0 : typeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeParameterListIR_of_typeDefIR:clause:0»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_typeDefIR:clause:1»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_typeDefIR:clause:2»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_typeDefIR:clause:3»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_typeDefIR:clause:4»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_typeDefIR:clause:5»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_typeDefIR:clause:6»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_typeDefIR:clause:7»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_typeDefIR:clause:8»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_typeDefIR:clause:9»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_typeDefIR:clause:10»  input0)]


noncomputable def «$is_monomorphic_typeDefIR:clause:0» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:nameTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$is_monomorphic_typeDefIR:case_1:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : SpecTec.nameTypeDefIR := «exec:1»; (let nameTypeDefIR : SpecTec.nameTypeDefIR := «eval:0»; (.pure ((true : _root_.Bool))))) | none => .unmatch))))


noncomputable def «$is_monomorphic_typeDefIR:clause:1» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:aliasTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$is_monomorphic_typeDefIR:case_2:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : SpecTec.aliasTypeDefIR := «exec:1»; (let aliasTypeDefIR : SpecTec.aliasTypeDefIR := «eval:0»; (.pure ((true : _root_.Bool))))) | none => .unmatch))))


noncomputable def «$is_monomorphic_typeDefIR:clause:2» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:enumTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$is_monomorphic_typeDefIR:case_3:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : SpecTec.enumTypeDefIR := «exec:1»; (let enumTypeDefIR : SpecTec.enumTypeDefIR := «eval:0»; (.pure ((true : _root_.Bool))))) | none => .unmatch))))


noncomputable def «$is_monomorphic_typeDefIR:clause:3» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:tableObjectTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$is_monomorphic_typeDefIR:case_4:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : SpecTec.tableObjectTypeDefIR := «exec:1»; (let tableObjectTypeDefIR : SpecTec.tableObjectTypeDefIR := «eval:0»; (.pure ((true : _root_.Bool))))) | none => .unmatch))))


noncomputable def «$is_monomorphic_typeDefIR:clause:4» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_monomorphic_typeDefIR_clauses» (input0 : typeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_monomorphic_typeDefIR:clause:0»  input0), fun (_ : _root_.Unit) => («$is_monomorphic_typeDefIR:clause:1»  input0), fun (_ : _root_.Unit) => («$is_monomorphic_typeDefIR:clause:2»  input0), fun (_ : _root_.Unit) => («$is_monomorphic_typeDefIR:clause:3»  input0), fun (_ : _root_.Unit) => («$is_monomorphic_typeDefIR:clause:4»  input0)]


noncomputable def «$is_polymorphic_typeDefIR:clause:0» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_monomorphic_typeDefIR» typeDefIR⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure (((!«eval:0») : _root_.Bool)))))))


noncomputable def «$is_polymorphic_typeDefIR_clauses» (input0 : typeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_polymorphic_typeDefIR:clause:0»  input0)]


noncomputable def «$typeId_of_typeDefIR:clause:0» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:nameTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_1:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : nameTypeIR := «exec:1»; (match «eval:0» with | ._NAME «exec:2» => (let typeId : SpecTec.typeId := «exec:2»; (.pure ((typeId : SpecTec.typeId)))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:1» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:typedefTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_2:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : typedefTypeIR := «exec:1»; (match «eval:0» with | .TYPEDEF «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let _typeIR : typeIR := «exec:3»; (.pure ((typeId : SpecTec.typeId))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:2» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:newTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_3:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : newTypeIR := «exec:1»; (match «eval:0» with | .TYPE «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let _typeIR : typeIR := «exec:3»; (.pure ((typeId : SpecTec.typeId))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:3» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:structTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_4:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : structTypeDefIR := «exec:1»; (match «eval:0» with | .«STRUCT % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_fieldTypeIR*» : (_root_.List fieldTypeIR) := «exec:4»; (.pure ((typeId : SpecTec.typeId)))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:4» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:headerTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_5:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : headerTypeDefIR := «exec:1»; (match «eval:0» with | .«HEADER % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_fieldTypeIR*» : (_root_.List fieldTypeIR) := «exec:4»; (.pure ((typeId : SpecTec.typeId)))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:5» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:headerUnionTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_6:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : headerUnionTypeDefIR := «exec:1»; (match «eval:0» with | .«HEADER_UNION % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_fieldTypeIR*» : (_root_.List fieldTypeIR) := «exec:4»; (.pure ((typeId : SpecTec.typeId)))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:6» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:simpleEnumTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_7:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : simpleEnumTypeIR := «exec:1»; (match «eval:0» with | .«ENUM % `{ % `}» «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let «_nameIR*» : (_root_.List nameIR) := «exec:3»; (.pure ((typeId : SpecTec.typeId))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:7» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:serializableEnumTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_8:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : serializableEnumTypeIR := «exec:1»; (match «eval:0» with | .«ENUM % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let _typeIR : typeIR := «exec:3»; (let «_valueFieldIR*» : (_root_.List valueFieldIR) := «exec:4»; (.pure ((typeId : SpecTec.typeId)))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:8» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:externObjectTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_9:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : externObjectTypeDefIR := «exec:1»; (match «eval:0» with | .«EXTERN % `< % ',' % `> %» «exec:2» «exec:3» «exec:4» «exec:5» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:4»; (match «exec:5» with | .«`{ % `}» «exec:6» => (let «_pair<callableId, externMethodTypeDefIR>*» : (_root_.List (pair callableId externMethodTypeDefIR)) := «exec:6»; (.pure ((typeId : SpecTec.typeId)))))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:9» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:parserObjectTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_10:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : parserObjectTypeDefIR := «exec:1»; (match «eval:0» with | .«PARSER % `< % ',' % `> `( % `)» «exec:2» «exec:3» «exec:4» «exec:5» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:4»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:5»; (.pure ((typeId : SpecTec.typeId))))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:10» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:controlObjectTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_11:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : controlObjectTypeDefIR := «exec:1»; (match «eval:0» with | .«CONTROL % `< % ',' % `> `( % `)» «exec:2» «exec:3» «exec:4» «exec:5» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:4»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:5»; (.pure ((typeId : SpecTec.typeId))))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:11» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:packageObjectTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_12:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : packageObjectTypeDefIR := «exec:1»; (match «eval:0» with | .«PACKAGE % `< % ',' % `> `{ % `}» «exec:2» «exec:3» «exec:4» «exec:5» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:4»; (let «_typeIR*» : (_root_.List typeIR) := «exec:5»; (.pure ((typeId : SpecTec.typeId))))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR:clause:12» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:tableObjectTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$typeId_of_typeDefIR:case_13:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : tableObjectTypeIR := «exec:1»; (match «eval:0» with | .«TABLE % `{ % `}» «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let _tableMetadataStructTypeIR : tableMetadataStructTypeIR := «exec:3»; (.pure ((typeId : SpecTec.typeId))))))) | none => .unmatch))))


noncomputable def «$typeId_of_typeDefIR_clauses» (input0 : typeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:0»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:1»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:2»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:3»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:4»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:5»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:6»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:7»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:8»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:9»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:10»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:11»  input0), fun (_ : _root_.Unit) => («$typeId_of_typeDefIR:clause:12»  input0)]


noncomputable def «$lift_typeDefIR_as_typeName:clause:0» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:nameTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_1:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : nameTypeIR := «exec:1»; (match «eval:0» with | ._NAME «exec:2» => (let typeId : SpecTec.typeId := «exec:2»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:3» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:3»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName)))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:1» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:typedefTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_2:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : typedefTypeIR := «exec:1»; (match «eval:0» with | .TYPEDEF «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let _typeIR : typeIR := «exec:3»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:4» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:4»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName))))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:2» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:newTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_3:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : newTypeIR := «exec:1»; (match «eval:0» with | .TYPE «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let _typeIR : typeIR := «exec:3»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:4» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:4»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName))))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:3» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:structTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_4:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : structTypeDefIR := «exec:1»; (match «eval:0» with | .«STRUCT % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_fieldTypeIR*» : (_root_.List fieldTypeIR) := «exec:4»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:5» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:5»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName)))))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:4» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:headerTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_5:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : headerTypeDefIR := «exec:1»; (match «eval:0» with | .«HEADER % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_fieldTypeIR*» : (_root_.List fieldTypeIR) := «exec:4»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:5» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:5»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName)))))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:5» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:headerUnionTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_6:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : headerUnionTypeDefIR := «exec:1»; (match «eval:0» with | .«HEADER_UNION % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_fieldTypeIR*» : (_root_.List fieldTypeIR) := «exec:4»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:5» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:5»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName)))))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:6» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:simpleEnumTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_7:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : simpleEnumTypeIR := «exec:1»; (match «eval:0» with | .«ENUM % `{ % `}» «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let «_nameIR*» : (_root_.List nameIR) := «exec:3»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:4» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:4»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName))))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:7» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:serializableEnumTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_8:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : serializableEnumTypeIR := «exec:1»; (match «eval:0» with | .«ENUM % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let _typeIR : typeIR := «exec:3»; (let «_valueFieldIR*» : (_root_.List valueFieldIR) := «exec:4»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:5» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:5»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName)))))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:8» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:externObjectTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_9:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : externObjectTypeDefIR := «exec:1»; (match «eval:0» with | .«EXTERN % `< % ',' % `> %» «exec:2» «exec:3» «exec:4» «exec:5» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:4»; (let _externMethodTypeDefEnv : externMethodTypeDefEnv := «exec:5»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:6» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:6»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName))))))))))))) | none => .unmatch))))

end SpecTec
