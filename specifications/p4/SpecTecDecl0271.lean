import SpecTecDecl0270

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_typeDefIR_as_typeName:clause:9» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:parserObjectTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_10:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : parserObjectTypeDefIR := «exec:1»; (match «eval:0» with | .«PARSER % `< % ',' % `> `( % `)» «exec:2» «exec:3» «exec:4» «exec:5» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:4»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:5»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:6» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:6»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName))))))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:10» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:controlObjectTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_11:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : controlObjectTypeDefIR := «exec:1»; (match «eval:0» with | .«CONTROL % `< % ',' % `> `( % `)» «exec:2» «exec:3» «exec:4» «exec:5» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:4»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:5»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:6» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:6»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName))))))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:11» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:packageObjectTypeDefIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_12:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : packageObjectTypeDefIR := «exec:1»; (match «eval:0» with | .«PACKAGE % `< % ',' % `> `{ % `}» «exec:2» «exec:3» «exec:4» «exec:5» => (let typeId : SpecTec.typeId := «exec:2»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:3»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:4»; (let «_typeIR*» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:6» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:6»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName))))))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:12» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.guard (((«sub:typeDefIR:tableObjectTypeIR» typeDefIR) = true))) (fun (_ : Unit) => (match («$lift_typeDefIR_as_typeName:case_13:downcast:0» typeDefIR) with | some «exec:1» => (let «eval:0» : tableObjectTypeIR := «exec:1»; (match «eval:0» with | .«TABLE % `{ % `}» «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let _tableMetadataStructTypeIR : tableMetadataStructTypeIR := «exec:3»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:4» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:4»; (let typeName : SpecTec.typeName := «eval:1»; (.pure ((typeName : SpecTec.typeName))))))))))) | none => .unmatch))))


noncomputable def «$lift_typeDefIR_as_typeName:clause:13» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.call ⟨typeName, SpecTecCall.«$sink» typeName⟩) (fun («exec:1» : typeName) => (let «eval:0» : typeName := «exec:1»; (.pure ((«eval:0» : typeName)))))))


noncomputable def «$lift_typeDefIR_as_typeName_clauses» (input0 : typeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:4»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:5»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:6»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:7»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:8»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:9»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:10»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:11»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:12»  input0), fun (_ : _root_.Unit) => («$lift_typeDefIR_as_typeName:clause:13»  input0)]


noncomputable def «$cast_array:clause:0» (input0 : SpecTec.typeIR) (input1 : arrayValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (match input1 with | .«ARRAY `[ % `]» «exec:1» => (let «value*» : (_root_.List value) := «exec:1»; (.bind (.guard (((«sub:typeIR:arrayTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$cast_array:case_1:downcast:0» typeIR') with | some «exec:2» => (let «eval:0» : arrayTypeIR := «exec:2»; (match «eval:0» with | .«ARRAY % `[ % `]» «exec:3» «exec:4» => (let typeIR : SpecTec.typeIR := «exec:3»; (let n_size : _root_.Nat := «exec:4»; (.pure ((((value.«ARRAY `[ % `]» «value*») : value) : value))))))) | none => .unmatch))))))


noncomputable def «$cast_array_clauses» (input0 : typeIR) (input1 : arrayValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_array:clause:0»  input0 input1)]


noncomputable def «$is_concrete_extern_object':clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard ((¬ ((«sub:typeIR:externObjectTypeIR» typeIR) = true)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$is_concrete_extern_object':clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:externObjectTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$is_concrete_extern_object':case_2:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : externObjectTypeIR := «exec:1»; (match «eval:0» with | .«EXTERN % `< % `> %» «exec:2» «exec:3» «exec:4» => (let _typeId : typeId := «exec:2»; (let «_typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:3»; (match «exec:4» with | .«`{ % `}» «exec:5» => (let «eval:2» : (_root_.List (pair callableId externMethodTypeDefIR)) := «exec:5»; (.bind (.call ⟨((_root_.List callableId) × (_root_.List externMethodTypeDefIR)), SpecTecCall.«$is_concrete_extern_object':case_2:pattern-iter:1» «eval:2»⟩) (fun («exec:6» : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))) => (let «_callableId*» : (_root_.List callableId) := («exec:6»).1; (let «externMethodTypeDefIR*» : (_root_.List externMethodTypeDefIR) := («exec:6»).2; (.bind (.call ⟨_root_.Unit, SpecTecCall.«$is_concrete_extern_object':case_2:iter:3» «externMethodTypeDefIR*»⟩) (fun («exec:7» : _root_.Unit) => (.pure ((true : _root_.Bool))))))))))))))) | none => .unmatch))))


noncomputable def «$is_concrete_extern_object':clause:2» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_concrete_extern_object'_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_concrete_extern_object':clause:0»  input0), fun (_ : _root_.Unit) => («$is_concrete_extern_object':clause:1»  input0), fun (_ : _root_.Unit) => («$is_concrete_extern_object':clause:2»  input0)]


noncomputable def «$cast_header_stack:clause:0» (input0 : SpecTec.typeIR) (input1 : headerStackValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (match input1 with | .«HEADER_STACK `[ % `( % `) `]» «exec:1» «exec:2» => (let «value*» : (_root_.List value) := «exec:1»; (let n_idx : _root_.Nat := «exec:2»; (.bind (.guard (((«sub:typeIR:headerStackTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$cast_header_stack:case_1:downcast:0» typeIR') with | some «exec:3» => (let «eval:0» : headerStackTypeIR := «exec:3»; (match «eval:0» with | .«HEADER_STACK % `[ % `]» «exec:4» «exec:5» => (let typeIR : SpecTec.typeIR := «exec:4»; (let n_size : _root_.Nat := «exec:5»; (.pure ((((value.«HEADER_STACK `[ % `( % `) `]» «value*» n_idx) : value) : value))))))) | none => .unmatch)))))))


noncomputable def «$cast_header_stack_clauses» (input0 : typeIR) (input1 : headerStackValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_header_stack:clause:0»  input0 input1)]


noncomputable def «$cast_header:clause:0» (input0 : SpecTec.typeIR) (input1 : headerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (match input1 with | .«HEADER % `{ % ';' % `}» «exec:1» «exec:2» «exec:3» => (let typeId' : SpecTec.typeId := «exec:1»; (let b : _root_.Bool := «exec:2»; (let «eval:1» : (_root_.List fieldValue) := «exec:3»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_header:case_1:pattern-iter:0» «eval:1»⟩) (fun («exec:4» : ((_root_.List nameIR) × (_root_.List value))) => (let «nameIR_field*» : (_root_.List nameIR) := («exec:4»).1; (let «value_field*» : (_root_.List value) := («exec:4»).2; (.bind (.guard (((«sub:typeIR:headerTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$cast_header:case_1:downcast:2» typeIR) with | some «exec:5» => (let «eval:2» : headerTypeIR := «exec:5»; (match «eval:2» with | .«HEADER % `< % `> `{ % `}» «exec:6» «exec:7» «exec:8» => (let typeId : SpecTec.typeId := «exec:6»; (let «_typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:7»; (let «_fieldTypeIR*» : (_root_.List fieldTypeIR) := «exec:8»; (.bind (.guard (typeId' = typeId)) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_header:case_1:iter:3» «nameIR_field*» «value_field*»⟩) (fun («exec:9» : (_root_.List fieldValue)) => (let «eval:4» : (_root_.List fieldValue) := «exec:9»; (.pure ((((value.«HEADER % `{ % ';' % `}» typeId b «eval:4») : value) : value))))))))))))) | none => .unmatch))))))))))))


noncomputable def «$cast_header_clauses» (input0 : typeIR) (input1 : headerValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_header:clause:0»  input0 input1)]


noncomputable def «$cast_header_union:clause:0» (input0 : SpecTec.typeIR) (input1 : headerUnionValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (match input1 with | .«HEADER_UNION % `{ % `}» «exec:1» «exec:2» => (let typeId' : SpecTec.typeId := «exec:1»; (let «eval:1» : (_root_.List fieldValue) := «exec:2»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_header_union:case_1:pattern-iter:0» «eval:1»⟩) (fun («exec:3» : ((_root_.List nameIR) × (_root_.List value))) => (let «nameIR_field*» : (_root_.List nameIR) := («exec:3»).1; (let «value_field*» : (_root_.List value) := («exec:3»).2; (.bind (.guard (((«sub:typeIR:headerUnionTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$cast_header_union:case_1:downcast:2» typeIR) with | some «exec:4» => (let «eval:2» : headerUnionTypeIR := «exec:4»; (match «eval:2» with | .«HEADER_UNION % `< % `> `{ % `}» «exec:5» «exec:6» «exec:7» => (let typeId : SpecTec.typeId := «exec:5»; (let «_typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:6»; (let «_fieldTypeIR*» : (_root_.List fieldTypeIR) := «exec:7»; (.bind (.guard (typeId' = typeId)) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_header_union:case_1:iter:3» «nameIR_field*» «value_field*»⟩) (fun («exec:8» : (_root_.List fieldValue)) => (let «eval:4» : (_root_.List fieldValue) := «exec:8»; (.pure ((((value.«HEADER_UNION % `{ % `}» typeId «eval:4») : value) : value))))))))))))) | none => .unmatch)))))))))))


noncomputable def «$cast_header_union_clauses» (input0 : typeIR) (input1 : headerUnionValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_header_union:clause:0»  input0 input1)]


noncomputable def «$cast_string:clause:0» (input0 : SpecTec.typeIR) (input1 : SpecTec.stringValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let stringValue : SpecTec.stringValue := input1; (.bind (.guard (((«sub:typeIR:stringTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$cast_string:case_1:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.stringTypeIR := «exec:1»; (let stringTypeIR : SpecTec.stringTypeIR := «eval:0»; (.bind (.guard (((SpecTec.stringTypeIR.STRING) : SpecTec.stringTypeIR) = stringTypeIR)) (fun (_ : Unit) => (.pure (((«cast:stringLiteral:value» stringValue) : value))))))) | none => .unmatch)))))


noncomputable def «$cast_string_clauses» (input0 : typeIR) (input1 : stringValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_string:clause:0»  input0 input1)]


noncomputable def «$cast_struct:clause:0» (input0 : SpecTec.typeIR) (input1 : structValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (match input1 with | .«STRUCT % `{ % `}» «exec:1» «exec:2» => (let typeId' : SpecTec.typeId := «exec:1»; (let «eval:1» : (_root_.List fieldValue) := «exec:2»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_struct:case_1:pattern-iter:0» «eval:1»⟩) (fun («exec:3» : ((_root_.List nameIR) × (_root_.List value))) => (let «nameIR_field*» : (_root_.List nameIR) := («exec:3»).1; (let «value_field*» : (_root_.List value) := («exec:3»).2; (.bind (.guard (((«sub:typeIR:structTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$cast_struct:case_1:downcast:2» typeIR) with | some «exec:4» => (let «eval:2» : structTypeIR := «exec:4»; (match «eval:2» with | .«STRUCT % `< % `> `{ % `}» «exec:5» «exec:6» «exec:7» => (let typeId : SpecTec.typeId := «exec:5»; (let «_typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:6»; (let «_fieldTypeIR*» : (_root_.List fieldTypeIR) := «exec:7»; (.bind (.guard (typeId' = typeId)) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_struct:case_1:iter:3» «nameIR_field*» «value_field*»⟩) (fun («exec:8» : (_root_.List fieldValue)) => (let «eval:4» : (_root_.List fieldValue) := «exec:8»; (.pure ((((value.«STRUCT % `{ % `}» typeId «eval:4») : value) : value))))))))))))) | none => .unmatch)))))))))))


noncomputable def «$cast_struct_clauses» (input0 : typeIR) (input1 : structValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_struct:clause:0»  input0 input1)]


noncomputable def «$unroll_typeIR:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:typedefTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$unroll_typeIR:case_1:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : typedefTypeIR := «exec:1»; (match «eval:0» with | .TYPEDEF «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$unroll_typeIR» typeIR⟩) (fun («exec:4» : SpecTec.typeIR) => (let «eval:1» : SpecTec.typeIR := «exec:4»; (.pure ((«eval:1» : SpecTec.typeIR)))))))))) | none => .unmatch))))


noncomputable def «$unroll_typeIR:clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.pure ((typeIR : SpecTec.typeIR))))


noncomputable def «$unroll_typeIR_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unroll_typeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$unroll_typeIR:clause:1»  input0)]


noncomputable def «$unroll_aliasTypeIR:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:newTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$unroll_aliasTypeIR:case_1:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : newTypeIR := «exec:1»; (match «eval:0» with | .TYPE «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$unroll_aliasTypeIR» typeIR⟩) (fun («exec:4» : SpecTec.typeIR) => (let «eval:1» : SpecTec.typeIR := «exec:4»; (.pure ((«eval:1» : SpecTec.typeIR)))))))))) | none => .unmatch))))


noncomputable def «$unroll_aliasTypeIR:clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:typedefTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$unroll_aliasTypeIR:case_2:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : typedefTypeIR := «exec:1»; (match «eval:0» with | .TYPEDEF «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$unroll_aliasTypeIR» typeIR⟩) (fun («exec:4» : SpecTec.typeIR) => (let «eval:1» : SpecTec.typeIR := «exec:4»; (.pure ((«eval:1» : SpecTec.typeIR)))))))))) | none => .unmatch))))


noncomputable def «$unroll_aliasTypeIR:clause:2» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.pure ((typeIR : SpecTec.typeIR))))


noncomputable def «$unroll_aliasTypeIR_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unroll_aliasTypeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$unroll_aliasTypeIR:clause:1»  input0), fun (_ : _root_.Unit) => («$unroll_aliasTypeIR:clause:2»  input0)]


noncomputable def «$free_typeIR:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:baseTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$free_typeIR:case_1:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.baseTypeIR := «exec:1»; (let baseTypeIR : SpecTec.baseTypeIR := «eval:0»; (.pure ((((set.«`{ % `}» ([] : (_root_.List typeId))) : (set typeId)) : bound))))) | none => .unmatch))))


noncomputable def «$free_typeIR:clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:nameTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$free_typeIR:case_2:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : nameTypeIR := «exec:1»; (match «eval:0» with | ._NAME «exec:2» => (let typeId : SpecTec.typeId := «exec:2»; (.pure ((((set.«`{ % `}» ([typeId] : (_root_.List SpecTec.typeId))) : (set SpecTec.typeId)) : bound)))))) | none => .unmatch))))


noncomputable def «$free_typeIR:clause:2» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:typedefTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$free_typeIR:case_3:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : typedefTypeIR := «exec:1»; (match «eval:0» with | .TYPEDEF «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:4» : bound) => (let «eval:1» : bound := «exec:4»; (.pure ((«eval:1» : bound)))))))))) | none => .unmatch))))

end SpecTec
