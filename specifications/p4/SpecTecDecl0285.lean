import SpecTecDecl0284

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Type_wf:clause:18» (input0 : bound) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:defaultTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («Type_wf:defaultTypeIR:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.defaultTypeIR := «exec:1»; (let defaultTypeIR : SpecTec.defaultTypeIR := «eval:0»; (.bind (.guard (((SpecTec.defaultTypeIR.DEFAULT) : SpecTec.defaultTypeIR) = defaultTypeIR)) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))) | none => .unmatch)))))


noncomputable def «Type_wf:clause:19» (input0 : bound) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:invalidHeaderTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («Type_wf:invalidHeaderTypeIR:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.invalidHeaderTypeIR := «exec:1»; (let invalidHeaderTypeIR : SpecTec.invalidHeaderTypeIR := «eval:0»; (.bind (.guard (((SpecTec.invalidHeaderTypeIR.HEADER_INVALID) : SpecTec.invalidHeaderTypeIR) = invalidHeaderTypeIR)) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))) | none => .unmatch)))))


noncomputable def «Type_wf:clause:20» (input0 : bound) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let typeIR' : typeIR := input1; (.bind (.guard (((«sub:typeIR:sequenceTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Type_wf:non-default:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : SpecTec.sequenceTypeIR := «exec:1»; (let sequenceTypeIR : SpecTec.sequenceTypeIR := «eval:0»; (let sequenceTypeIR' : SpecTec.sequenceTypeIR := sequenceTypeIR; (.bind (.guard (((«exec:match:sequenceTypeIR:SEQ `< % `>» sequenceTypeIR') = true))) (fun (_ : Unit) => (match sequenceTypeIR' with | .«SEQ `< % `>» «exec:2» => (let «typeIR*» : (_root_.List typeIR) := «exec:2»; (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:non-default:iter:1» B «typeIR*»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))) | _ => .unmatch)))))) | none => .unmatch)))))


noncomputable def «Type_wf:clause:21» (input0 : bound) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let typeIR' : typeIR := input1; (.bind (.guard (((«sub:typeIR:sequenceTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Type_wf:default:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : SpecTec.sequenceTypeIR := «exec:1»; (let sequenceTypeIR : SpecTec.sequenceTypeIR := «eval:0»; (let sequenceTypeIR' : SpecTec.sequenceTypeIR := sequenceTypeIR; (.bind (.guard (((«exec:match:sequenceTypeIR:SEQ `< % ',' '...' `>» sequenceTypeIR') = true))) (fun (_ : Unit) => (match sequenceTypeIR' with | .«SEQ `< % ',' '...' `>» «exec:2» => (let «typeIR*» : (_root_.List typeIR) := «exec:2»; (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:default:iter:1» B «typeIR*»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))) | _ => .unmatch)))))) | none => .unmatch)))))


noncomputable def «Type_wf:clause:22» (input0 : bound) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:recordTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («Type_wf:non-default_2:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.recordTypeIR := «exec:1»; (let recordTypeIR : SpecTec.recordTypeIR := «eval:0»; (let recordTypeIR' : SpecTec.recordTypeIR := recordTypeIR; (.bind (.guard (((«exec:match:recordTypeIR:RECORD `{ % `}» recordTypeIR') = true))) (fun (_ : Unit) => (match recordTypeIR' with | .«RECORD `{ % `}» «exec:2» => (let «eval:2» : (_root_.List fieldTypeIR) := «exec:2»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«Type_wf:non-default_2:pattern-iter:1» «eval:2»⟩) (fun («exec:3» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:3»).1; (let «nameIR_field*» : (_root_.List nameIR) := ((«exec:3»).2).1; (let «typeIR_field*» : (_root_.List SpecTec.typeIR) := ((«exec:3»).2).2; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$distinct_» nameIR «nameIR_field*»⟩) (fun («exec:4» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:4»; (.bind (.guard ((«eval:3» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:non-default_2:iter:4» B «typeIR_field*»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))))))) | _ => .unmatch)))))) | none => .unmatch)))))


noncomputable def «Type_wf:clause:23» (input0 : bound) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:recordTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («Type_wf:default_2:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.recordTypeIR := «exec:1»; (let recordTypeIR : SpecTec.recordTypeIR := «eval:0»; (let recordTypeIR' : SpecTec.recordTypeIR := recordTypeIR; (.bind (.guard (((«exec:match:recordTypeIR:RECORD `{ % ',' '...' `}» recordTypeIR') = true))) (fun (_ : Unit) => (match recordTypeIR' with | .«RECORD `{ % ',' '...' `}» «exec:2» => (let «eval:2» : (_root_.List fieldTypeIR) := «exec:2»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«Type_wf:default_2:pattern-iter:1» «eval:2»⟩) (fun («exec:3» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:3»).1; (let «nameIR_field*» : (_root_.List nameIR) := ((«exec:3»).2).1; (let «typeIR_field*» : (_root_.List SpecTec.typeIR) := ((«exec:3»).2).2; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$distinct_» nameIR «nameIR_field*»⟩) (fun («exec:4» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:4»; (.bind (.guard ((«eval:3» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:default_2:iter:4» B «typeIR_field*»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))))))) | _ => .unmatch)))))) | none => .unmatch)))))


noncomputable def «Type_wf:clause:24» (input0 : bound) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let typeIR' : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:setTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Type_wf:setTypeIR:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : setTypeIR := «exec:1»; (match «eval:0» with | .«SET `< % `>» «exec:2» => (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_set» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_wf B typeIR⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))))) | none => .unmatch)))))


noncomputable def «Type_wf:clause:25» (input0 : bound) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let typeIR : SpecTec.typeIR := input1; (let typeIR' : SpecTec.typeIR := typeIR; (.bind (.guard (((«sub:typeIR:tableMetadataEnumTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Type_wf:enum:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : tableMetadataEnumTypeIR := «exec:1»; (match «eval:0» with | .«TABLE_ENUM % `{ % `}» «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let «nameIR*» : (_root_.List nameIR) := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$distinct_» nameIR «nameIR*»⟩) (fun («exec:4» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:4»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | none => .unmatch))))))


noncomputable def «Type_wf:clause:26» (input0 : bound) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let typeIR : SpecTec.typeIR := input1; (let typeIR' : SpecTec.typeIR := typeIR; (.bind (.guard (((«sub:typeIR:tableMetadataStructTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Type_wf:struct:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : tableMetadataStructTypeIR := «exec:1»; (match «eval:0» with | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» «exec:2» «exec:3» «exec:4» «exec:5» => (let _typeId : typeId := «exec:2»; (let _boolTypeIR : boolTypeIR := «exec:3»; (let _boolTypeIR' : boolTypeIR := «exec:4»; (let tableMetadataEnumTypeIR : SpecTec.tableMetadataEnumTypeIR := «exec:5»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_wf B («cast:tableMetadataEnumTypeIR:typeIR» tableMetadataEnumTypeIR)⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))) | none => .unmatch))))))


noncomputable def Type_wf_clauses (input0 : bound) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:1»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:2»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:3»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:4»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:5»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:6»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:7»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:8»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:9»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:10»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:11»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:12»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:13»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:14»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:15»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:16»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:17»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:18»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:19»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:20»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:21»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:22»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:23»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:24»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:25»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:clause:26»  input0 input1)]


noncomputable def «Type_wf:tupleTypeIR:iter:3:clause:0» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «Type_wf:tupleTypeIR:iter:3:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_wf B typeIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:tupleTypeIR:iter:3» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «Type_wf:tupleTypeIR:iter:3_clauses» (input0 : bound) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:tupleTypeIR:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:tupleTypeIR:iter:3:clause:1»  input0 input1)]


noncomputable def «Type_wf:structTypeIR:iter:6:clause:0» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «Type_wf:structTypeIR:iter:6:clause:1» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_wf B typeIR_field⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:structTypeIR:iter:6» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «Type_wf:structTypeIR:iter:6_clauses» (input0 : bound) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:structTypeIR:iter:6:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:structTypeIR:iter:6:clause:1»  input0 input1)]


noncomputable def «Type_wf:headerTypeIR:iter:6:clause:0» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «Type_wf:headerTypeIR:iter:6:clause:1» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_wf B typeIR_field⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:headerTypeIR:iter:6» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «Type_wf:headerTypeIR:iter:6_clauses» (input0 : bound) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:headerTypeIR:iter:6:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:headerTypeIR:iter:6:clause:1»  input0 input1)]


noncomputable def «Type_wf:headerUnionTypeIR:iter:6:clause:0» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «Type_wf:headerUnionTypeIR:iter:6:clause:1» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_wf B typeIR_field⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:headerUnionTypeIR:iter:6» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «Type_wf:headerUnionTypeIR:iter:6_clauses» (input0 : bound) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:headerUnionTypeIR:iter:6:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:headerUnionTypeIR:iter:6:clause:1»  input0 input1)]


noncomputable def «Type_wf:externObjectTypeIR:iter:3:clause:0» (input0 : bound) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «Type_wf:externObjectTypeIR:iter:3:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externMethodTypeDefIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.CallableTypeDef_wf B («cast:externMethodTypeDefIR:callableTypeDefIR» externMethodTypeDefIR)⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:externObjectTypeIR:iter:3» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «Type_wf:externObjectTypeIR:iter:3_clauses» (input0 : bound) (input1 : (_root_.List externMethodTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:externObjectTypeIR:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:externObjectTypeIR:iter:3:clause:1»  input0 input1)]


noncomputable def «Type_wf:parserObjectTypeIR:iter:1:clause:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «Type_wf:parserObjectTypeIR:iter:1:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ParameterType_wf B parameterIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:parserObjectTypeIR:iter:1» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «Type_wf:parserObjectTypeIR:iter:1_clauses» (input0 : bound) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:parserObjectTypeIR:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:parserObjectTypeIR:iter:1:clause:1»  input0 input1)]


noncomputable def «Type_wf:controlObjectTypeIR:iter:1:clause:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «Type_wf:controlObjectTypeIR:iter:1:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ParameterType_wf B parameterIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:controlObjectTypeIR:iter:1» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «Type_wf:controlObjectTypeIR:iter:1_clauses» (input0 : bound) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:controlObjectTypeIR:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_wf:controlObjectTypeIR:iter:1:clause:1»  input0 input1)]


noncomputable def «Type_wf:packageObjectTypeIR:iter:1:clause:0» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))

end SpecTec
