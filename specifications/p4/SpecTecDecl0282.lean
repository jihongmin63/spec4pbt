import SpecTecDecl0281

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Type_alpha:clause:21» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let typeIR' : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:sequenceTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («Type_alpha:non-default:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.sequenceTypeIR := «exec:1»; (let sequenceTypeIR : SpecTec.sequenceTypeIR := «eval:0»; (.bind (.guard (((«sub:typeIR:sequenceTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Type_alpha:non-default:downcast:1» typeIR') with | some «exec:2» => (let «eval:1» : SpecTec.sequenceTypeIR := «exec:2»; (let sequenceTypeIR' : SpecTec.sequenceTypeIR := «eval:1»; (let sequenceTypeIR'' : SpecTec.sequenceTypeIR := sequenceTypeIR; (.bind (.guard (((«exec:match:sequenceTypeIR:SEQ `< % `>» sequenceTypeIR'') = true))) (fun (_ : Unit) => (match sequenceTypeIR'' with | .«SEQ `< % `>» «exec:3» => (let «typeIR_a*» : (_root_.List SpecTec.typeIR) := «exec:3»; (let sequenceTypeIR''' : SpecTec.sequenceTypeIR := sequenceTypeIR'; (.bind (.guard (((«exec:match:sequenceTypeIR:SEQ `< % `>» sequenceTypeIR''') = true))) (fun (_ : Unit) => (match sequenceTypeIR''' with | .«SEQ `< % `>» «exec:4» => (let «typeIR_b*» : (_root_.List SpecTec.typeIR) := «exec:4»; (.bind (.guard ((_root_.List.length «typeIR_b*») = (_root_.List.length «typeIR_a*»))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:non-default:iter:2» «typeIR_a*» «typeIR_b*»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))) | _ => .unmatch))))) | _ => .unmatch)))))) | none => .unmatch))))) | none => .unmatch)))))


noncomputable def «Type_alpha:clause:22» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let typeIR' : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:sequenceTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («Type_alpha:default:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.sequenceTypeIR := «exec:1»; (let sequenceTypeIR : SpecTec.sequenceTypeIR := «eval:0»; (.bind (.guard (((«sub:typeIR:sequenceTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Type_alpha:default:downcast:1» typeIR') with | some «exec:2» => (let «eval:1» : SpecTec.sequenceTypeIR := «exec:2»; (let sequenceTypeIR' : SpecTec.sequenceTypeIR := «eval:1»; (let sequenceTypeIR'' : SpecTec.sequenceTypeIR := sequenceTypeIR; (.bind (.guard (((«exec:match:sequenceTypeIR:SEQ `< % ',' '...' `>» sequenceTypeIR'') = true))) (fun (_ : Unit) => (match sequenceTypeIR'' with | .«SEQ `< % ',' '...' `>» «exec:3» => (let «typeIR_a*» : (_root_.List SpecTec.typeIR) := «exec:3»; (let sequenceTypeIR''' : SpecTec.sequenceTypeIR := sequenceTypeIR'; (.bind (.guard (((«exec:match:sequenceTypeIR:SEQ `< % ',' '...' `>» sequenceTypeIR''') = true))) (fun (_ : Unit) => (match sequenceTypeIR''' with | .«SEQ `< % ',' '...' `>» «exec:4» => (let «typeIR_b*» : (_root_.List SpecTec.typeIR) := «exec:4»; (.bind (.guard ((_root_.List.length «typeIR_b*») = (_root_.List.length «typeIR_a*»))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:default:iter:2» «typeIR_a*» «typeIR_b*»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))) | _ => .unmatch))))) | _ => .unmatch)))))) | none => .unmatch))))) | none => .unmatch)))))


noncomputable def «Type_alpha:clause:23» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let typeIR' : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:recordTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («Type_alpha:non-default_2:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.recordTypeIR := «exec:1»; (let recordTypeIR : SpecTec.recordTypeIR := «eval:0»; (.bind (.guard (((«sub:typeIR:recordTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Type_alpha:non-default_2:downcast:1» typeIR') with | some «exec:2» => (let «eval:1» : SpecTec.recordTypeIR := «exec:2»; (let recordTypeIR' : SpecTec.recordTypeIR := «eval:1»; (let recordTypeIR'' : SpecTec.recordTypeIR := recordTypeIR; (.bind (.guard (((«exec:match:recordTypeIR:RECORD `{ % `}» recordTypeIR'') = true))) (fun (_ : Unit) => (match recordTypeIR'' with | .«RECORD `{ % `}» «exec:3» => (let «eval:3» : (_root_.List fieldTypeIR) := «exec:3»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«Type_alpha:non-default_2:pattern-iter:2» «eval:3»⟩) (fun («exec:4» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «annotationList*» : (_root_.List annotationList) := («exec:4»).1; (let «nameIR_field*» : (_root_.List nameIR) := ((«exec:4»).2).1; (let «typeIR_field_a*» : (_root_.List SpecTec.typeIR) := ((«exec:4»).2).2; (let recordTypeIR''' : SpecTec.recordTypeIR := recordTypeIR'; (.bind (.guard (((«exec:match:recordTypeIR:RECORD `{ % `}» recordTypeIR''') = true))) (fun (_ : Unit) => (match recordTypeIR''' with | .«RECORD `{ % `}» «exec:5» => (let «eval:5» : (_root_.List fieldTypeIR) := «exec:5»; (.bind (.call ⟨((_root_.List SpecTec.typeIR) × ((_root_.List annotationList) × (_root_.List nameIR))), SpecTecCall.«Type_alpha:non-default_2:pattern-iter:4» «eval:5»⟩) (fun («exec:6» : ((_root_.List SpecTec.typeIR) × ((_root_.List annotationList) × (_root_.List nameIR)))) => (let «typeIR_field_b*» : (_root_.List SpecTec.typeIR) := («exec:6»).1; (let «annotationList'*» : (_root_.List annotationList) := ((«exec:6»).2).1; (let «nameIR*» : (_root_.List nameIR) := ((«exec:6»).2).2; (.bind (.guard ((_root_.List.length «annotationList'*») = (_root_.List.length «annotationList*»))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:non-default_2:iter:6» «annotationList*» «annotationList'*»⟩) (fun («exec:7» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:non-default_2:iter:7» «nameIR_field*» «nameIR*»⟩) (fun («exec:8» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:non-default_2:iter:8» «typeIR_field_a*» «typeIR_field_b*»⟩) (fun («exec:9» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))))))))) | _ => .unmatch)))))))))) | _ => .unmatch)))))) | none => .unmatch))))) | none => .unmatch)))))


noncomputable def «Type_alpha:clause:24» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let typeIR' : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:recordTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («Type_alpha:default_2:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.recordTypeIR := «exec:1»; (let recordTypeIR : SpecTec.recordTypeIR := «eval:0»; (.bind (.guard (((«sub:typeIR:recordTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Type_alpha:default_2:downcast:1» typeIR') with | some «exec:2» => (let «eval:1» : SpecTec.recordTypeIR := «exec:2»; (let recordTypeIR' : SpecTec.recordTypeIR := «eval:1»; (let recordTypeIR'' : SpecTec.recordTypeIR := recordTypeIR; (.bind (.guard (((«exec:match:recordTypeIR:RECORD `{ % ',' '...' `}» recordTypeIR'') = true))) (fun (_ : Unit) => (match recordTypeIR'' with | .«RECORD `{ % ',' '...' `}» «exec:3» => (let «eval:3» : (_root_.List fieldTypeIR) := «exec:3»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«Type_alpha:default_2:pattern-iter:2» «eval:3»⟩) (fun («exec:4» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «annotationList*» : (_root_.List annotationList) := («exec:4»).1; (let «nameIR_field*» : (_root_.List nameIR) := ((«exec:4»).2).1; (let «typeIR_field_a*» : (_root_.List SpecTec.typeIR) := ((«exec:4»).2).2; (let recordTypeIR''' : SpecTec.recordTypeIR := recordTypeIR'; (.bind (.guard (((«exec:match:recordTypeIR:RECORD `{ % ',' '...' `}» recordTypeIR''') = true))) (fun (_ : Unit) => (match recordTypeIR''' with | .«RECORD `{ % ',' '...' `}» «exec:5» => (let «eval:5» : (_root_.List fieldTypeIR) := «exec:5»; (.bind (.call ⟨((_root_.List SpecTec.typeIR) × ((_root_.List annotationList) × (_root_.List nameIR))), SpecTecCall.«Type_alpha:default_2:pattern-iter:4» «eval:5»⟩) (fun («exec:6» : ((_root_.List SpecTec.typeIR) × ((_root_.List annotationList) × (_root_.List nameIR)))) => (let «typeIR_field_b*» : (_root_.List SpecTec.typeIR) := («exec:6»).1; (let «annotationList'*» : (_root_.List annotationList) := ((«exec:6»).2).1; (let «nameIR*» : (_root_.List nameIR) := ((«exec:6»).2).2; (.bind (.guard ((_root_.List.length «annotationList'*») = (_root_.List.length «annotationList*»))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:default_2:iter:6» «annotationList*» «annotationList'*»⟩) (fun («exec:7» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:default_2:iter:7» «nameIR_field*» «nameIR*»⟩) (fun («exec:8» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:default_2:iter:8» «typeIR_field_a*» «typeIR_field_b*»⟩) (fun («exec:9» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))))))))) | _ => .unmatch)))))))))) | _ => .unmatch)))))) | none => .unmatch))))) | none => .unmatch)))))


noncomputable def «Type_alpha:clause:25» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let typeIR' : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:setTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («Type_alpha:setTypeIR:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : setTypeIR := «exec:1»; (match «eval:0» with | .«SET `< % `>» «exec:2» => (let typeIR_a : SpecTec.typeIR := «exec:2»; (.bind (.guard (((«sub:typeIR:setTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Type_alpha:setTypeIR:downcast:1» typeIR') with | some «exec:3» => (let «eval:1» : setTypeIR := «exec:3»; (match «eval:1» with | .«SET `< % `>» «exec:4» => (let typeIR_b : SpecTec.typeIR := «exec:4»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_alpha typeIR_a typeIR_b⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))) | none => .unmatch)))))) | none => .unmatch)))))


noncomputable def «Type_alpha:clause:26» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let typeIR' : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:tableMetadataTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («Type_alpha:tableMetadataTypeIR:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.tableMetadataTypeIR := «exec:1»; (let tableMetadataTypeIR : SpecTec.tableMetadataTypeIR := «eval:0»; (.bind (.guard (((«sub:typeIR:tableMetadataTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («Type_alpha:tableMetadataTypeIR:downcast:1» typeIR') with | some «exec:2» => (let «eval:1» : SpecTec.tableMetadataTypeIR := «exec:2»; (let tableMetadataTypeIR' : SpecTec.tableMetadataTypeIR := «eval:1»; (.bind (.guard (tableMetadataTypeIR' = tableMetadataTypeIR)) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))) | none => .unmatch))))) | none => .unmatch)))))


noncomputable def Type_alpha_clauses (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:1»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:2»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:3»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:4»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:5»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:6»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:7»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:8»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:9»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:10»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:11»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:12»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:13»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:14»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:15»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:16»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:17»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:18»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:19»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:20»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:21»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:22»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:23»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:24»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:25»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:clause:26»  input0 input1)]


noncomputable def «Type_alpha:tupleTypeIR:iter:2:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:tupleTypeIR:iter:2:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_b : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_alpha typeIR_a typeIR_b⟩) (fun («exec:5» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:tupleTypeIR:iter:2» «tail:0» «tail:1»⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:tupleTypeIR:iter:2_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:tupleTypeIR:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:tupleTypeIR:iter:2:clause:1»  input0 input1)]


noncomputable def «Type_alpha:structTypeIR:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:structTypeIR:iter:2:clause:1» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR_a : typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeArgumentIR_b : typeArgumentIR := «exec:4»; (let «tail:1» : (_root_.List typeArgumentIR) := «exec:3»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_alpha typeArgumentIR_a typeArgumentIR_b⟩) (fun («exec:5» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:structTypeIR:iter:2» «tail:0» «tail:1»⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:structTypeIR:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:structTypeIR:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:structTypeIR:iter:2:clause:1»  input0 input1)]


noncomputable def «Type_alpha:headerTypeIR:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:headerTypeIR:iter:2:clause:1» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR_a : typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeArgumentIR_b : typeArgumentIR := «exec:4»; (let «tail:1» : (_root_.List typeArgumentIR) := «exec:3»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_alpha typeArgumentIR_a typeArgumentIR_b⟩) (fun («exec:5» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:headerTypeIR:iter:2» «tail:0» «tail:1»⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:headerTypeIR:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:headerTypeIR:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:headerTypeIR:iter:2:clause:1»  input0 input1)]


noncomputable def «Type_alpha:headerUnionTypeIR:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:headerUnionTypeIR:iter:2:clause:1» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR_a : typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeArgumentIR_b : typeArgumentIR := «exec:4»; (let «tail:1» : (_root_.List typeArgumentIR) := «exec:3»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_alpha typeArgumentIR_a typeArgumentIR_b⟩) (fun («exec:5» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:headerUnionTypeIR:iter:2» «tail:0» «tail:1»⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:headerUnionTypeIR:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:headerUnionTypeIR:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:headerUnionTypeIR:iter:2:clause:1»  input0 input1)]


noncomputable def «Type_alpha:externObjectTypeIR:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:externObjectTypeIR:iter:2:clause:1» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR_a : typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeArgumentIR_b : typeArgumentIR := «exec:4»; (let «tail:1» : (_root_.List typeArgumentIR) := «exec:3»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_alpha typeArgumentIR_a typeArgumentIR_b⟩) (fun («exec:5» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:externObjectTypeIR:iter:2» «tail:0» «tail:1»⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:externObjectTypeIR:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:externObjectTypeIR:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:externObjectTypeIR:iter:2:clause:1»  input0 input1)]


noncomputable def «Type_alpha:parserObjectTypeIR:iter:2:clause:0» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:parserObjectTypeIR:iter:2:clause:1» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_a : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let parameterIR_b : parameterIR := «exec:4»; (let «tail:1» : (_root_.List parameterIR) := «exec:3»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ParameterType_alpha parameterIR_a parameterIR_b⟩) (fun («exec:5» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:parserObjectTypeIR:iter:2» «tail:0» «tail:1»⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:parserObjectTypeIR:iter:2_clauses» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:parserObjectTypeIR:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:parserObjectTypeIR:iter:2:clause:1»  input0 input1)]


noncomputable def «Type_alpha:controlObjectTypeIR:iter:2:clause:0» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:controlObjectTypeIR:iter:2:clause:1» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_a : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let parameterIR_b : parameterIR := «exec:4»; (let «tail:1» : (_root_.List parameterIR) := «exec:3»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ParameterType_alpha parameterIR_a parameterIR_b⟩) (fun («exec:5» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:controlObjectTypeIR:iter:2» «tail:0» «tail:1»⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:controlObjectTypeIR:iter:2_clauses» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:controlObjectTypeIR:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:controlObjectTypeIR:iter:2:clause:1»  input0 input1)]


noncomputable def «Type_alpha:packageObjectTypeIR:iter:2:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:packageObjectTypeIR:iter:2:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_a : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_b : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_alpha typeIR_a typeIR_b⟩) (fun («exec:5» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:packageObjectTypeIR:iter:2» «tail:0» «tail:1»⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:packageObjectTypeIR:iter:2_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:packageObjectTypeIR:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:packageObjectTypeIR:iter:2:clause:1»  input0 input1)]


noncomputable def «Type_alpha:non-default:iter:2:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)

end SpecTec
