import SpecTecDecl0138

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$update_fieldValue:clause:0» (input0 : (_root_.List fieldValue)) (input1 : SpecTec.nameIR) (input2 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «fieldValue*» : (_root_.List fieldValue) := input0; (let nameIR : SpecTec.nameIR := input1; (let value : SpecTec.value := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «fieldValue*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))))))))


noncomputable def «$update_fieldValue:clause:1» (input0 : (_root_.List fieldValue)) (input1 : SpecTec.nameIR) (input2 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «fieldValue*» : (_root_.List fieldValue) := input0; (let nameIR : SpecTec.nameIR := input1; (let value : SpecTec.value := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «fieldValue*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «fieldValue*» with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field_h : SpecTec.value := «exec:3»; (let nameIR_field_h : SpecTec.nameIR := «exec:4»; (let «fieldValue_t*» : (_root_.List fieldValue) := «exec:1»; (.bind (.guard (nameIR = nameIR_field_h)) (fun (_ : Unit) => (.pure (((((fieldValue.«% % ';'» value nameIR) : fieldValue) :: «fieldValue_t*») : (_root_.List fieldValue)))))))))) | [] => .unmatch))))))


noncomputable def «$update_fieldValue:clause:2» (input0 : (_root_.List fieldValue)) (input1 : SpecTec.nameIR) (input2 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «fieldValue*» : (_root_.List fieldValue) := input0; (let nameIR : SpecTec.nameIR := input1; (let value : SpecTec.value := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «fieldValue*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «fieldValue*» with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field_h : SpecTec.value := «exec:3»; (let nameIR_field_h : SpecTec.nameIR := «exec:4»; (let «fieldValue_t*» : (_root_.List fieldValue) := «exec:1»; (.bind (.guard ((nameIR_field_h ≠ nameIR))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$update_fieldValue» «fieldValue_t*» nameIR value⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «eval:0» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value_field_h nameIR_field_h) : fieldValue) :: «eval:0») : (_root_.List fieldValue))))))))))))) | [] => .unmatch))))))


noncomputable def «$update_fieldValue_clauses» (input0 : (_root_.List fieldValue)) (input1 : nameIR) (input2 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_fieldValue:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$update_fieldValue:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$update_fieldValue:clause:2»  input0 input1 input2)]


noncomputable def «$invalidate_header:clause:0» (input0 : headerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«HEADER % `{ % ';' % `}» «exec:1» «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:1»; (let _b : _root_.Bool := «exec:2»; (let «fieldValue*» : (_root_.List fieldValue) := «exec:3»; (.pure ((((headerValue.«HEADER % `{ % ';' % `}» typeId false «fieldValue*») : headerValue) : headerValue)))))))


noncomputable def «$invalidate_header_clauses» (input0 : headerValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$invalidate_header:clause:0»  input0)]


noncomputable def «$invalidate_headerUnion:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$invalidate_headerUnion:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let nameIR_field : nameIR := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$invalidate_headerUnion:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «$invalidate_headerUnion:case_1:pattern-iter:0_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$invalidate_headerUnion:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$invalidate_headerUnion:case_1:pattern-iter:0:clause:1»  input0)]


noncomputable def «$invalidate_headerUnion:case_1:iter:4:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$invalidate_headerUnion:case_1:iter:4:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field_invalidated : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$invalidate_headerUnion:case_1:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value_field_invalidated nameIR_field) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$invalidate_headerUnion:case_1:iter:4_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$invalidate_headerUnion:case_1:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$invalidate_headerUnion:case_1:iter:4:clause:1»  input0 input1)]


noncomputable def «$write_bits_from_value:case_7:pattern-iter:1:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List value))) : ((_root_.List id) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$write_bits_from_value:case_7:pattern-iter:1:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let id_field : id := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«$write_bits_from_value:case_7:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List id) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((id_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List id) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «$write_bits_from_value:case_7:pattern-iter:1_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$write_bits_from_value:case_7:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:case_7:pattern-iter:1:clause:1»  input0)]


noncomputable def «$write_bits_from_value:case_8:pattern-iter:1:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List value))) : ((_root_.List id) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$write_bits_from_value:case_8:pattern-iter:1:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let id_field : id := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«$write_bits_from_value:case_8:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List id) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((id_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List id) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «$write_bits_from_value:case_8:pattern-iter:1_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$write_bits_from_value:case_8:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:case_8:pattern-iter:1:clause:1»  input0)]


noncomputable def «$write_bits_from_value:case_10:pattern-iter:1:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List value))) : ((_root_.List id) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$write_bits_from_value:case_10:pattern-iter:1:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value : SpecTec.value := «exec:3»; (let id : SpecTec.id := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.id) × (_root_.List SpecTec.value)), SpecTecCall.«$write_bits_from_value:case_10:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.id) × (_root_.List SpecTec.value))) => (let «pattern-tail:1» : (_root_.List SpecTec.id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.value) := («exec:5»).2; (.pure ((((id :: «pattern-tail:1»), (value :: «pattern-tail:2»)) : ((_root_.List SpecTec.id) × (_root_.List SpecTec.value))))))))))))) | [] => .unmatch)


noncomputable def «$write_bits_from_value:case_10:pattern-iter:1_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$write_bits_from_value:case_10:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:case_10:pattern-iter:1:clause:1»  input0)]


noncomputable def «$capture_avoiding_:case_1:iter:8:clause:0» (input0 : bound) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B_capture : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «$capture_avoiding_:case_1:iter:8:clause:1» (input0 : bound) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B_capture : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeParameterIR_fresh : typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List typeParameterIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» typeId typeParameterIR_fresh B_capture⟩) (fun («exec:3» : _root_.Bool) => (let «eval:9» : _root_.Bool := «exec:3»; (.bind (.guard ((¬ («eval:9» = true)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$capture_avoiding_:case_1:iter:8» B_capture «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch))


noncomputable def «$capture_avoiding_:case_1:iter:8_clauses» (input0 : bound) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:8:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:8:clause:1»  input0 input1)]


noncomputable def «$capture_avoiding:case_1:iter:8:clause:0» (input0 : bound) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B_capture : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «$capture_avoiding:case_1:iter:8:clause:1» (input0 : bound) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B_capture : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeId_fresh : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» typeId typeId_fresh B_capture⟩) (fun («exec:3» : _root_.Bool) => (let «eval:9» : _root_.Bool := «exec:3»; (.bind (.guard ((¬ («eval:9» = true)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$capture_avoiding:case_1:iter:8» B_capture «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch))


noncomputable def «$capture_avoiding:case_1:iter:8_clauses» (input0 : bound) (input1 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:8:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:8:clause:1»  input0 input1)]


noncomputable def «Type_alpha:serializable:pattern-iter:1:clause:0» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:serializable:pattern-iter:1:clause:1» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' % ';'» «exec:3» «exec:4» => (let nameIR_field : nameIR := «exec:3»; (let value_field : value := «exec:4»; (let «pattern-tail:0» : (_root_.List valueFieldIR) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Type_alpha:serializable:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Type_alpha:serializable:pattern-iter:1_clauses» (input0 : (_root_.List valueFieldIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:serializable:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Type_alpha:serializable:pattern-iter:1:clause:1»  input0)]


noncomputable def «Type_alpha:serializable:iter:4:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List valueFieldIR)) : (_root_.List valueFieldIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:serializable:iter:4:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List valueFieldIR), SpecTecCall.«Type_alpha:serializable:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List valueFieldIR)) => (let «tail:2» : (_root_.List valueFieldIR) := «exec:5»; (.pure (((((valueFieldIR.«% '=' % ';'» nameIR_field value_field) : valueFieldIR) :: «tail:2») : (_root_.List valueFieldIR))))))))) | [] => .unmatch))) | [] => .unmatch)

end SpecTec
