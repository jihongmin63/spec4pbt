import SpecTecDecl0323

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$write_value_fields_from_bits':clause:0» (input0 : (_root_.List fieldValue)) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «fieldValue*» : (_root_.List fieldValue) := input0; (let n_var : _root_.Nat := input1; (let «b*» : (_root_.List _root_.Bool) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «fieldValue*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure (((([] : (_root_.List fieldValue)), «b*») : ((_root_.List fieldValue) × (_root_.List _root_.Bool))))))))))


noncomputable def «$write_value_fields_from_bits':clause:1» (input0 : (_root_.List fieldValue)) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «fieldValue*» : (_root_.List fieldValue) := input0; (let n_var : _root_.Nat := input1; (let «b*» : (_root_.List _root_.Bool) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «fieldValue*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «fieldValue*» with | «exec:2» :: «exec:1» => (let fieldValue_h : fieldValue := «exec:2»; (let «fieldValue_t*» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨(fieldValue × (_root_.List _root_.Bool)), SpecTecCall.«$write_value_field_from_bits'» fieldValue_h n_var «b*»⟩) (fun («exec:3» : (fieldValue × (_root_.List _root_.Bool))) => (let «eval:0» : (fieldValue × (_root_.List _root_.Bool)) := «exec:3»; (let fieldValue_h_updated : fieldValue := («eval:0»).1; (let «b_t*» : (_root_.List _root_.Bool) := («eval:0»).2; (.bind (.call ⟨((_root_.List fieldValue) × (_root_.List _root_.Bool)), SpecTecCall.«$write_value_fields_from_bits'» «fieldValue_t*» n_var «b_t*»⟩) (fun («exec:4» : ((_root_.List fieldValue) × (_root_.List _root_.Bool))) => (let «eval:1» : ((_root_.List fieldValue) × (_root_.List _root_.Bool)) := «exec:4»; (let «fieldValue_t_updated*» : (_root_.List fieldValue) := («eval:1»).1; (let «b_rest*» : (_root_.List _root_.Bool) := («eval:1»).2; (.pure ((((fieldValue_h_updated :: «fieldValue_t_updated*»), «b_rest*») : ((_root_.List fieldValue) × (_root_.List _root_.Bool))))))))))))))))) | [] => .unmatch))))))


noncomputable def «$write_value_fields_from_bits'_clauses» (input0 : (_root_.List fieldValue)) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$write_value_fields_from_bits':clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$write_value_fields_from_bits':clause:1»  input0 input1 input2)]


noncomputable def «$write_value_field_from_bits':clause:0» (input0 : fieldValue) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % ';'» «exec:1» «exec:2» => (let value : SpecTec.value := «exec:1»; (let id : SpecTec.id := «exec:2»; (let n_var : _root_.Nat := input1; (let «b*» : (_root_.List _root_.Bool) := input2; (.bind (.call ⟨(SpecTec.value × (_root_.List _root_.Bool)), SpecTecCall.«$write_value_from_bits'» value n_var «b*»⟩) (fun («exec:3» : (SpecTec.value × (_root_.List _root_.Bool))) => (let «eval:0» : (SpecTec.value × (_root_.List _root_.Bool)) := «exec:3»; (let value_updated : SpecTec.value := («eval:0»).1; (let «b_rest*» : (_root_.List _root_.Bool) := («eval:0»).2; (.pure (((((fieldValue.«% % ';'» value_updated id) : fieldValue), «b_rest*») : (fieldValue × (_root_.List _root_.Bool)))))))))))))))


noncomputable def «$write_value_field_from_bits'_clauses» (input0 : fieldValue) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$write_value_field_from_bits':clause:0»  input0 input1 input2)]


noncomputable def «$write_value_from_bits:clause:0» (input0 : SpecTec.value) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (let n_var : _root_.Nat := input1; (let «b*» : (_root_.List _root_.Bool) := input2; (.bind (.call ⟨(SpecTec.value × (_root_.List _root_.Bool)), SpecTecCall.«$write_value_from_bits'» value n_var «b*»⟩) (fun («exec:1» : (SpecTec.value × (_root_.List _root_.Bool))) => (let «eval:0» : (SpecTec.value × (_root_.List _root_.Bool)) := «exec:1»; (let value_updated : SpecTec.value := («eval:0»).1; (let «b'*» : (_root_.List _root_.Bool) := («eval:0»).2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «b'*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((value_updated : SpecTec.value)))))))))))))


noncomputable def «$write_value_from_bits_clauses» (input0 : value) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$write_value_from_bits:clause:0»  input0 input1 input2)]


noncomputable def «$write_bits_from_value:clause:0» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:boolValue» value) = true))) (fun (_ : Unit) => (match («$write_bits_from_value:case_1:downcast:0» value) with | some «exec:1» => (let «eval:0» : boolValue := «exec:1»; (match «eval:0» with | ._B «exec:2» => (let b : _root_.Bool := «exec:2»; (.pure ((([b] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool))))))) | none => .unmatch))))


noncomputable def «$write_bits_from_value:clause:1» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:integerLiteral» value) = true))) (fun (_ : Unit) => (match («$write_bits_from_value:case_2:downcast:0» value) with | some «exec:1» => (let «eval:0» : SpecTec.integerLiteral := «exec:1»; (let integerLiteral : SpecTec.integerLiteral := «eval:0»; (.bind (.guard (((«exec:match:integerLiteral:% S %» integerLiteral) = true))) (fun (_ : Unit) => (match integerLiteral with | .«% S %» «exec:2» «exec:3» => (let w : _root_.Nat := «exec:2»; (let i : _root_.Int := «exec:3»; (.bind (.call ⟨bits, SpecTecCall.«$int_to_bits_signed» w i⟩) (fun («exec:4» : bits) => (let «eval:1» : bits := «exec:4»; (.pure ((«eval:1» : (_root_.List _root_.Bool))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$write_bits_from_value:clause:2» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:integerLiteral» value) = true))) (fun (_ : Unit) => (match («$write_bits_from_value:case_3:downcast:0» value) with | some «exec:1» => (let «eval:0» : SpecTec.integerLiteral := «exec:1»; (let integerLiteral : SpecTec.integerLiteral := «eval:0»; (.bind (.guard (((«exec:match:integerLiteral:% W %» integerLiteral) = true))) (fun (_ : Unit) => (match integerLiteral with | .«% W %» «exec:2» «exec:3» => (let w : _root_.Nat := «exec:2»; (let i : _root_.Int := «exec:3»; (.bind (.call ⟨bits, SpecTecCall.«$int_to_bits_unsigned» w i⟩) (fun («exec:4» : bits) => (let «eval:1» : bits := «exec:4»; (.pure ((«eval:1» : (_root_.List _root_.Bool))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$write_bits_from_value:clause:3» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:integerValue» value) = true))) (fun (_ : Unit) => (match («$write_bits_from_value:case_4:downcast:0» value) with | some «exec:1» => (let «eval:0» : SpecTec.integerValue := «exec:1»; (let integerValue : SpecTec.integerValue := «eval:0»; (.bind (.guard (((«exec:match:integerValue:% '.' % V %» integerValue) = true))) (fun (_ : Unit) => (match integerValue with | .«% '.' % V %» «exec:2» «exec:3» «exec:4» => (let _nat : _root_.Nat := «exec:2»; (let w : _root_.Nat := «exec:3»; (let i : _root_.Int := «exec:4»; (.bind (.call ⟨bits, SpecTecCall.«$int_to_bits_unsigned» w i⟩) (fun («exec:5» : bits) => (let «eval:1» : bits := «exec:5»; (.pure ((«eval:1» : (_root_.List _root_.Bool)))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$write_bits_from_value:clause:4» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:arrayValue» value) = true))) (fun (_ : Unit) => (match («$write_bits_from_value:case_5:downcast:0» value) with | some «exec:1» => (let «eval:0» : arrayValue := «exec:1»; (match «eval:0» with | .«ARRAY `[ % `]» «exec:2» => (let «value_element*» : (_root_.List SpecTec.value) := «exec:2»; (.bind (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_5:iter:1» «value_element*»⟩) (fun («exec:3» : (_root_.List (_root_.List _root_.Bool))) => (let «eval:3» : (_root_.List (_root_.List _root_.Bool)) := «exec:3»; (.pure (((«$concat_» (X := _root_.Bool) «eval:3») : (_root_.List _root_.Bool)))))))))) | none => .unmatch))))


noncomputable def «$write_bits_from_value:clause:5» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:headerStackValue» value) = true))) (fun (_ : Unit) => (match («$write_bits_from_value:case_6:downcast:0» value) with | some «exec:1» => (let «eval:0» : headerStackValue := «exec:1»; (match «eval:0» with | .«HEADER_STACK `[ % `( % `) `]» «exec:2» «exec:3» => (let «value_element*» : (_root_.List SpecTec.value) := «exec:2»; (let _nat : _root_.Nat := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_6:iter:1» «value_element*»⟩) (fun («exec:4» : (_root_.List (_root_.List _root_.Bool))) => (let «eval:3» : (_root_.List (_root_.List _root_.Bool)) := «exec:4»; (.pure (((«$concat_» (X := _root_.Bool) «eval:3») : (_root_.List _root_.Bool))))))))))) | none => .unmatch))))


noncomputable def «$write_bits_from_value:clause:6» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:structValue» value) = true))) (fun (_ : Unit) => (match («$write_bits_from_value:case_7:downcast:0» value) with | some «exec:1» => (let «eval:0» : structValue := «exec:1»; (match «eval:0» with | .«STRUCT % `{ % `}» «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let «eval:2» : (_root_.List fieldValue) := «exec:3»; (.bind (.call ⟨((_root_.List id) × (_root_.List SpecTec.value)), SpecTecCall.«$write_bits_from_value:case_7:pattern-iter:1» «eval:2»⟩) (fun («exec:4» : ((_root_.List id) × (_root_.List SpecTec.value))) => (let «id_field*» : (_root_.List id) := («exec:4»).1; (let «value_field*» : (_root_.List SpecTec.value) := («exec:4»).2; (.bind (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_7:iter:3» «value_field*»⟩) (fun («exec:5» : (_root_.List (_root_.List _root_.Bool))) => (let «eval:5» : (_root_.List (_root_.List _root_.Bool)) := «exec:5»; (.pure (((«$concat_» (X := _root_.Bool) «eval:5») : (_root_.List _root_.Bool))))))))))))))) | none => .unmatch))))


noncomputable def «$write_bits_from_value:clause:7» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:headerValue» value) = true))) (fun (_ : Unit) => (match («$write_bits_from_value:case_8:downcast:0» value) with | some «exec:1» => (let «eval:0» : headerValue := «exec:1»; (match «eval:0» with | .«HEADER % `{ % ';' % `}» «exec:2» «exec:3» «exec:4» => (let _typeId : typeId := «exec:2»; (let b : _root_.Bool := «exec:3»; (let «eval:2» : (_root_.List fieldValue) := «exec:4»; (.bind (.call ⟨((_root_.List id) × (_root_.List SpecTec.value)), SpecTecCall.«$write_bits_from_value:case_8:pattern-iter:1» «eval:2»⟩) (fun («exec:5» : ((_root_.List id) × (_root_.List SpecTec.value))) => (let «id_field*» : (_root_.List id) := («exec:5»).1; (let «value_field*» : (_root_.List SpecTec.value) := («exec:5»).2; (.bind (.guard (true = b)) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_8:iter:3» «value_field*»⟩) (fun («exec:6» : (_root_.List (_root_.List _root_.Bool))) => (let «eval:5» : (_root_.List (_root_.List _root_.Bool)) := «exec:6»; (.pure (((«$concat_» (X := _root_.Bool) «eval:5») : (_root_.List _root_.Bool)))))))))))))))))) | none => .unmatch))))


noncomputable def «$write_bits_from_value:clause:8» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:headerValue» value) = true))) (fun (_ : Unit) => (match («$write_bits_from_value:case_9:downcast:0» value) with | some «exec:1» => (let «eval:0» : headerValue := «exec:1»; (match «eval:0» with | .«HEADER % `{ % ';' % `}» «exec:2» «exec:3» «exec:4» => (let _typeId : typeId := «exec:2»; (let b : _root_.Bool := «exec:3»; (let «_fieldValue*» : (_root_.List fieldValue) := «exec:4»; (.bind (.guard (false = b)) (fun (_ : Unit) => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool))))))))))) | none => .unmatch))))


noncomputable def «$write_bits_from_value:clause:9» (input0 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value' : value := input0; (.bind (.guard (((«sub:value:headerUnionValue» value') = true))) (fun (_ : Unit) => (match («$write_bits_from_value:case_10:downcast:0» value') with | some «exec:1» => (let «eval:0» : headerUnionValue := «exec:1»; (match «eval:0» with | .«HEADER_UNION % `{ % `}» «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let «eval:2» : (_root_.List fieldValue) := «exec:3»; (.bind (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«$write_bits_from_value:case_10:pattern-iter:1» «eval:2»⟩) (fun («exec:4» : ((_root_.List id) × (_root_.List value))) => (let «id*» : (_root_.List id) := («exec:4»).1; (let «value*» : (_root_.List value) := («exec:4»).2; (.bind (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_10:iter:3» «value*»⟩) (fun («exec:5» : (_root_.List (_root_.List _root_.Bool))) => (let «eval:5» : (_root_.List (_root_.List _root_.Bool)) := «exec:5»; (.pure (((«$concat_» (X := _root_.Bool) «eval:5») : (_root_.List _root_.Bool))))))))))))))) | none => .unmatch))))


noncomputable def «$write_bits_from_value:clause:10» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value' : SpecTec.value := input0; (.bind (.guard (((«sub:value:enumValue» value') = true))) (fun (_ : Unit) => (match («$write_bits_from_value:case_11:downcast:0» value') with | some «exec:1» => (let «eval:0» : SpecTec.enumValue := «exec:1»; (let enumValue : SpecTec.enumValue := «eval:0»; (.bind (.guard (((«exec:match:enumValue:% '.' % '.' %» enumValue) = true))) (fun (_ : Unit) => (match enumValue with | .«% '.' % '.' %» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let id : SpecTec.id := «exec:3»; (let value : SpecTec.value := «exec:4»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$write_bits_from_value» value⟩) (fun («exec:5» : (_root_.List _root_.Bool)) => (let «eval:1» : (_root_.List _root_.Bool) := «exec:5»; (.pure ((«eval:1» : (_root_.List _root_.Bool)))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$write_bits_from_value_clauses» (input0 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$write_bits_from_value:clause:0»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:clause:1»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:clause:2»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:clause:3»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:clause:4»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:clause:5»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:clause:6»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:clause:7»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:clause:8»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:clause:9»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:clause:10»  input0)]


noncomputable def «$write_bits_from_value:case_5:iter:1:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List _root_.Bool))) : (_root_.List (_root_.List _root_.Bool))))) | _ :: _ => .unmatch)


noncomputable def «$write_bits_from_value:case_5:iter:1:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_element : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$write_bits_from_value» value_element⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «eval:2» : (_root_.List _root_.Bool) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_5:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List _root_.Bool))) => (let «tail:1» : (_root_.List (_root_.List _root_.Bool)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$write_bits_from_value:case_5:iter:1_clauses» (input0 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$write_bits_from_value:case_5:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:case_5:iter:1:clause:1»  input0)]


noncomputable def «$write_bits_from_value:case_6:iter:1:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List _root_.Bool))) : (_root_.List (_root_.List _root_.Bool))))) | _ :: _ => .unmatch)


noncomputable def «$write_bits_from_value:case_6:iter:1:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_element : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$write_bits_from_value» value_element⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «eval:2» : (_root_.List _root_.Bool) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_6:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List _root_.Bool))) => (let «tail:1» : (_root_.List (_root_.List _root_.Bool)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$write_bits_from_value:case_6:iter:1_clauses» (input0 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$write_bits_from_value:case_6:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:case_6:iter:1:clause:1»  input0)]


noncomputable def «$write_bits_from_value:case_7:iter:3:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List _root_.Bool))) : (_root_.List (_root_.List _root_.Bool))))) | _ :: _ => .unmatch)


noncomputable def «$write_bits_from_value:case_7:iter:3:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_field : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$write_bits_from_value» value_field⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «eval:4» : (_root_.List _root_.Bool) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_7:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List _root_.Bool))) => (let «tail:1» : (_root_.List (_root_.List _root_.Bool)) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$write_bits_from_value:case_7:iter:3_clauses» (input0 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$write_bits_from_value:case_7:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:case_7:iter:3:clause:1»  input0)]


noncomputable def «$write_bits_from_value:case_8:iter:3:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List _root_.Bool))) : (_root_.List (_root_.List _root_.Bool))))) | _ :: _ => .unmatch)


noncomputable def «$write_bits_from_value:case_8:iter:3:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_field : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$write_bits_from_value» value_field⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «eval:4» : (_root_.List _root_.Bool) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List _root_.Bool)), SpecTecCall.«$write_bits_from_value:case_8:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List _root_.Bool))) => (let «tail:1» : (_root_.List (_root_.List _root_.Bool)) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$write_bits_from_value:case_8:iter:3_clauses» (input0 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$write_bits_from_value:case_8:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$write_bits_from_value:case_8:iter:3:clause:1»  input0)]


noncomputable def «$write_bits_from_value:case_10:iter:3:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List _root_.Bool))) : (_root_.List (_root_.List _root_.Bool))))) | _ :: _ => .unmatch)

end SpecTec
