import SpecTecDecl0329

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$default:clause:15» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:simpleEnumTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$default:case_16:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : simpleEnumTypeIR := «exec:1»; (match «eval:0» with | .«ENUM % `{ % `}» «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let «id*» : (_root_.List id) := «exec:3»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «id*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «id*» with | «exec:5» :: «exec:4» => (let id_f_h : id := «exec:5»; (let «_id*» : (_root_.List id) := «exec:4»; (.pure ((((value.«% '.' %» typeId id_f_h) : value) : value))))) | [] => .unmatch))))))) | none => .unmatch))))


noncomputable def «$default:clause:16» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:serializableEnumTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$default:case_17:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : serializableEnumTypeIR := «exec:1»; (match «eval:0» with | .«ENUM % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (let «eval:2» : (_root_.List valueFieldIR) := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$default:case_17:pattern-iter:1» «eval:2»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «nameIR_field*» : (_root_.List nameIR) := («exec:5»).1; (let «value_field*» : (_root_.List value) := («exec:5»).2; (.bind (.call ⟨value, SpecTecCall.«$cast_int» typeIR ((integerValue.D (_root_.Int.ofNat (0 : _root_.Nat))) : integerValue)⟩) (fun («exec:6» : value) => (let «eval:3» : value := «exec:6»; (let value_zero : value := «eval:3»; (.bind (.call ⟨(_root_.List (value × _root_.String)), SpecTecCall.«$default:case_17:iter:4» «nameIR_field*» «value_field*»⟩) (fun («exec:7» : (_root_.List (value × _root_.String))) => (let «eval:5» : (_root_.List (value × nameIR)) := «exec:7»; (.bind (.call ⟨(_root_.Option id), SpecTecCall.«$assoc_» value id value_zero «eval:5»⟩) (fun («exec:8» : (_root_.Option id)) => (let «eval:6» : (_root_.Option id) := «exec:8»; (let id? : (_root_.Option id) := «eval:6»; (.bind (.guard (((_root_.Option.isSome id?) = true))) (fun (_ : Unit) => (match id? with | some «exec:9» => (let id_zero : id := «exec:9»; (.pure ((((value.«% '.' % '.' %» typeId id_zero value_zero) : value) : value)))) | none => .unmatch))))))))))))))))))))))) | none => .unmatch))))


noncomputable def «$default:clause:17» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:serializableEnumTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$default:case_18:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : serializableEnumTypeIR := «exec:1»; (match «eval:0» with | .«ENUM % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (let «eval:2» : (_root_.List valueFieldIR) := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$default:case_18:pattern-iter:1» «eval:2»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «nameIR_field*» : (_root_.List nameIR) := («exec:5»).1; (let «value_field*» : (_root_.List value) := («exec:5»).2; (.bind (.call ⟨value, SpecTecCall.«$cast_int» typeIR ((integerValue.D (_root_.Int.ofNat (0 : _root_.Nat))) : integerValue)⟩) (fun («exec:6» : value) => (let «eval:3» : value := «exec:6»; (let value_zero : value := «eval:3»; (.bind (.call ⟨(_root_.List (value × _root_.String)), SpecTecCall.«$default:case_18:iter:4» «nameIR_field*» «value_field*»⟩) (fun («exec:7» : (_root_.List (value × _root_.String))) => (let «eval:5» : (_root_.List (value × nameIR)) := «exec:7»; (.bind (.call ⟨(_root_.Option id), SpecTecCall.«$assoc_» value id value_zero «eval:5»⟩) (fun («exec:8» : (_root_.Option id)) => (let «eval:6» : (_root_.Option id) := «exec:8»; (match «eval:6» with | none => (let id_zero : id := "__UNSPECIFIED"; (.pure ((((value.«% '.' % '.' %» typeId id_zero value_zero) : value) : value)))) | some _ => .unmatch)))))))))))))))))))) | none => .unmatch))))


noncomputable def «$default_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:clause:0»  input0), fun (_ : _root_.Unit) => («$default:clause:1»  input0), fun (_ : _root_.Unit) => («$default:clause:2»  input0), fun (_ : _root_.Unit) => («$default:clause:3»  input0), fun (_ : _root_.Unit) => («$default:clause:4»  input0), fun (_ : _root_.Unit) => («$default:clause:5»  input0), fun (_ : _root_.Unit) => («$default:clause:6»  input0), fun (_ : _root_.Unit) => («$default:clause:7»  input0), fun (_ : _root_.Unit) => («$default:clause:8»  input0), fun (_ : _root_.Unit) => («$default:clause:9»  input0), fun (_ : _root_.Unit) => («$default:clause:10»  input0), fun (_ : _root_.Unit) => («$default:clause:11»  input0), fun (_ : _root_.Unit) => («$default:clause:12»  input0), fun (_ : _root_.Unit) => («$default:clause:13»  input0), fun (_ : _root_.Unit) => («$default:clause:14»  input0), fun (_ : _root_.Unit) => («$default:clause:15»  input0), fun (_ : _root_.Unit) => («$default:clause:16»  input0), fun (_ : _root_.Unit) => («$default:clause:17»  input0)]


noncomputable def «$default:case_10:iter:1:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «$default:case_10:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨value, SpecTecCall.«$default» typeIR⟩) (fun («exec:3» : value) => (let «eval:2» : value := «exec:3»; (.bind (.call ⟨(_root_.List value), SpecTecCall.«$default:case_10:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List value)))))))))))) | [] => .unmatch)


noncomputable def «$default:case_10:iter:1_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:case_10:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$default:case_10:iter:1:clause:1»  input0)]


noncomputable def «$default:case_13:iter:3:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$default:case_13:iter:3:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_f : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_f : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨value, SpecTecCall.«$default» typeIR_f⟩) (fun («exec:5» : value) => (let «eval:4» : value := «exec:5»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$default:case_13:iter:3» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:6»; (.pure (((((fieldValue.«% % ';'» «eval:4» id_f) : fieldValue) :: «tail:2») : (_root_.List fieldValue)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$default:case_13:iter:3_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:case_13:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$default:case_13:iter:3:clause:1»  input0 input1)]


noncomputable def «$default:case_14:iter:3:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$default:case_14:iter:3:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_f : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_f : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨value, SpecTecCall.«$default» typeIR_f⟩) (fun («exec:5» : value) => (let «eval:4» : value := «exec:5»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$default:case_14:iter:3» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:6»; (.pure (((((fieldValue.«% % ';'» «eval:4» id_f) : fieldValue) :: «tail:2») : (_root_.List fieldValue)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$default:case_14:iter:3_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:case_14:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$default:case_14:iter:3:clause:1»  input0 input1)]


noncomputable def «$default:case_15:iter:3:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$default:case_15:iter:3:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_f : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_f : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨value, SpecTecCall.«$default» typeIR_f⟩) (fun («exec:5» : value) => (let «eval:4» : value := «exec:5»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$default:case_15:iter:3» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:6»; (.pure (((((fieldValue.«% % ';'» «eval:4» id_f) : fieldValue) :: «tail:2») : (_root_.List fieldValue)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$default:case_15:iter:3_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:case_15:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$default:case_15:iter:3:clause:1»  input0 input1)]


noncomputable def «$cast_to_enum:clause:0» (input0 : SpecTec.enumTypeIR) (input1 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let enumTypeIR : SpecTec.enumTypeIR := input0; (let value : SpecTec.value := input1; (.bind (.guard (((«sub:enumTypeIR:serializableEnumTypeIR» enumTypeIR) = true))) (fun (_ : Unit) => (match («$cast_to_enum:case_1:downcast:0» enumTypeIR) with | some «exec:1» => (let «eval:0» : serializableEnumTypeIR := «exec:1»; (match «eval:0» with | .«ENUM % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (let «valueFieldIR*» : (_root_.List valueFieldIR) := «exec:4»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_to_enum'» typeId typeIR «valueFieldIR*» value⟩) (fun («exec:5» : SpecTec.value) => (let «eval:1» : SpecTec.value := «exec:5»; (.pure ((«eval:1» : SpecTec.value))))))))))) | none => .unmatch)))))


noncomputable def «$cast_to_enum_clauses» (input0 : enumTypeIR) (input1 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_to_enum:clause:0»  input0 input1)]


noncomputable def «$cast_to_enum':clause:0» (input0 : SpecTec.typeId) (input1 : SpecTec.typeIR) (input2 : (_root_.List valueFieldIR)) (input3 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeId : SpecTec.typeId := input0; (let typeIR : SpecTec.typeIR := input1; (let «valueFieldIR*» : (_root_.List valueFieldIR) := input2; (let value_target : value := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «valueFieldIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$cast_op» typeIR value_target⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (let value_idx : value := «eval:0»; (let id_unnamed : id := "__UNSPECIFIED"; (.pure ((((value.«% '.' % '.' %» typeId id_unnamed value_idx) : value) : value))))))))))))))


noncomputable def «$cast_to_enum':clause:1» (input0 : SpecTec.typeId) (input1 : SpecTec.typeIR) (input2 : (_root_.List valueFieldIR)) (input3 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeId : SpecTec.typeId := input0; (let typeIR : SpecTec.typeIR := input1; (let «valueFieldIR*» : (_root_.List valueFieldIR) := input2; (let value_target : SpecTec.value := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «valueFieldIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «valueFieldIR*» with | «exec:2» :: «exec:1» => (let valueFieldIR_h : valueFieldIR := «exec:2»; (let «valueFieldIR_t*» : (_root_.List valueFieldIR) := «exec:1»; (match valueFieldIR_h with | .«% '=' % ';'» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let value : SpecTec.value := «exec:4»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» value value_target⟩) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.pure ((((SpecTec.value.«% '.' % '.' %» typeId nameIR value) : SpecTec.value) : SpecTec.value))))))))))))) | [] => .unmatch)))))))


noncomputable def «$cast_to_enum':clause:2» (input0 : SpecTec.typeId) (input1 : SpecTec.typeIR) (input2 : (_root_.List valueFieldIR)) (input3 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeId : SpecTec.typeId := input0; (let typeIR : SpecTec.typeIR := input1; (let «valueFieldIR*» : (_root_.List valueFieldIR) := input2; (let value_target : SpecTec.value := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «valueFieldIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «valueFieldIR*» with | «exec:2» :: «exec:1» => (let valueFieldIR_h : valueFieldIR := «exec:2»; (let «valueFieldIR_t*» : (_root_.List valueFieldIR) := «exec:1»; (match valueFieldIR_h with | .«% '=' % ';'» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let value : SpecTec.value := «exec:4»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» value value_target⟩) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_to_enum'» typeId typeIR «valueFieldIR_t*» value_target⟩) (fun («exec:6» : SpecTec.value) => (let «eval:1» : SpecTec.value := «exec:6»; (.pure ((«eval:1» : SpecTec.value)))))))))))))))) | [] => .unmatch)))))))


noncomputable def «$cast_to_enum'_clauses» (input0 : typeId) (input1 : typeIR) (input2 : (_root_.List valueFieldIR)) (input3 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_to_enum':clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$cast_to_enum':clause:1»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$cast_to_enum':clause:2»  input0 input1 input2 input3)]


noncomputable def «$cast_bool:clause:0» (input0 : SpecTec.typeIR) (input1 : boolValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (match input1 with | ._B «exec:1» => (let b : _root_.Bool := «exec:1»; (.bind (.guard (((«sub:typeIR:boolTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$cast_bool:case_1:downcast:0» typeIR) with | some «exec:2» => (let «eval:0» : SpecTec.boolTypeIR := «exec:2»; (let boolTypeIR : SpecTec.boolTypeIR := «eval:0»; (.bind (.guard (((SpecTec.boolTypeIR.BOOL) : SpecTec.boolTypeIR) = boolTypeIR)) (fun (_ : Unit) => (.pure ((((value._B b) : value) : value))))))) | none => .unmatch))))))


noncomputable def «$cast_bool:clause:1» (input0 : SpecTec.typeIR) (input1 : SpecTec.boolValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let boolValue : SpecTec.boolValue := input1; (.bind (.guard (((«sub:typeIR:fixedBitTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$cast_bool:case_2:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : fixedBitTypeIR := «exec:1»; (match «eval:0» with | .«BIT `< % `>» «exec:2» => (let w : _root_.Nat := «exec:2»; (.bind (.guard (((SpecTec.boolValue._B true) : SpecTec.boolValue) = boolValue)) (fun (_ : Unit) => (.pure ((((value.«% W %» w (_root_.Int.ofNat (1 : _root_.Nat))) : value) : value)))))))) | none => .unmatch)))))


noncomputable def «$cast_bool:clause:2» (input0 : SpecTec.typeIR) (input1 : SpecTec.boolValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let boolValue : SpecTec.boolValue := input1; (.bind (.guard (((«sub:typeIR:fixedBitTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$cast_bool:case_3:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : fixedBitTypeIR := «exec:1»; (match «eval:0» with | .«BIT `< % `>» «exec:2» => (let w : _root_.Nat := «exec:2»; (.bind (.guard (((SpecTec.boolValue._B false) : SpecTec.boolValue) = boolValue)) (fun (_ : Unit) => (.pure ((((value.«% W %» w (_root_.Int.ofNat (0 : _root_.Nat))) : value) : value)))))))) | none => .unmatch)))))


noncomputable def «$cast_bool:clause:3» (input0 : SpecTec.typeIR) (input1 : SpecTec.boolValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (let boolValue : SpecTec.boolValue := input1; (.bind (.guard (((«sub:typeIR:newTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$cast_bool:case_4:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : newTypeIR := «exec:1»; (match «eval:0» with | .TYPE «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (.bind (.call ⟨value, SpecTecCall.«$cast_op» typeIR («cast:boolValue:value» boolValue)⟩) (fun («exec:4» : value) => (let «eval:1» : value := «exec:4»; (.pure ((«eval:1» : value)))))))))) | none => .unmatch)))))


noncomputable def «$cast_bool:clause:4» (input0 : SpecTec.typeIR) (input1 : SpecTec.boolValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (let boolValue : SpecTec.boolValue := input1; (.bind (.guard (((«sub:typeIR:setTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$cast_bool:case_5:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : setTypeIR := «exec:1»; (match «eval:0» with | .«SET `< % `>» «exec:2» => (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.call ⟨value, SpecTecCall.«$cast_op» typeIR («cast:boolValue:value» boolValue)⟩) (fun («exec:3» : value) => (let «eval:1» : value := «exec:3»; (.pure ((((value.«SET `{ % `}» «eval:1») : value) : value))))))))) | none => .unmatch)))))


noncomputable def «$cast_bool_clauses» (input0 : typeIR) (input1 : boolValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_bool:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_bool:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$cast_bool:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$cast_bool:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$cast_bool:clause:4»  input0 input1)]


noncomputable def «$cast_int:clause:0» (input0 : SpecTec.typeIR) (input1 : SpecTec.integerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let integerValue : SpecTec.integerValue := input1; (.bind (.guard (((«sub:typeIR:boolTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$cast_int:case_1:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.boolTypeIR := «exec:1»; (let boolTypeIR : SpecTec.boolTypeIR := «eval:0»; (.bind (.guard (((SpecTec.boolTypeIR.BOOL) : SpecTec.boolTypeIR) = boolTypeIR)) (fun (_ : Unit) => (.bind (.guard (((«sub:integerValue:integerLiteral» integerValue) = true))) (fun (_ : Unit) => (match («$cast_int:case_1:downcast:1» integerValue) with | some «exec:2» => (let «eval:1» : SpecTec.integerLiteral := «exec:2»; (let integerLiteral : SpecTec.integerLiteral := «eval:1»; (.bind (.guard (((«exec:match:integerLiteral:D» integerLiteral) = true))) (fun (_ : Unit) => (match integerLiteral with | .D «exec:3» => (let i : _root_.Int := «exec:3»; (.pure ((((value._B (_root_.Decidable.decide (i ≠ (_root_.Int.ofNat (0 : _root_.Nat))))) : value) : value)))) | _ => .unmatch))))) | none => .unmatch))))))) | none => .unmatch)))))


noncomputable def «$cast_int:clause:1» (input0 : SpecTec.typeIR) (input1 : SpecTec.integerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let integerValue : SpecTec.integerValue := input1; (.bind (.guard (((«sub:typeIR:boolTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$cast_int:case_2:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.boolTypeIR := «exec:1»; (let boolTypeIR : SpecTec.boolTypeIR := «eval:0»; (.bind (.guard (((SpecTec.boolTypeIR.BOOL) : SpecTec.boolTypeIR) = boolTypeIR)) (fun (_ : Unit) => (.bind (.guard (((«sub:integerValue:integerLiteral» integerValue) = true))) (fun (_ : Unit) => (match («$cast_int:case_2:downcast:1» integerValue) with | some «exec:2» => (let «eval:1» : SpecTec.integerLiteral := «exec:2»; (let integerLiteral : SpecTec.integerLiteral := «eval:1»; (.bind (.guard (((«exec:match:integerLiteral:% W %» integerLiteral) = true))) (fun (_ : Unit) => (match integerLiteral with | .«% W %» «exec:3» «exec:4» => (let w : _root_.Nat := «exec:3»; (let i : _root_.Int := «exec:4»; (.pure ((((value._B (_root_.Decidable.decide (i ≠ (_root_.Int.ofNat (0 : _root_.Nat))))) : value) : value))))) | _ => .unmatch))))) | none => .unmatch))))))) | none => .unmatch)))))


noncomputable def «$cast_int:clause:2» (input0 : SpecTec.typeIR) (input1 : SpecTec.integerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let integerValue : SpecTec.integerValue := input1; (.bind (.guard (((«sub:typeIR:intTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$cast_int:case_3:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.intTypeIR := «exec:1»; (let intTypeIR : SpecTec.intTypeIR := «eval:0»; (.bind (.guard (((SpecTec.intTypeIR.INT) : SpecTec.intTypeIR) = intTypeIR)) (fun (_ : Unit) => (.bind (.guard (((«sub:integerValue:integerLiteral» integerValue) = true))) (fun (_ : Unit) => (match («$cast_int:case_3:downcast:1» integerValue) with | some «exec:2» => (let «eval:1» : SpecTec.integerLiteral := «exec:2»; (let integerLiteral : SpecTec.integerLiteral := «eval:1»; (.bind (.guard (((«exec:match:integerLiteral:D» integerLiteral) = true))) (fun (_ : Unit) => (match integerLiteral with | .D «exec:3» => (let i : _root_.Int := «exec:3»; (.pure ((((value.D i) : value) : value)))) | _ => .unmatch))))) | none => .unmatch))))))) | none => .unmatch)))))


noncomputable def «$cast_int:clause:3» (input0 : SpecTec.typeIR) (input1 : SpecTec.integerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let integerValue : SpecTec.integerValue := input1; (.bind (.guard (((«sub:typeIR:intTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$cast_int:case_4:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.intTypeIR := «exec:1»; (let intTypeIR : SpecTec.intTypeIR := «eval:0»; (.bind (.guard (((SpecTec.intTypeIR.INT) : SpecTec.intTypeIR) = intTypeIR)) (fun (_ : Unit) => (.bind (.guard (((«sub:integerValue:integerLiteral» integerValue) = true))) (fun (_ : Unit) => (match («$cast_int:case_4:downcast:1» integerValue) with | some «exec:2» => (let «eval:1» : SpecTec.integerLiteral := «exec:2»; (let integerLiteral : SpecTec.integerLiteral := «eval:1»; (.bind (.guard (((«exec:match:integerLiteral:% W %» integerLiteral) = true))) (fun (_ : Unit) => (match integerLiteral with | .«% W %» «exec:3» «exec:4» => (let _nat : _root_.Nat := «exec:3»; (let i : _root_.Int := «exec:4»; (.pure ((((value.D i) : value) : value))))) | _ => .unmatch))))) | none => .unmatch))))))) | none => .unmatch)))))

end SpecTec
