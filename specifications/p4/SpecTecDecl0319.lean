import SpecTecDecl0318

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$tableObject_add_entry:clause:0» (input0 : evalContext) (input1 : tableObject) (input2 : SpecTec.tableEntryPriorityInterface) (input3 : SpecTec.tableKeysetInterface) (input4 : SpecTec.tableActionInterface) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let EC : evalContext := input0; (match input1 with | .«TABLE % `{ % % `}» «exec:1» «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:1»; (let frame : SpecTec.frame := «exec:2»; (let TBL : tableObjectProperty := «exec:3»; (let tableEntryPriorityInterface : SpecTec.tableEntryPriorityInterface := input2; (let tableKeysetInterface : SpecTec.tableKeysetInterface := input3; (let tableActionInterface : SpecTec.tableActionInterface := input4; (.bind (.call ⟨SpecTec.tableEntryPriorityOptIR, SpecTecCall.«$tableObject_create_entry_priority» tableEntryPriorityInterface⟩) (fun («exec:4» : SpecTec.tableEntryPriorityOptIR) => (let «eval:0» : SpecTec.tableEntryPriorityOptIR := «exec:4»; (let tableEntryPriorityOptIR : SpecTec.tableEntryPriorityOptIR := «eval:0»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$needs_priority_tableKeysPropertyIR» (tableObjectProperty.KEYS TBL)⟩) (fun («exec:5» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:5»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_some_» tableEntryPriorityIR tableEntryPriorityOptIR⟩) (fun («exec:6» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:6»; (.bind (.guard (((«eval:1» = true) → («eval:2» = true)))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.keysetExpressionIR, SpecTecCall.«$tableObject_create_entry_keyset» EC (tableObjectProperty.KEYS TBL) tableKeysetInterface⟩) (fun («exec:7» : SpecTec.keysetExpressionIR) => (let «eval:3» : SpecTec.keysetExpressionIR := «exec:7»; (let keysetExpressionIR : SpecTec.keysetExpressionIR := «eval:3»; (.bind (.call ⟨SpecTec.tableActionReferenceIR, SpecTecCall.«$tableObject_create_entry_action» EC (tableObjectProperty.ACTIONS TBL) tableActionInterface⟩) (fun («exec:8» : SpecTec.tableActionReferenceIR) => (let «eval:4» : SpecTec.tableActionReferenceIR := «exec:8»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «eval:4»; (let tableEntryIR_update : tableEntryIR := ((tableEntryIR.«% % % ':' % % ';'» ((_root_.Option.none) : (_root_.Option constIR)) tableEntryPriorityOptIR keysetExpressionIR tableActionReferenceIR ((SpecTec.annotationList._EMPTY) : SpecTec.annotationList)) : tableEntryIR); (match (tableObjectProperty.ENTRIES TBL) with | .«% % ENTRIES '=' `{ % `}» «exec:9» «exec:10» «exec:11» => (let annotationList : SpecTec.annotationList := «exec:9»; (let constOptIR : SpecTec.constOptIR := «exec:10»; (let «tableEntryIR*» : (_root_.List tableEntryIR) := «exec:11»; (let tableEntriesPropertyIR_updated : tableEntriesPropertyIR := ((tableEntriesPropertyIR.«% % ENTRIES '=' `{ % `}» annotationList constOptIR («tableEntryIR*» ++ ([tableEntryIR_update] : (_root_.List tableEntryIR)))) : tableEntriesPropertyIR); (let TBL_updated : tableObjectProperty := ({ TBL with ENTRIES := tableEntriesPropertyIR_updated } : tableObjectProperty); (.pure (((_root_.Option.some ((tableObject.«TABLE % `{ % % `}» typeId frame TBL_updated) : tableObject)) : (_root_.Option tableObject)))))))))))))))))))))))))))))))))))))))


noncomputable def «$tableObject_add_entry:clause:1» (input0 : evalContext) (input1 : tableObject) (input2 : SpecTec.tableEntryPriorityInterface) (input3 : SpecTec.tableKeysetInterface) (input4 : SpecTec.tableActionInterface) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let EC : evalContext := input0; (match input1 with | .«TABLE % `{ % % `}» «exec:1» «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:1»; (let frame : SpecTec.frame := «exec:2»; (let TBL : tableObjectProperty := «exec:3»; (let tableEntryPriorityInterface : SpecTec.tableEntryPriorityInterface := input2; (let tableKeysetInterface : SpecTec.tableKeysetInterface := input3; (let tableActionInterface : SpecTec.tableActionInterface := input4; (.pure ((((_root_.Option.none) : (_root_.Option tableObject)) : (_root_.Option tableObject))))))))))))


noncomputable def «$tableObject_add_entry_clauses» (input0 : evalContext) (input1 : tableObject) (input2 : tableEntryPriorityInterface) (input3 : tableKeysetInterface) (input4 : tableActionInterface) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_add_entry:clause:0»  input0 input1 input2 input3 input4), fun (_ : _root_.Unit) => («$tableObject_add_entry:clause:1»  input0 input1 input2 input3 input4)]


noncomputable def «$tableObject_add_default_action:clause:0» (input0 : evalContext) (input1 : tableObject) (input2 : SpecTec.tableActionInterface) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let EC : evalContext := input0; (match input1 with | .«TABLE % `{ % % `}» «exec:1» «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:1»; (let frame : SpecTec.frame := «exec:2»; (let TBL : tableObjectProperty := «exec:3»; (let tableActionInterface : SpecTec.tableActionInterface := input2; (match (tableObjectProperty.DEFAULT_ACTION TBL) with | .«% % DEFAULT_ACTION '=' % ';'» «exec:4» «exec:5» «exec:6» => (let _annotationList : annotationList := «exec:4»; (let constIR? : (_root_.Option constIR) := «exec:5»; (let _tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:6»; (.bind (.guard (((_root_.Option.isNone constIR?) = true))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.tableActionReferenceIR, SpecTecCall.«$tableObject_create_entry_action» EC (tableObjectProperty.ACTIONS TBL) tableActionInterface⟩) (fun («exec:7» : SpecTec.tableActionReferenceIR) => (let «eval:0» : SpecTec.tableActionReferenceIR := «exec:7»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «eval:0»; (let tableDefaultActionPropertyIR : SpecTec.tableDefaultActionPropertyIR := ((SpecTec.tableDefaultActionPropertyIR.«% % DEFAULT_ACTION '=' % ';'» ((annotationList._EMPTY) : annotationList) ((_root_.Option.none) : (_root_.Option constIR)) tableActionReferenceIR) : SpecTec.tableDefaultActionPropertyIR); (let TBL_updated : tableObjectProperty := ({ TBL with DEFAULT_ACTION := tableDefaultActionPropertyIR } : tableObjectProperty); (.pure ((((tableObject.«TABLE % `{ % % `}» typeId frame TBL_updated) : tableObject) : tableObject)))))))))))))))))))))


noncomputable def «$tableObject_add_default_action_clauses» (input0 : evalContext) (input1 : tableObject) (input2 : tableActionInterface) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_add_default_action:clause:0»  input0 input1 input2)]


noncomputable def «$update_headerUnion:clause:0» (input0 : (_root_.List fieldValue)) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «fieldValue*» : (_root_.List fieldValue) := input0; (let nameIR : SpecTec.nameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «fieldValue*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue))))))))


noncomputable def «$update_headerUnion:clause:1» (input0 : (_root_.List fieldValue)) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «fieldValue*» : (_root_.List fieldValue) := input0; (let nameIR : SpecTec.nameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «fieldValue*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «fieldValue*» with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field_h : value := «exec:3»; (let nameIR_field_h : SpecTec.nameIR := «exec:4»; (let «fieldValue_t*» : (_root_.List fieldValue) := «exec:1»; (.bind (.guard (nameIR = nameIR_field_h)) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$update_headerUnion» «fieldValue_t*» nameIR⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «eval:0» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value_field_h nameIR_field_h) : fieldValue) :: «eval:0») : (_root_.List fieldValue))))))))))))) | [] => .unmatch)))))


noncomputable def «$update_headerUnion:clause:2» (input0 : (_root_.List fieldValue)) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «fieldValue'*» : (_root_.List fieldValue) := input0; (let nameIR : SpecTec.nameIR := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «fieldValue'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «fieldValue'*» with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field_h : SpecTec.value := «exec:3»; (let nameIR_field_h : SpecTec.nameIR := «exec:4»; (let «fieldValue_t*» : (_root_.List fieldValue) := «exec:1»; (.bind (.guard ((nameIR_field_h ≠ nameIR))) (fun (_ : Unit) => (let value : SpecTec.value := value_field_h; (.bind (.guard (((«sub:value:headerValue» value) = true))) (fun (_ : Unit) => (match («$update_headerUnion:case_3:downcast:0» value) with | some «exec:5» => (let «eval:0» : headerValue := «exec:5»; (match «eval:0» with | .«HEADER % `{ % ';' % `}» «exec:6» «exec:7» «exec:8» => (let typeId : SpecTec.typeId := «exec:6»; (let _b : _root_.Bool := «exec:7»; (let «fieldValue*» : (_root_.List fieldValue) := «exec:8»; (let value_field_h_update : SpecTec.value := ((SpecTec.value.«HEADER % `{ % ';' % `}» typeId false «fieldValue*») : SpecTec.value); (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$update_headerUnion» «fieldValue_t*» nameIR⟩) (fun («exec:9» : (_root_.List fieldValue)) => (let «eval:1» : (_root_.List fieldValue) := «exec:9»; (.pure (((((fieldValue.«% % ';'» value_field_h_update nameIR_field_h) : fieldValue) :: «eval:1») : (_root_.List fieldValue))))))))))))) | none => .unmatch)))))))))) | [] => .unmatch)))))


noncomputable def «$update_headerUnion_clauses» (input0 : (_root_.List fieldValue)) (input1 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_headerUnion:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$update_headerUnion:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$update_headerUnion:clause:2»  input0 input1)]


noncomputable def «$isValid_header:clause:0» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:headerValue» value) = true))) (fun (_ : Unit) => (match («$isValid_header:case_1:downcast:0» value) with | some «exec:1» => (let «eval:0» : SpecTec.headerValue := «exec:1»; (let headerValue : SpecTec.headerValue := «eval:0»; (match headerValue with | .«HEADER % `{ % ';' % `}» «exec:2» «exec:3» «exec:4» => (let _typeId : typeId := «exec:2»; (let b_valid : _root_.Bool := «exec:3»; (let «_fieldValue*» : (_root_.List fieldValue) := «exec:4»; (.pure ((b_valid : _root_.Bool))))))))) | none => .unmatch))))


noncomputable def «$isValid_header_clauses» (input0 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$isValid_header:clause:0»  input0)]


noncomputable def «$invalidate_value:clause:0» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:headerValue» value) = true))) (fun (_ : Unit) => (match («$invalidate_value:case_1:downcast:0» value) with | some «exec:1» => (let «eval:0» : SpecTec.headerValue := «exec:1»; (let headerValue : SpecTec.headerValue := «eval:0»; (.bind (.call ⟨SpecTec.headerValue, SpecTecCall.«$invalidate_header» headerValue⟩) (fun («exec:2» : SpecTec.headerValue) => (let «eval:1» : SpecTec.headerValue := «exec:2»; (.pure (((«cast:headerValue:value» «eval:1») : SpecTec.value)))))))) | none => .unmatch))))


noncomputable def «$invalidate_value:clause:1» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:headerUnionValue» value) = true))) (fun (_ : Unit) => (match («$invalidate_value:case_2:downcast:0» value) with | some «exec:1» => (let «eval:0» : SpecTec.headerUnionValue := «exec:1»; (let headerUnionValue : SpecTec.headerUnionValue := «eval:0»; (.bind (.call ⟨SpecTec.headerUnionValue, SpecTecCall.«$invalidate_headerUnion» headerUnionValue⟩) (fun («exec:2» : SpecTec.headerUnionValue) => (let «eval:1» : SpecTec.headerUnionValue := «exec:2»; (.pure (((«cast:headerUnionValue:value» «eval:1») : SpecTec.value)))))))) | none => .unmatch))))


noncomputable def «$invalidate_value_clauses» (input0 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$invalidate_value:clause:0»  input0), fun (_ : _root_.Unit) => («$invalidate_value:clause:1»  input0)]


noncomputable def «$invalidate_headerUnion:clause:0» (input0 : headerUnionValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«HEADER_UNION % `{ % `}» «exec:1» «exec:2» => (let typeId : SpecTec.typeId := «exec:1»; (let «eval:1» : (_root_.List fieldValue) := «exec:2»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$invalidate_headerUnion:case_1:pattern-iter:0» «eval:1»⟩) (fun («exec:3» : ((_root_.List nameIR) × (_root_.List value))) => (let «nameIR_field*» : (_root_.List nameIR) := («exec:3»).1; (let «value_field*» : (_root_.List value) := («exec:3»).2; (.bind (.call ⟨(_root_.List value), SpecTecCall.«$invalidate_headerUnion:case_1:iter:2» «value_field*»⟩) (fun («exec:4» : (_root_.List value)) => (let «value_field_invalidated*» : (_root_.List value) := «exec:4»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$invalidate_headerUnion:case_1:iter:4» «nameIR_field*» «value_field_invalidated*»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «eval:5» : (_root_.List fieldValue) := «exec:5»; (.pure ((((headerUnionValue.«HEADER_UNION % `{ % `}» typeId «eval:5») : headerUnionValue) : headerUnionValue))))))))))))))))


noncomputable def «$invalidate_headerUnion_clauses» (input0 : headerUnionValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$invalidate_headerUnion:clause:0»  input0)]


noncomputable def «$invalidate_headerUnion:case_1:iter:2:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «$invalidate_headerUnion:case_1:iter:2:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_field : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (.bind (.call ⟨value, SpecTecCall.«$invalidate_value» value_field⟩) (fun («exec:3» : value) => (let «eval:3» : value := «exec:3»; (let value_field_invalidated : value := «eval:3»; (.bind (.call ⟨(_root_.List value), SpecTecCall.«$invalidate_headerUnion:case_1:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:4»; (.pure (((value_field_invalidated :: «tail:1») : (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «$invalidate_headerUnion:case_1:iter:2_clauses» (input0 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$invalidate_headerUnion:case_1:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$invalidate_headerUnion:case_1:iter:2:clause:1»  input0)]


noncomputable def «Call_eval:cont:iter:5:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «Call_eval:cont:iter:5:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_front : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (.bind (.call ⟨value, SpecTecCall.«$invalidate_value» value_front⟩) (fun («exec:3» : value) => (let «eval:6» : value := «exec:3»; (let value_front_invalidated : value := «eval:6»; (.bind (.call ⟨(_root_.List value), SpecTecCall.«Call_eval:cont:iter:5» «tail:0»⟩) (fun («exec:4» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:4»; (.pure (((value_front_invalidated :: «tail:1») : (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Call_eval:cont:iter:5_clauses» (input0 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:cont:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Call_eval:cont:iter:5:clause:1»  input0)]


noncomputable def «Call_eval:cont-overflow:iter:5:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «Call_eval:cont-overflow:iter:5:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_element : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (.bind (.call ⟨value, SpecTecCall.«$invalidate_value» value_element⟩) (fun («exec:3» : value) => (let «eval:6» : value := «exec:3»; (let value_element_updated : value := «eval:6»; (.bind (.call ⟨(_root_.List value), SpecTecCall.«Call_eval:cont-overflow:iter:5» «tail:0»⟩) (fun («exec:4» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:4»; (.pure (((value_element_updated :: «tail:1») : (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Call_eval:cont-overflow:iter:5_clauses» (input0 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:cont-overflow:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Call_eval:cont-overflow:iter:5:clause:1»  input0)]


noncomputable def «Call_eval:cont_2:iter:5:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «Call_eval:cont_2:iter:5:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_back : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (.bind (.call ⟨value, SpecTecCall.«$invalidate_value» value_back⟩) (fun («exec:3» : value) => (let «eval:6» : value := «exec:3»; (let value_back_invalidated : value := «eval:6»; (.bind (.call ⟨(_root_.List value), SpecTecCall.«Call_eval:cont_2:iter:5» «tail:0»⟩) (fun («exec:4» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:4»; (.pure (((value_back_invalidated :: «tail:1») : (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Call_eval:cont_2:iter:5_clauses» (input0 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:cont_2:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Call_eval:cont_2:iter:5:clause:1»  input0)]


noncomputable def «Call_eval:cont-overflow_2:iter:5:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «Call_eval:cont-overflow_2:iter:5:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_element : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (.bind (.call ⟨value, SpecTecCall.«$invalidate_value» value_element⟩) (fun («exec:3» : value) => (let «eval:6» : value := «exec:3»; (let value_element_updated : value := «eval:6»; (.bind (.call ⟨(_root_.List value), SpecTecCall.«Call_eval:cont-overflow_2:iter:5» «tail:0»⟩) (fun («exec:4» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:4»; (.pure (((value_element_updated :: «tail:1») : (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Call_eval:cont-overflow_2:iter:5_clauses» (input0 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:cont-overflow_2:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Call_eval:cont-overflow_2:iter:5:clause:1»  input0)]


noncomputable def «Call_eval:builtinIsValidMethodCallee-header-union:iter:3:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)

end SpecTec
