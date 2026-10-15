import SpecTecDecl0227

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$select_action:case_4:iter:0:clause:0» (input0 : (_root_.List tableMatch)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List (_root_.Option _root_.Nat))), ([] : (_root_.List tableActionReferenceIR))) : ((_root_.List (_root_.Option _root_.Nat)) × (_root_.List tableActionReferenceIR))))) | _ :: _ => .unmatch)


noncomputable def «$select_action:case_4:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableMatch)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableMatch : SpecTec.tableMatch := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableMatch) := «exec:1»; (match tableMatch with | .«% ':' %» «exec:3» «exec:4» => (let nat? : (_root_.Option _root_.Nat) := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (.bind (.call ⟨((_root_.List (_root_.Option _root_.Nat)) × (_root_.List SpecTec.tableActionReferenceIR)), SpecTecCall.«$select_action:case_4:iter:0» «tail:0»⟩) (fun («exec:5» : ((_root_.List (_root_.Option _root_.Nat)) × (_root_.List SpecTec.tableActionReferenceIR))) => (let «tail:1» : (_root_.List (_root_.Option _root_.Nat)) := («exec:5»).1; (let «tail:2» : (_root_.List SpecTec.tableActionReferenceIR) := («exec:5»).2; (.pure ((((nat? :: «tail:1»), (tableActionReferenceIR :: «tail:2»)) : ((_root_.List (_root_.Option _root_.Nat)) × (_root_.List SpecTec.tableActionReferenceIR)))))))))))))) | [] => .unmatch)


noncomputable def «$select_action:case_4:iter:0_clauses» (input0 : (_root_.List tableMatch)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$select_action:case_4:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$select_action:case_4:iter:0:clause:1»  input0)]


noncomputable def «$select_action:case_4:iter:1:clause:0» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$select_action:case_4:iter:1:clause:1» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nat? : (_root_.Option _root_.Nat) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option _root_.Nat)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome nat?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$select_action:case_4:iter:1» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «$select_action:case_4:iter:1_clauses» (input0 : (_root_.List (_root_.Option _root_.Nat))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$select_action:case_4:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$select_action:case_4:iter:1:clause:1»  input0)]


noncomputable def «$select_action:case_4:iter:2:clause:0» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Nat)) : (_root_.List _root_.Nat)))) | _ :: _ => .unmatch)


noncomputable def «$select_action:case_4:iter:2:clause:1» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nat? : (_root_.Option _root_.Nat) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option _root_.Nat)) := «exec:1»; (match nat? with | some «exec:3» => (let n_priority : _root_.Nat := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$select_action:case_4:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Nat)) => (let «tail:1» : (_root_.List _root_.Nat) := «exec:4»; (.pure (((n_priority :: «tail:1») : (_root_.List _root_.Nat)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «$select_action:case_4:iter:2_clauses» (input0 : (_root_.List (_root_.Option _root_.Nat))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$select_action:case_4:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$select_action:case_4:iter:2:clause:1»  input0)]


noncomputable def «$select_action:case_4:iter:3:clause:0» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List tableActionReferenceIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.Nat × tableActionReferenceIR))) : (_root_.List (_root_.Nat × tableActionReferenceIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$select_action:case_4:iter:3:clause:1» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List SpecTec.tableActionReferenceIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let n_priority : _root_.Nat := «exec:2»; (let «tail:0» : (_root_.List _root_.Nat) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.tableActionReferenceIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.Nat × SpecTec.tableActionReferenceIR)), SpecTecCall.«$select_action:case_4:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.Nat × SpecTec.tableActionReferenceIR))) => (let «tail:2» : (_root_.List (_root_.Nat × SpecTec.tableActionReferenceIR)) := «exec:5»; (.pure ((((n_priority, tableActionReferenceIR) :: «tail:2») : (_root_.List (_root_.Nat × SpecTec.tableActionReferenceIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$select_action:case_4:iter:3_clauses» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List tableActionReferenceIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$select_action:case_4:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$select_action:case_4:iter:3:clause:1»  input0 input1)]


noncomputable def «$select_action:case_4:pattern-iter:5:clause:0» (input0 : (_root_.List (_root_.Nat × tableActionReferenceIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List _root_.Nat)), ([] : (_root_.List tableActionReferenceIR))) : ((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR))))) | _ :: _ => .unmatch)


noncomputable def «$select_action:case_4:pattern-iter:5:clause:1» (input0 : (_root_.List (_root_.Nat × tableActionReferenceIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let n_priority_sorted : _root_.Nat := («exec:2»).1; (let tableActionReferenceIR_sorted : tableActionReferenceIR := («exec:2»).2; (let «pattern-tail:0» : (_root_.List (_root_.Nat × tableActionReferenceIR)) := «exec:1»; (.bind (.call ⟨((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR)), SpecTecCall.«$select_action:case_4:pattern-iter:5» «pattern-tail:0»⟩) (fun («exec:3» : ((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR))) => (let «pattern-tail:1» : (_root_.List _root_.Nat) := («exec:3»).1; (let «pattern-tail:2» : (_root_.List tableActionReferenceIR) := («exec:3»).2; (.pure ((((n_priority_sorted :: «pattern-tail:1»), (tableActionReferenceIR_sorted :: «pattern-tail:2»)) : ((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR)))))))))))) | [] => .unmatch)


noncomputable def «$select_action:case_4:pattern-iter:5_clauses» (input0 : (_root_.List (_root_.Nat × tableActionReferenceIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$select_action:case_4:pattern-iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («$select_action:case_4:pattern-iter:5:clause:1»  input0)]


noncomputable def «$reverse_bytes_of_hex':clause:0» (input0 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (.guard (((_root_.String.utf8ByteSize t) ≤ (2 : _root_.Nat)))) (fun (_ : Unit) => (.pure ((t : _root_.String))))))


noncomputable def «$reverse_bytes_of_hex':clause:1» (input0 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let n_len : _root_.Nat := (_root_.String.utf8ByteSize t); (.bind (.guard ((n_len > (2 : _root_.Nat)))) (fun (_ : Unit) => (.bind (SpecTecExecution.require ((((0 : _root_.Nat) + (2 : _root_.Nat)) ≤ (_root_.String.utf8ByteSize t))) "slice out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextSliceValid t (0 : _root_.Nat) (2 : _root_.Nat))) "text result is not valid UTF-8") (fun (_ : Unit) => (let t_byte : _root_.String := (_root_.specTecTextSlice t (0 : _root_.Nat) (2 : _root_.Nat)); (let i : _root_.Int := ((_root_.Int.ofNat n_len) - (_root_.Int.ofNat (2 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let n_len_bytes : _root_.Nat := (_root_.Int.toNat i); (.bind (SpecTecExecution.require ((((2 : _root_.Nat) + n_len_bytes) ≤ (_root_.String.utf8ByteSize t))) "slice out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextSliceValid t (2 : _root_.Nat) n_len_bytes)) "text result is not valid UTF-8") (fun (_ : Unit) => (let t_bytes : _root_.String := (_root_.specTecTextSlice t (2 : _root_.Nat) n_len_bytes); (.bind (.call ⟨_root_.String, SpecTecCall.«$reverse_bytes_of_hex'» t_bytes⟩) (fun («exec:1» : _root_.String) => (let «eval:0» : _root_.String := «exec:1»; (let t_bytes_rev : _root_.String := «eval:0»; (.pure (((t_bytes_rev ++ t_byte) : _root_.String)))))))))))))))))))))))))))


noncomputable def «$reverse_bytes_of_hex'_clauses» (input0 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$reverse_bytes_of_hex':clause:0»  input0), fun (_ : _root_.Unit) => («$reverse_bytes_of_hex':clause:1»  input0)]


noncomputable def «$reverse_bytes_of_hex:clause:0» (input0 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (.bind (SpecTecExecution.require ((((0 : _root_.Nat) + (2 : _root_.Nat)) ≤ (_root_.String.utf8ByteSize t))) "slice out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextSliceValid t (0 : _root_.Nat) (2 : _root_.Nat))) "text result is not valid UTF-8") (fun (_ : Unit) => (.bind (.guard ("0x" = (_root_.specTecTextSlice t (0 : _root_.Nat) (2 : _root_.Nat)))) (fun (_ : Unit) => (let n_len : _root_.Nat := (_root_.String.utf8ByteSize t); (let i : _root_.Int := ((_root_.Int.ofNat n_len) - (_root_.Int.ofNat (2 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let n_len_bytes : _root_.Nat := (_root_.Int.toNat i); (.bind (SpecTecExecution.require ((((2 : _root_.Nat) + n_len_bytes) ≤ (_root_.String.utf8ByteSize t))) "slice out of bounds") (fun (_ : Unit) => (.bind (SpecTecExecution.require ((_root_.specTecTextSliceValid t (2 : _root_.Nat) n_len_bytes)) "text result is not valid UTF-8") (fun (_ : Unit) => (.bind (.call ⟨_root_.String, SpecTecCall.«$reverse_bytes_of_hex'» (_root_.specTecTextSlice t (2 : _root_.Nat) n_len_bytes)⟩) (fun («exec:1» : _root_.String) => (let «eval:0» : _root_.String := «exec:1»; (.pure ((("0x" ++ «eval:0») : _root_.String))))))))))))))))))))))))


noncomputable def «$reverse_bytes_of_hex_clauses» (input0 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$reverse_bytes_of_hex:clause:0»  input0)]


noncomputable def «$tableObject_create_entry_priority:clause:0» (input0 : tableEntryPriorityInterface) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let i? : (_root_.Option _root_.Int) := input0; (.bind (.guard (((_root_.Option.isNone i?) = true))) (fun (_ : Unit) => (.pure ((((_root_.Option.none) : (_root_.Option tableEntryPriorityIR)) : tableEntryPriorityOptIR))))))


noncomputable def «$tableObject_create_entry_priority:clause:1» (input0 : SpecTec.tableEntryPriorityInterface) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableEntryPriorityInterface : SpecTec.tableEntryPriorityInterface := input0; (.bind (.guard (((_root_.Option.isSome tableEntryPriorityInterface) = true))) (fun (_ : Unit) => (match tableEntryPriorityInterface with | some «exec:1» => (let i : _root_.Int := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let n_priority : _root_.Nat := (_root_.Int.toNat i); (.pure (((_root_.Option.some ((tableEntryPriorityIR.«PRIORITY '=' % ':'» ((integerLiteral.D (_root_.Int.ofNat n_priority)) : integerLiteral)) : tableEntryPriorityIR)) : tableEntryPriorityOptIR))))))))) | none => .unmatch))))


noncomputable def «$tableObject_create_entry_priority_clauses» (input0 : tableEntryPriorityInterface) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_priority:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_priority:clause:1»  input0)]


noncomputable def «$needs_priority_tableKeysPropertyIR:case_1:iter:0:clause:0» (input0 : (_root_.List tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), (([] : (_root_.List typedExpressionIR)), ([] : (_root_.List nameIR))))) : ((_root_.List annotationList) × ((_root_.List nameIR) × ((_root_.List typedExpressionIR) × (_root_.List nameIR))))))) | _ :: _ => .unmatch)


noncomputable def «$needs_priority_tableKeysPropertyIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyIR : SpecTec.tableKeyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyIR) := «exec:1»; (match tableKeyIR with | .«% '#' % ':' % % ';'» «exec:3» «exec:4» «exec:5» «exec:6» => (let _typedExpressionIR : typedExpressionIR := «exec:3»; (let _nameIR : nameIR := «exec:4»; (let nameIR_matchKind : nameIR := «exec:5»; (let _annotationList : annotationList := «exec:6»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × ((_root_.List typedExpressionIR) × (_root_.List nameIR)))), SpecTecCall.«$needs_priority_tableKeysPropertyIR:case_1:iter:0» «tail:0»⟩) (fun («exec:7» : ((_root_.List annotationList) × ((_root_.List nameIR) × ((_root_.List typedExpressionIR) × (_root_.List nameIR))))) => (let «tail:1» : (_root_.List annotationList) := («exec:7»).1; (let «tail:2» : (_root_.List nameIR) := ((«exec:7»).2).1; (let «tail:3» : (_root_.List typedExpressionIR) := (((«exec:7»).2).2).1; (let «tail:4» : (_root_.List nameIR) := (((«exec:7»).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_nameIR :: «tail:2»), ((_typedExpressionIR :: «tail:3»), (nameIR_matchKind :: «tail:4»)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × ((_root_.List typedExpressionIR) × (_root_.List nameIR)))))))))))))))))))) | [] => .unmatch)


noncomputable def «$needs_priority_tableKeysPropertyIR:case_1:iter:0_clauses» (input0 : (_root_.List tableKeyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$needs_priority_tableKeysPropertyIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$needs_priority_tableKeysPropertyIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$needs_priority_tableKeysPropertyIR:case_1:iter:1:clause:0» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$needs_priority_tableKeysPropertyIR:case_1:iter:1:clause:1» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_matchKind : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$needs_priority_tableKeysPropertyIR:case_1:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((_root_.Decidable.decide (nameIR_matchKind = "ternary")) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$needs_priority_tableKeysPropertyIR:case_1:iter:1_clauses» (input0 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$needs_priority_tableKeysPropertyIR:case_1:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$needs_priority_tableKeysPropertyIR:case_1:iter:1:clause:1»  input0)]


noncomputable def «$needs_priority_tableKeysPropertyIR:clause:0» (input0 : tableKeysPropertyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«KEY '=' `{ % `}» «exec:1» => (let «tableKeyIR*» : (_root_.List tableKeyIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × ((_root_.List typedExpressionIR) × (_root_.List nameIR)))), SpecTecCall.«$needs_priority_tableKeysPropertyIR:case_1:iter:0» «tableKeyIR*»⟩) (fun («exec:2» : ((_root_.List annotationList) × ((_root_.List nameIR) × ((_root_.List typedExpressionIR) × (_root_.List nameIR))))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:2»).1; (let «_nameIR*» : (_root_.List nameIR) := ((«exec:2»).2).1; (let «_typedExpressionIR*» : (_root_.List typedExpressionIR) := (((«exec:2»).2).2).1; (let «nameIR_matchKind*» : (_root_.List nameIR) := (((«exec:2»).2).2).2; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$needs_priority_tableKeysPropertyIR:case_1:iter:1» «nameIR_matchKind*»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «eval:2» : (_root_.List _root_.Bool) := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$exists_» «eval:2»⟩) (fun («exec:4» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:4»; (.pure ((«eval:3» : _root_.Bool)))))))))))))))))


noncomputable def «$needs_priority_tableKeysPropertyIR_clauses» (input0 : tableKeysPropertyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$needs_priority_tableKeysPropertyIR:clause:0»  input0)]


noncomputable def «$tableObject_create_entry_keys:case_2:pattern-iter:0:clause:0» (input0 : (_root_.List (_root_.String × (_root_.String × typeIR)))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)

end SpecTec
