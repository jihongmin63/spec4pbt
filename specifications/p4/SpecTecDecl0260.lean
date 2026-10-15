import SpecTecDecl0259

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$int_of_integerValue:clause:1» (input0 : SpecTec.integerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerValue : SpecTec.integerValue := input0; (.bind (.guard (((«sub:integerValue:integerLiteral» integerValue) = true))) (fun (_ : Unit) => (match («$int_of_integerValue:case_2:downcast:0» integerValue) with | some «exec:1» => (let «eval:0» : SpecTec.integerLiteral := «exec:1»; (let integerLiteral : SpecTec.integerLiteral := «eval:0»; (.bind (.guard (((«exec:match:integerLiteral:% S %» integerLiteral) = true))) (fun (_ : Unit) => (match integerLiteral with | .«% S %» «exec:2» «exec:3» => (let w : _root_.Nat := «exec:2»; (let i : _root_.Int := «exec:3»; (.bind (.call ⟨_root_.Int, SpecTecCall.«$bitstr_to_int» (_root_.Int.ofNat w) i⟩) (fun («exec:4» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:4»; (.pure ((«eval:1» : _root_.Int)))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$int_of_integerValue:clause:2» (input0 : SpecTec.integerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerValue : SpecTec.integerValue := input0; (.bind (.guard (((«sub:integerValue:integerLiteral» integerValue) = true))) (fun (_ : Unit) => (match («$int_of_integerValue:case_3:downcast:0» integerValue) with | some «exec:1» => (let «eval:0» : SpecTec.integerLiteral := «exec:1»; (let integerLiteral : SpecTec.integerLiteral := «eval:0»; (.bind (.guard (((«exec:match:integerLiteral:% W %» integerLiteral) = true))) (fun (_ : Unit) => (match integerLiteral with | .«% W %» «exec:2» «exec:3» => (let w : _root_.Nat := «exec:2»; (let i : _root_.Int := «exec:3»; (.pure ((i : _root_.Int))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$int_of_integerValue:clause:3» (input0 : SpecTec.integerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerValue : SpecTec.integerValue := input0; (.bind (.guard (((«exec:match:integerValue:% '.' % V %» integerValue) = true))) (fun (_ : Unit) => (match integerValue with | .«% '.' % V %» «exec:1» «exec:2» «exec:3» => (let _nat : _root_.Nat := «exec:1»; (let _nat' : _root_.Nat := «exec:2»; (let i : _root_.Int := «exec:3»; (.pure ((i : _root_.Int)))))) | _ => .unmatch))))


noncomputable def «$int_of_integerValue_clauses» (input0 : integerValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$int_of_integerValue:clause:0»  input0), fun (_ : _root_.Unit) => («$int_of_integerValue:clause:1»  input0), fun (_ : _root_.Unit) => («$int_of_integerValue:clause:2»  input0), fun (_ : _root_.Unit) => («$int_of_integerValue:clause:3»  input0)]


noncomputable def «$nat_of_integerValue:clause:0» (input0 : SpecTec.integerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerValue : SpecTec.integerValue := input0; (.bind (.call ⟨_root_.Int, SpecTecCall.«$int_of_integerValue» integerValue⟩) (fun («exec:1» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:1»; (let i : _root_.Int := «eval:0»; (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let n : _root_.Nat := (_root_.Int.toNat i); (.pure (((_root_.Option.some n) : (_root_.Option _root_.Nat))))))))))))))


noncomputable def «$nat_of_integerValue:clause:1» (input0 : SpecTec.integerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerValue : SpecTec.integerValue := input0; (.pure ((((_root_.Option.none) : (_root_.Option _root_.Nat)) : (_root_.Option _root_.Nat)))))


noncomputable def «$nat_of_integerValue_clauses» (input0 : integerValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nat_of_integerValue:clause:0»  input0), fun (_ : _root_.Unit) => («$nat_of_integerValue:clause:1»  input0)]


noncomputable def «$set_priorities_of_tableEntryListIR':clause:0» (input0 : tableContext) (input1 : _root_.Nat) (input2 : (_root_.List tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let n_last : _root_.Nat := input1; (let «tableEntryIR*» : (_root_.List tableEntryIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableEntryIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List tableEntryIR)) : (_root_.List tableEntryIR)))))))))


noncomputable def «$set_priorities_of_tableEntryListIR':clause:1» (input0 : tableContext) (input1 : _root_.Nat) (input2 : (_root_.List tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let n_last : _root_.Nat := input1; (let «tableEntryIR*» : (_root_.List tableEntryIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableEntryIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableEntryIR*» with | «exec:2» :: «exec:1» => (let tableEntryIR_h : tableEntryIR := «exec:2»; (let «tableEntryIR_t*» : (_root_.List tableEntryIR) := «exec:1»; (.bind (.call ⟨tableEntryPriorityOptIR, SpecTecCall.«$tableEntryPriorityOptIR_of_tableEntryIR» tableEntryIR_h⟩) (fun («exec:3» : tableEntryPriorityOptIR) => (let «eval:0» : tableEntryPriorityOptIR := «exec:3»; (match «eval:0» with | none => (let b_lw : _root_.Bool := (matchPriority.LARGEST_WINS (tableContext.PRIORITIES TBLC)); (let n_delta : _root_.Nat := (matchPriority.DELTA (tableContext.PRIORITIES TBLC)); (.bind (.call ⟨_root_.Int, SpecTecCall.«$ite» _root_.Int b_lw ((_root_.Int.ofNat n_last) - (_root_.Int.ofNat n_delta)) (_root_.Int.ofNat (n_last + n_delta))⟩) (fun («exec:4» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:4»; (let i : _root_.Int := «eval:1»; (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let n : _root_.Nat := (_root_.Int.toNat i); (.bind (.call ⟨tableEntryIR, SpecTecCall.«$set_priority_of_tableEntryIR» tableEntryIR_h n⟩) (fun («exec:5» : tableEntryIR) => (let «eval:2» : tableEntryIR := «exec:5»; (let tableEntryIR_h_updated : tableEntryIR := «eval:2»; (.bind (.call ⟨(_root_.List tableEntryIR), SpecTecCall.«$set_priorities_of_tableEntryListIR'» TBLC n «tableEntryIR_t*»⟩) (fun («exec:6» : (_root_.List tableEntryIR)) => (let «eval:3» : (_root_.List tableEntryIR) := «exec:6»; (let «tableEntryIR_t_updated*» : (_root_.List tableEntryIR) := «eval:3»; (.pure (((tableEntryIR_h_updated :: «tableEntryIR_t_updated*») : (_root_.List tableEntryIR))))))))))))))))))))))) | some _ => .unmatch)))))) | [] => .unmatch))))))


noncomputable def «$set_priorities_of_tableEntryListIR':clause:2» (input0 : tableContext) (input1 : _root_.Nat) (input2 : (_root_.List tableEntryIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let n_last : _root_.Nat := input1; (let «tableEntryIR*» : (_root_.List tableEntryIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableEntryIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableEntryIR*» with | «exec:2» :: «exec:1» => (let tableEntryIR_h : tableEntryIR := «exec:2»; (let «tableEntryIR_t*» : (_root_.List tableEntryIR) := «exec:1»; (.bind (.call ⟨SpecTec.tableEntryPriorityOptIR, SpecTecCall.«$tableEntryPriorityOptIR_of_tableEntryIR» tableEntryIR_h⟩) (fun («exec:3» : SpecTec.tableEntryPriorityOptIR) => (let «eval:0» : SpecTec.tableEntryPriorityOptIR := «exec:3»; (let tableEntryPriorityOptIR : SpecTec.tableEntryPriorityOptIR := «eval:0»; (.bind (.guard (((_root_.Option.isSome tableEntryPriorityOptIR) = true))) (fun (_ : Unit) => (match tableEntryPriorityOptIR with | some «exec:4» => (match «exec:4» with | .«PRIORITY '=' % ':'» «exec:5» => (let integerLiteral : SpecTec.integerLiteral := «exec:5»; (.bind (.call ⟨(_root_.Option _root_.Nat), SpecTecCall.«$nat_of_integerValue» («cast:integerLiteral:integerValue» integerLiteral)⟩) (fun («exec:6» : (_root_.Option _root_.Nat)) => (let «eval:1» : (_root_.Option _root_.Nat) := «exec:6»; (let nat? : (_root_.Option _root_.Nat) := «eval:1»; (.bind (.guard (((_root_.Option.isSome nat?) = true))) (fun (_ : Unit) => (match nat? with | some «exec:7» => (let n : _root_.Nat := «exec:7»; (.bind (.call ⟨tableEntryIR, SpecTecCall.«$set_priority_of_tableEntryIR» tableEntryIR_h n⟩) (fun («exec:8» : tableEntryIR) => (let «eval:2» : tableEntryIR := «exec:8»; (let tableEntryIR_h_updated : tableEntryIR := «eval:2»; (.bind (.call ⟨(_root_.List tableEntryIR), SpecTecCall.«$set_priorities_of_tableEntryListIR'» TBLC n «tableEntryIR_t*»⟩) (fun («exec:9» : (_root_.List tableEntryIR)) => (let «eval:3» : (_root_.List tableEntryIR) := «exec:9»; (let «tableEntryIR_t_updated*» : (_root_.List tableEntryIR) := «eval:3»; (.pure (((tableEntryIR_h_updated :: «tableEntryIR_t_updated*») : (_root_.List tableEntryIR))))))))))))) | none => .unmatch))))))))) | none => .unmatch))))))))) | [] => .unmatch))))))


noncomputable def «$set_priorities_of_tableEntryListIR'_clauses» (input0 : tableContext) (input1 : _root_.Nat) (input2 : (_root_.List tableEntryIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR':clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR':clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR':clause:2»  input0 input1 input2)]


noncomputable def «$set_priorities_of_tableEntryListIR:clause:0» (input0 : tableContext) (input1 : (_root_.List tableEntryState)) (input2 : tableEntryListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let «TBLS*» : (_root_.List tableEntryState) := input1; (let «tableEntryIR*» : (_root_.List tableEntryIR) := input2; (.bind (.guard (((matchMode.NONE) : matchMode) = (tableContext.MODE TBLC))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_1:iter:0» «tableEntryIR*»⟩) (fun («exec:1» : _root_.Unit) => (.pure ((«tableEntryIR*» : tableEntryListIR))))))))))


noncomputable def «$set_priorities_of_tableEntryListIR:clause:1» (input0 : tableContext) (input1 : (_root_.List tableEntryState)) (input2 : tableEntryListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let «TBLS*» : (_root_.List tableEntryState) := input1; (let «tableEntryIR*» : (_root_.List tableEntryIR) := input2; (let matchMode : SpecTec.matchMode := (tableContext.MODE TBLC); (.bind (.guard (((«exec:match:matchMode:LPM» matchMode) = true))) (fun (_ : Unit) => (match matchMode with | .LPM «exec:1» => (let n : _root_.Nat := «exec:1»; (.bind (.call ⟨(_root_.List tableEntryState), SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:0» «TBLS*»⟩) (fun («exec:2» : (_root_.List tableEntryState)) => (let «TBLS'*» : (_root_.List tableEntryState) := «exec:2»; (.bind (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:1» «TBLS'*»⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:2» «TBLS'*»⟩) (fun («exec:4» : (_root_.List _root_.Nat)) => (let «n_prefix*» : (_root_.List _root_.Nat) := «exec:4»; (.bind (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:3» «tableEntryIR*»⟩) (fun («exec:5» : _root_.Unit) => (.bind (.guard ((_root_.List.length «tableEntryIR*») = (_root_.List.length «n_prefix*»))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List tableEntryIR), SpecTecCall.«$set_priorities_of_tableEntryListIR:case_2:iter:5» «n_prefix*» «tableEntryIR*»⟩) (fun («exec:6» : (_root_.List tableEntryIR)) => (let «tableEntryIR_updated*» : (_root_.List tableEntryIR) := «exec:6»; (.pure ((«tableEntryIR_updated*» : tableEntryListIR))))))))))))))))))) | _ => .unmatch)))))))


noncomputable def «$set_priorities_of_tableEntryListIR:clause:2» (input0 : tableContext) (input1 : (_root_.List tableEntryState)) (input2 : tableEntryListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let «TBLS*» : (_root_.List tableEntryState) := input1; (let «tableEntryIR*» : (_root_.List tableEntryIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableEntryIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.guard (((matchMode.PRI) : matchMode) = (tableContext.MODE TBLC))) (fun (_ : Unit) => (.pure ((([] : (_root_.List tableEntryIR)) : tableEntryListIR))))))))))


noncomputable def «$set_priorities_of_tableEntryListIR:clause:3» (input0 : tableContext) (input1 : (_root_.List tableEntryState)) (input2 : tableEntryListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let «TBLS*» : (_root_.List tableEntryState) := input1; (let «tableEntryIR*» : (_root_.List tableEntryIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableEntryIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableEntryIR*» with | «exec:2» :: «exec:1» => (let tableEntryIR_h : tableEntryIR := «exec:2»; (let «tableEntryIR_t*» : (_root_.List tableEntryIR) := «exec:1»; (.bind (.guard (((matchMode.PRI) : matchMode) = (tableContext.MODE TBLC))) (fun (_ : Unit) => (.bind (.call ⟨tableEntryPriorityOptIR, SpecTecCall.«$tableEntryPriorityOptIR_of_tableEntryIR» tableEntryIR_h⟩) (fun («exec:3» : tableEntryPriorityOptIR) => (let «eval:0» : tableEntryPriorityOptIR := «exec:3»; (match «eval:0» with | none => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$set_priorities_of_tableEntryListIR:case_4:iter:1» «tableEntryIR_t*»⟩) (fun («exec:4» : _root_.Unit) => (let b_lw : _root_.Bool := (matchPriority.LARGEST_WINS (tableContext.PRIORITIES TBLC)); (let n_size : _root_.Nat := (matchEntries.SIZE (tableContext.ENTRIES TBLC)); (let n_delta : _root_.Nat := (matchPriority.DELTA (tableContext.PRIORITIES TBLC)); (.bind (.call ⟨_root_.Int, SpecTecCall.«$ite» _root_.Int b_lw ((((_root_.Int.ofNat n_size) - (_root_.Int.ofNat (1 : _root_.Nat))) * (_root_.Int.ofNat n_delta)) + (_root_.Int.ofNat (1 : _root_.Nat))) (_root_.Int.ofNat (1 : _root_.Nat))⟩) (fun («exec:5» : _root_.Int) => (let «eval:3» : _root_.Int := «exec:5»; (let i : _root_.Int := «eval:3»; (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let n : _root_.Nat := (_root_.Int.toNat i); (.bind (.call ⟨tableEntryIR, SpecTecCall.«$set_priority_of_tableEntryIR» tableEntryIR_h n⟩) (fun («exec:6» : tableEntryIR) => (let «eval:4» : tableEntryIR := «exec:6»; (let tableEntryIR_h_updated : tableEntryIR := «eval:4»; (.bind (.call ⟨(_root_.List tableEntryIR), SpecTecCall.«$set_priorities_of_tableEntryListIR'» TBLC n «tableEntryIR_t*»⟩) (fun («exec:7» : (_root_.List tableEntryIR)) => (let «eval:5» : (_root_.List tableEntryIR) := «exec:7»; (let «tableEntryIR_t_updated*» : (_root_.List tableEntryIR) := «eval:5»; (.pure (((tableEntryIR_h_updated :: «tableEntryIR_t_updated*») : tableEntryListIR))))))))))))))))))))))))) | some _ => .unmatch)))))))) | [] => .unmatch))))))


noncomputable def «$set_priorities_of_tableEntryListIR:clause:4» (input0 : tableContext) (input1 : (_root_.List tableEntryState)) (input2 : tableEntryListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let «TBLS*» : (_root_.List tableEntryState) := input1; (let «tableEntryIR*» : (_root_.List tableEntryIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableEntryIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableEntryIR*» with | «exec:2» :: «exec:1» => (let tableEntryIR_h : tableEntryIR := «exec:2»; (let «tableEntryIR_t*» : (_root_.List tableEntryIR) := «exec:1»; (.bind (.guard (((matchMode.PRI) : matchMode) = (tableContext.MODE TBLC))) (fun (_ : Unit) => (.bind (.guard ((¬ ((matchEntries.CONST (tableContext.ENTRIES TBLC)) = true)))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.tableEntryPriorityOptIR, SpecTecCall.«$tableEntryPriorityOptIR_of_tableEntryIR» tableEntryIR_h⟩) (fun («exec:3» : SpecTec.tableEntryPriorityOptIR) => (let «eval:0» : SpecTec.tableEntryPriorityOptIR := «exec:3»; (let tableEntryPriorityOptIR : SpecTec.tableEntryPriorityOptIR := «eval:0»; (.bind (.guard (((_root_.Option.isSome tableEntryPriorityOptIR) = true))) (fun (_ : Unit) => (match tableEntryPriorityOptIR with | some «exec:4» => (match «exec:4» with | .«PRIORITY '=' % ':'» «exec:5» => (let integerLiteral : SpecTec.integerLiteral := «exec:5»; (.bind (.call ⟨(_root_.Option _root_.Nat), SpecTecCall.«$nat_of_integerValue» («cast:integerLiteral:integerValue» integerLiteral)⟩) (fun («exec:6» : (_root_.Option _root_.Nat)) => (let «eval:1» : (_root_.Option _root_.Nat) := «exec:6»; (let nat? : (_root_.Option _root_.Nat) := «eval:1»; (.bind (.guard (((_root_.Option.isSome nat?) = true))) (fun (_ : Unit) => (match nat? with | some «exec:7» => (let n : _root_.Nat := «exec:7»; (.bind (.call ⟨tableEntryIR, SpecTecCall.«$set_priority_of_tableEntryIR» tableEntryIR_h n⟩) (fun («exec:8» : tableEntryIR) => (let «eval:2» : tableEntryIR := «exec:8»; (let tableEntryIR_h_updated : tableEntryIR := «eval:2»; (.bind (.call ⟨(_root_.List tableEntryIR), SpecTecCall.«$set_priorities_of_tableEntryListIR'» TBLC n «tableEntryIR_t*»⟩) (fun («exec:9» : (_root_.List tableEntryIR)) => (let «eval:3» : (_root_.List tableEntryIR) := «exec:9»; (let «tableEntryIR_t_updated*» : (_root_.List tableEntryIR) := «eval:3»; (.pure (((tableEntryIR_h_updated :: «tableEntryIR_t_updated*») : tableEntryListIR)))))))))))) | none => .unmatch))))))))) | none => .unmatch))))))))))))) | [] => .unmatch))))))


noncomputable def «$set_priorities_of_tableEntryListIR_clauses» (input0 : tableContext) (input1 : (_root_.List tableEntryState)) (input2 : tableEntryListIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:clause:3»  input0 input1 input2), fun (_ : _root_.Unit) => («$set_priorities_of_tableEntryListIR:clause:4»  input0 input1 input2)]


noncomputable def «$get_tableEntryPriority:clause:0» (input0 : (_root_.Option tableEntryPriorityIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableEntryPriorityIR? : (_root_.Option tableEntryPriorityIR) := input0; (.bind (.guard (((_root_.Option.isNone tableEntryPriorityIR?) = true))) (fun (_ : Unit) => (.pure ((((_root_.Option.none) : (_root_.Option _root_.Nat)) : (_root_.Option _root_.Nat)))))))


noncomputable def «$get_tableEntryPriority:clause:1» (input0 : (_root_.Option tableEntryPriorityIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableEntryPriorityIR? : (_root_.Option tableEntryPriorityIR) := input0; (.bind (.guard (((_root_.Option.isSome tableEntryPriorityIR?) = true))) (fun (_ : Unit) => (match tableEntryPriorityIR? with | some «exec:1» => (match «exec:1» with | .«PRIORITY '=' % ':'» «exec:2» => (let integerLiteral : SpecTec.integerLiteral := «exec:2»; (.bind (.call ⟨(_root_.Option _root_.Nat), SpecTecCall.«$nat_of_integerValue» («cast:integerLiteral:integerValue» integerLiteral)⟩) (fun («exec:3» : (_root_.Option _root_.Nat)) => (let «eval:0» : (_root_.Option _root_.Nat) := «exec:3»; (let nat? : (_root_.Option _root_.Nat) := «eval:0»; (.bind (.guard (((_root_.Option.isSome nat?) = true))) (fun (_ : Unit) => (match nat? with | some «exec:4» => (let n : _root_.Nat := «exec:4»; (.pure (((_root_.Option.some n) : (_root_.Option _root_.Nat))))) | none => .unmatch))))))))) | none => .unmatch))))


noncomputable def «$get_tableEntryPriority_clauses» (input0 : (_root_.Option tableEntryPriorityIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$get_tableEntryPriority:clause:0»  input0), fun (_ : _root_.Unit) => («$get_tableEntryPriority:clause:1»  input0)]


noncomputable def «$flatten_keysetExpressionIR:clause:0» (input0 : SpecTec.keysetExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let keysetExpressionIR : SpecTec.keysetExpressionIR := input0; (.bind (.guard (((«sub:keysetExpressionIR:simpleKeysetExpressionIR» keysetExpressionIR) = true))) (fun (_ : Unit) => (match («$flatten_keysetExpressionIR:case_1:downcast:0» keysetExpressionIR) with | some «exec:1» => (let «eval:0» : SpecTec.simpleKeysetExpressionIR := «exec:1»; (let simpleKeysetExpressionIR : SpecTec.simpleKeysetExpressionIR := «eval:0»; (.pure ((([simpleKeysetExpressionIR] : (_root_.List SpecTec.simpleKeysetExpressionIR)) : simpleKeysetExpressionListIR))))) | none => .unmatch))))


noncomputable def «$flatten_keysetExpressionIR:clause:1» (input0 : SpecTec.keysetExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let keysetExpressionIR : SpecTec.keysetExpressionIR := input0; (.bind (.guard (((«sub:keysetExpressionIR:tupleKeysetExpressionIR» keysetExpressionIR) = true))) (fun (_ : Unit) => (match («$flatten_keysetExpressionIR:case_2:downcast:0» keysetExpressionIR) with | some «exec:1» => (let «eval:0» : tupleKeysetExpressionIR := «exec:1»; (match «eval:0» with | .«`( % `)» «exec:2» => (let simpleKeysetExpressionListIR : SpecTec.simpleKeysetExpressionListIR := «exec:2»; (.pure ((simpleKeysetExpressionListIR : SpecTec.simpleKeysetExpressionListIR)))))) | none => .unmatch))))


noncomputable def «$flatten_keysetExpressionIR_clauses» (input0 : keysetExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_keysetExpressionIR:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_keysetExpressionIR:clause:1»  input0)]


noncomputable def «$find_local_return_type_t:clause:0» (input0 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let localKind : SpecTec.localKind := (localTypingLayer.KIND (typingContext.LOCAL TC)); (.bind (.guard (((«sub:localKind:definedFunctionLocalKind» localKind) = true))) (fun (_ : Unit) => (match («$find_local_return_type_t:case_1:downcast:0» localKind) with | some «exec:1» => (let «eval:0» : definedFunctionLocalKind := «exec:1»; (match «eval:0» with | .«FUNCTION ':' %» «exec:2» => (let typeIR_ret : typeIR := «exec:2»; (.pure (((_root_.Option.some typeIR_ret) : (_root_.Option typeIR))))))) | none => .unmatch)))))


noncomputable def «$find_local_return_type_t:clause:1» (input0 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let localKind : SpecTec.localKind := (localTypingLayer.KIND (typingContext.LOCAL TC)); (.bind (.guard (((«sub:localKind:externFunctionLocalKind» localKind) = true))) (fun (_ : Unit) => (match («$find_local_return_type_t:case_2:downcast:0» localKind) with | some «exec:1» => (let «eval:0» : externFunctionLocalKind := «exec:1»; (match «eval:0» with | .«EXTERN_FUNCTION ':' %» «exec:2» => (let typeIR_ret : typeIR := «exec:2»; (.pure (((_root_.Option.some typeIR_ret) : (_root_.Option typeIR))))))) | none => .unmatch)))))


noncomputable def «$find_local_return_type_t:clause:2» (input0 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (match (localTypingLayer.KIND (typingContext.LOCAL TC)) with | .ACTION  => (.pure (((_root_.Option.some ((typeIR.VOID) : typeIR)) : (_root_.Option typeIR)))) | _ => .unmatch))


noncomputable def «$find_local_return_type_t:clause:3» (input0 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let localKind : SpecTec.localKind := (localTypingLayer.KIND (typingContext.LOCAL TC)); (.bind (.guard (((«sub:localKind:externMethodLocalKind» localKind) = true))) (fun (_ : Unit) => (match («$find_local_return_type_t:case_4:downcast:0» localKind) with | some «exec:1» => (let «eval:0» : SpecTec.externMethodLocalKind := «exec:1»; (let externMethodLocalKind : SpecTec.externMethodLocalKind := «eval:0»; (.bind (.guard (((«exec:match:externMethodLocalKind:EXTERN_METHOD ':' %» externMethodLocalKind) = true))) (fun (_ : Unit) => (match externMethodLocalKind with | .«EXTERN_METHOD ':' %» «exec:2» => (let typeIR_ret : typeIR := «exec:2»; (.pure (((_root_.Option.some typeIR_ret) : (_root_.Option typeIR))))) | _ => .unmatch))))) | none => .unmatch)))))


noncomputable def «$find_local_return_type_t:clause:4» (input0 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let localKind : SpecTec.localKind := (localTypingLayer.KIND (typingContext.LOCAL TC)); (.bind (.guard (((«sub:localKind:externMethodLocalKind» localKind) = true))) (fun (_ : Unit) => (match («$find_local_return_type_t:case_5:downcast:0» localKind) with | some «exec:1» => (let «eval:0» : SpecTec.externMethodLocalKind := «exec:1»; (let externMethodLocalKind : SpecTec.externMethodLocalKind := «eval:0»; (.bind (.guard (((«exec:match:externMethodLocalKind:EXTERN_METHOD ABSTRACT ':' %» externMethodLocalKind) = true))) (fun (_ : Unit) => (match externMethodLocalKind with | .«EXTERN_METHOD ABSTRACT ':' %» «exec:2» => (let typeIR_ret : typeIR := «exec:2»; (.pure (((_root_.Option.some typeIR_ret) : (_root_.Option typeIR))))) | _ => .unmatch))))) | none => .unmatch)))))


noncomputable def «$find_local_return_type_t:clause:5» (input0 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (match (localTypingLayer.KIND (typingContext.LOCAL TC)) with | .CONTROL_APPLY_METHOD  => (.pure (((_root_.Option.some ((typeIR.VOID) : typeIR)) : (_root_.Option typeIR)))) | _ => .unmatch))


noncomputable def «$find_local_return_type_t:clause:6» (input0 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (.pure ((((_root_.Option.none) : (_root_.Option typeIR)) : (_root_.Option typeIR)))))


noncomputable def «$find_local_return_type_t_clauses» (input0 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_local_return_type_t:clause:0»  input0), fun (_ : _root_.Unit) => («$find_local_return_type_t:clause:1»  input0), fun (_ : _root_.Unit) => («$find_local_return_type_t:clause:2»  input0), fun (_ : _root_.Unit) => («$find_local_return_type_t:clause:3»  input0), fun (_ : _root_.Unit) => («$find_local_return_type_t:clause:4»  input0), fun (_ : _root_.Unit) => («$find_local_return_type_t:clause:5»  input0), fun (_ : _root_.Unit) => («$find_local_return_type_t:clause:6»  input0)]


noncomputable def «$callable_definedFunction:clause:0» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))

end SpecTec
