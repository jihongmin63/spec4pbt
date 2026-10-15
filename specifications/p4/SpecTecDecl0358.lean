import SpecTecDecl0357

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def Decls_inst_clauses (input0 : instContext) (input1 : store) (input2 : (_root_.List declarationIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decls_inst:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decls_inst:clause:1»  input0 input1 input2)]


noncomputable def «Program_inst:clause:0» (input0 : SpecTec.p4program) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p4program : SpecTec.p4program := input0; (.bind (.call ⟨p4programIR, SpecTecCall.Program_ok p4program⟩) (fun («exec:1» : p4programIR) => (match «exec:1» with | .«% ';'» «exec:2» => (let «declarationIR*» : (_root_.List declarationIR) := «exec:2»; (.bind (.call ⟨instContext, SpecTecCall.«$empty_instContext»⟩) (fun («exec:3» : instContext) => (let «eval:0» : instContext := «exec:3»; (let IC_0 : instContext := «eval:0»; (.bind (.call ⟨store, SpecTecCall.«$empty_store»⟩) (fun («exec:4» : store) => (let «eval:1» : store := «exec:4»; (let STO_0 : store := «eval:1»; (.bind (.call ⟨(instContext × store), SpecTecCall.Decls_inst IC_0 STO_0 «declarationIR*»⟩) (fun («exec:5» : (instContext × store)) => (let IC_1 : instContext := («exec:5»).1; (let STO_1 : store := («exec:5»).2; (.pure ((((instContext.GLOBAL IC_1), STO_1) : (globalInstLayer × store)))))))))))))))))))))


noncomputable def Program_inst_clauses (input0 : p4program) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Program_inst:clause:0»  input0)]


noncomputable def «$match_keyset:case_3:iter:0:clause:0» (input0 : value) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value_key : value := input0; (match input1 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch))


noncomputable def «$match_keyset:case_3:iter:0:clause:1» (input0 : SpecTec.value) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value_key : SpecTec.value := input0; (match input1 with | «exec:2» :: «exec:1» => (let value : SpecTec.value := «exec:2»; (let «tail:0» : (_root_.List SpecTec.value) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» value value_key⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_keyset:case_3:iter:0» value_key «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:1» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch))


noncomputable def «$match_keyset:case_3:iter:0_clauses» (input0 : value) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_keyset:case_3:iter:0:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$match_keyset:case_3:iter:0:clause:1»  input0 input1)]


noncomputable def «$match_keyset:clause:0» (input0 : SpecTec.setValue) (input1 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let setValue : SpecTec.setValue := input0; (let value_key : value := input1; (.bind (.guard (((«exec:match:setValue:SET `{ '...' `}» setValue) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))


noncomputable def «$match_keyset:clause:1» (input0 : SpecTec.setValue) (input1 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let setValue : SpecTec.setValue := input0; (let value_key : SpecTec.value := input1; (.bind (.guard (((«exec:match:setValue:SET `{ % `}» setValue) = true))) (fun (_ : Unit) => (match setValue with | .«SET `{ % `}» «exec:1» => (let value : SpecTec.value := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» value value_key⟩) (fun («exec:2» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:2»; (.pure ((«eval:0» : _root_.Bool))))))) | _ => .unmatch)))))


noncomputable def «$match_keyset:clause:2» (input0 : SpecTec.setValue) (input1 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let setValue : SpecTec.setValue := input0; (let value_key : value := input1; (.bind (.guard (((«exec:match:setValue:SET `{ % `( % `) `}» setValue) = true))) (fun (_ : Unit) => (match setValue with | .«SET `{ % `( % `) `}» «exec:1» «exec:2» => (let «value*» : (_root_.List value) := «exec:1»; (let _nat : _root_.Nat := «exec:2»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_keyset:case_3:iter:0» value_key «value*»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «eval:2» : (_root_.List _root_.Bool) := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$exists_» «eval:2»⟩) (fun («exec:4» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:4»; (.pure ((«eval:3» : _root_.Bool))))))))))) | _ => .unmatch)))))


noncomputable def «$match_keyset:clause:3» (input0 : SpecTec.setValue) (input1 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let setValue : SpecTec.setValue := input0; (let value_key : value := input1; (.bind (.guard (((«exec:match:setValue:SET `{ % '&&&' % `}» setValue) = true))) (fun (_ : Unit) => (match setValue with | .«SET `{ % '&&&' % `}» «exec:1» «exec:2» => (let value_base : value := «exec:1»; (let value_mask : value := «exec:2»; (.bind (.call ⟨value, SpecTecCall.«$bin_band» value_base value_mask⟩) (fun («exec:3» : value) => (let «eval:0» : value := «exec:3»; (.bind (.call ⟨value, SpecTecCall.«$bin_band» value_key value_mask⟩) (fun («exec:4» : value) => (let «eval:1» : value := «exec:4»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» «eval:0» «eval:1»⟩) (fun («exec:5» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:5»; (.pure ((«eval:2» : _root_.Bool)))))))))))))) | _ => .unmatch)))))


noncomputable def «$match_keyset:clause:4» (input0 : SpecTec.setValue) (input1 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let setValue : SpecTec.setValue := input0; (let value_key : value := input1; (.bind (.guard (((«exec:match:setValue:SET `{ % '..' % `}» setValue) = true))) (fun (_ : Unit) => (match setValue with | .«SET `{ % '..' % `}» «exec:1» «exec:2» => (let value_base : value := «exec:1»; (let value_limit : value := «exec:2»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_le» value_base value_key⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_le» value_key value_limit⟩) (fun («exec:4» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:4»; (.pure (((«eval:0» && «eval:1») : _root_.Bool))))))))))) | _ => .unmatch)))))


noncomputable def «$match_keyset_clauses» (input0 : setValue) (input1 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_keyset:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$match_keyset:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$match_keyset:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$match_keyset:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$match_keyset:clause:4»  input0 input1)]


noncomputable def «$match_keysets:clause:0» (input0 : (_root_.List setValue)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «setValue*» : (_root_.List setValue) := input0; (let «value*» : (_root_.List value) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «setValue*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «value*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))))


noncomputable def «$match_keysets:clause:1» (input0 : (_root_.List setValue)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «setValue*» : (_root_.List setValue) := input0; (let «value_key*» : (_root_.List value) := input1; (.bind (.guard (([((setValue.«SET `{ '...' `}») : setValue)] : (_root_.List setValue)) = «setValue*»)) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))


noncomputable def «$match_keysets:clause:2» (input0 : (_root_.List SpecTec.setValue)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «setValue'*» : (_root_.List SpecTec.setValue) := input0; (let «value*» : (_root_.List value) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «setValue'*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «setValue'*» with | «exec:2» :: «exec:1» => (let setValue : SpecTec.setValue := «exec:2»; (match «exec:1» with | [] => (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «value*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «value*» with | «exec:4» :: «exec:3» => (let value_key : value := «exec:4»; (match «exec:3» with | [] => (.bind (.guard ((setValue ≠ ((SpecTec.setValue.«SET `{ '...' `}») : SpecTec.setValue)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$match_keyset» setValue value_key⟩) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.pure ((«eval:0» : _root_.Bool)))))))) | _ :: _ => .unmatch)) | [] => .unmatch))) | _ :: _ => .unmatch)) | [] => .unmatch)))))


noncomputable def «$match_keysets:clause:3» (input0 : (_root_.List setValue)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «setValue*» : (_root_.List setValue) := input0; (let «value*» : (_root_.List value) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «setValue*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «setValue*» with | «exec:2» :: «exec:1» => (let setValue_h : setValue := «exec:2»; (let «setValue_t*» : (_root_.List setValue) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «value*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «value*» with | «exec:4» :: «exec:3» => (let value_key_h : value := «exec:4»; (let «value_key_t*» : (_root_.List value) := «exec:3»; (.bind (.guard ((«setValue_t*» ≠ ([] : (_root_.List setValue))))) (fun (_ : Unit) => (.bind (.guard ((«value_key_t*» ≠ ([] : (_root_.List value))))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$match_keyset» setValue_h value_key_h⟩) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$match_keysets» «setValue_t*» «value_key_t*»⟩) (fun («exec:6» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:6»; (.pure ((«eval:1» : _root_.Bool))))))))))))))))) | [] => .unmatch))))) | [] => .unmatch)))))


noncomputable def «$match_keysets:clause:4» (input0 : (_root_.List setValue)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «setValue*» : (_root_.List setValue) := input0; (let «value*» : (_root_.List value) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «setValue*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «setValue*» with | «exec:2» :: «exec:1» => (let setValue_h : setValue := «exec:2»; (let «setValue_t*» : (_root_.List setValue) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «value*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «value*» with | «exec:4» :: «exec:3» => (let value_key_h : value := «exec:4»; (let «value_key_t*» : (_root_.List value) := «exec:3»; (.bind (.guard ((«setValue_t*» ≠ ([] : (_root_.List setValue))))) (fun (_ : Unit) => (.bind (.guard ((«value_key_t*» ≠ ([] : (_root_.List value))))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$match_keyset» setValue_h value_key_h⟩) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))))))))) | [] => .unmatch))))) | [] => .unmatch)))))


noncomputable def «$match_keysets_clauses» (input0 : (_root_.List setValue)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_keysets:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$match_keysets:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$match_keysets:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$match_keysets:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$match_keysets:clause:4»  input0 input1)]


noncomputable def «$values_of_setValue:clause:0» (input0 : setTypeIR) (input1 : SpecTec.setValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«SET `< % `>» «exec:1» => (let typeIR : SpecTec.typeIR := «exec:1»; (let setValue : SpecTec.setValue := input1; (.bind (.guard (((«exec:match:setValue:SET `{ % '..' % `}» setValue) = true))) (fun (_ : Unit) => (match setValue with | .«SET `{ % '..' % `}» «exec:2» «exec:3» => (let value_l : value := «exec:2»; (let value_r : value := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_lt» value_l value_r⟩) (fun («exec:4» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:4»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$cast_op» typeIR ((value.D (_root_.Int.ofNat (1 : _root_.Nat))) : value)⟩) (fun («exec:5» : value) => (let «eval:1» : value := «exec:5»; (let value_one : value := «eval:1»; (.bind (.call ⟨value, SpecTecCall.«$bin_plus» value_l value_one⟩) (fun («exec:6» : value) => (let «eval:2» : value := «exec:6»; (let value_l_inc : value := «eval:2»; (.bind (.call ⟨(_root_.List value), SpecTecCall.«$values_of_setValue» ((setTypeIR.«SET `< % `>» typeIR) : setTypeIR) ((SpecTec.setValue.«SET `{ % '..' % `}» value_l_inc value_r) : SpecTec.setValue)⟩) (fun («exec:7» : (_root_.List value)) => (let «eval:3» : (_root_.List value) := «exec:7»; (.pure (((value_l :: «eval:3») : (_root_.List value)))))))))))))))))))))) | _ => .unmatch))))))


noncomputable def «$values_of_setValue:clause:1» (input0 : setTypeIR) (input1 : SpecTec.setValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«SET `< % `>» «exec:1» => (let typeIR : SpecTec.typeIR := «exec:1»; (let setValue : SpecTec.setValue := input1; (.bind (.guard (((«exec:match:setValue:SET `{ % '..' % `}» setValue) = true))) (fun (_ : Unit) => (match setValue with | .«SET `{ % '..' % `}» «exec:2» «exec:3» => (let value_l : value := «exec:2»; (let value_r : value := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» value_l value_r⟩) (fun («exec:4» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:4»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.pure ((([value_l] : (_root_.List value)) : (_root_.List value))))))))))) | _ => .unmatch))))))


noncomputable def «$values_of_setValue:clause:2» (input0 : setTypeIR) (input1 : SpecTec.setValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«SET `< % `>» «exec:1» => (let typeIR : SpecTec.typeIR := «exec:1»; (let setValue : SpecTec.setValue := input1; (.bind (.guard (((«exec:match:setValue:SET `{ % '..' % `}» setValue) = true))) (fun (_ : Unit) => (match setValue with | .«SET `{ % '..' % `}» «exec:2» «exec:3» => (let value_l : value := «exec:2»; (let value_r : value := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_gt» value_l value_r⟩) (fun («exec:4» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:4»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List value)) : (_root_.List value))))))))))) | _ => .unmatch))))))


noncomputable def «$values_of_setValue_clauses» (input0 : setTypeIR) (input1 : setValue) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$values_of_setValue:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$values_of_setValue:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$values_of_setValue:clause:2»  input0 input1)]


noncomputable def «$match_switchLabelIR_general:clause:0» (input0 : SpecTec.value) (input1 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (let value' : SpecTec.value := input1; (.bind (.guard (((«sub:value:defaultValue» value') = true))) (fun (_ : Unit) => (match («$match_switchLabelIR_general:case_1:downcast:0» value') with | some «exec:1» => (let «eval:0» : SpecTec.defaultValue := «exec:1»; (let defaultValue : SpecTec.defaultValue := «eval:0»; (.bind (.guard (((SpecTec.defaultValue.DEFAULT) : SpecTec.defaultValue) = defaultValue)) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))) | none => .unmatch)))))


noncomputable def «$match_switchLabelIR_general:clause:1» (input0 : value) (input1 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value_a : value := input0; (let value_b : value := input1; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» value_a value_b⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((«eval:0» : _root_.Bool))))))))


noncomputable def «$match_switchLabelIR_general_clauses» (input0 : value) (input1 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_switchLabelIR_general:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$match_switchLabelIR_general:clause:1»  input0 input1)]


noncomputable def «Expr_eval:clause:0» (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : typedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC : evalContext := input1; (let ARCH : arch := input2; (match input3 with | .«% '#' %» «exec:1» «exec:2» => (let expressionIR : SpecTec.expressionIR := «exec:1»; (let _expressionNoteIR : expressionNoteIR := «exec:2»; (let expressionIR' : SpecTec.expressionIR := expressionIR; (.bind (.guard (((«sub:expressionIR:booleanLiteral» expressionIR') = true))) (fun (_ : Unit) => (match («Expr_eval:booleanLiteral:downcast:0» expressionIR') with | some «exec:3» => (let «eval:0» : SpecTec.booleanLiteral := «exec:3»; (let booleanLiteral : SpecTec.booleanLiteral := «eval:0»; (.bind (.call ⟨SpecTec.boolValue, SpecTecCall.«$ite» SpecTec.boolValue (_root_.Decidable.decide (booleanLiteral = ((SpecTec.booleanLiteral.TRUE) : SpecTec.booleanLiteral))) ((SpecTec.boolValue._B true) : SpecTec.boolValue) ((SpecTec.boolValue._B false) : SpecTec.boolValue)⟩) (fun («exec:4» : SpecTec.boolValue) => (let «eval:1» : SpecTec.boolValue := «exec:4»; (let boolValue : SpecTec.boolValue := «eval:1»; (let expressionResult : SpecTec.expressionResult := ((SpecTec.expressionResult._CONT («cast:boolValue:value» boolValue)) : SpecTec.expressionResult); (.pure (((EC, (ARCH, expressionResult)) : (evalContext × (arch × SpecTec.expressionResult)))))))))))) | none => .unmatch))))))))))


noncomputable def «Expr_eval:clause:1» (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : typedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC : evalContext := input1; (let ARCH : arch := input2; (match input3 with | .«% '#' %» «exec:1» «exec:2» => (let expressionIR : SpecTec.expressionIR := «exec:1»; (let _expressionNoteIR : expressionNoteIR := «exec:2»; (let expressionIR' : SpecTec.expressionIR := expressionIR; (.bind (.guard (((«sub:expressionIR:integerLiteral» expressionIR') = true))) (fun (_ : Unit) => (match («Expr_eval:integerLiteral:downcast:0» expressionIR') with | some «exec:3» => (let «eval:0» : SpecTec.integerLiteral := «exec:3»; (let integerLiteral : SpecTec.integerLiteral := «eval:0»; (let expressionResult : SpecTec.expressionResult := ((SpecTec.expressionResult._CONT («cast:integerLiteral:value» integerLiteral)) : SpecTec.expressionResult); (.pure (((EC, (ARCH, expressionResult)) : (evalContext × (arch × SpecTec.expressionResult)))))))) | none => .unmatch))))))))))


noncomputable def «Expr_eval:clause:2» (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : typedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC : evalContext := input1; (let ARCH : arch := input2; (match input3 with | .«% '#' %» «exec:1» «exec:2» => (let expressionIR : SpecTec.expressionIR := «exec:1»; (let _expressionNoteIR : expressionNoteIR := «exec:2»; (let expressionIR' : SpecTec.expressionIR := expressionIR; (.bind (.guard (((«sub:expressionIR:stringLiteral» expressionIR') = true))) (fun (_ : Unit) => (match («Expr_eval:stringLiteral:downcast:0» expressionIR') with | some «exec:3» => (let «eval:0» : SpecTec.stringLiteral := «exec:3»; (let stringLiteral : SpecTec.stringLiteral := «eval:0»; (let expressionResult : SpecTec.expressionResult := ((SpecTec.expressionResult._CONT («cast:stringLiteral:value» stringLiteral)) : SpecTec.expressionResult); (.pure (((EC, (ARCH, expressionResult)) : (evalContext × (arch × SpecTec.expressionResult)))))))) | none => .unmatch))))))))))


noncomputable def «Expr_eval:clause:3» (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : typedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC : evalContext := input1; (let ARCH : arch := input2; (match input3 with | .«% '#' %» «exec:1» «exec:2» => (let expressionIR : SpecTec.expressionIR := «exec:1»; (let _expressionNoteIR : expressionNoteIR := «exec:2»; (.bind (.guard (((«sub:expressionIR:prefixedNameIR» expressionIR) = true))) (fun (_ : Unit) => (match («Expr_eval:referenceExpressionIR:downcast:0» expressionIR) with | some «exec:3» => (let «eval:0» : SpecTec.prefixedNameIR := «exec:3»; (let prefixedNameIR : SpecTec.prefixedNameIR := «eval:0»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$find_var_e» prefixedNameIR p EC⟩) (fun («exec:4» : SpecTec.value) => (let «eval:1» : SpecTec.value := «exec:4»; (let value : SpecTec.value := «eval:1»; (let expressionResult : SpecTec.expressionResult := ((SpecTec.expressionResult._CONT value) : SpecTec.expressionResult); (.pure (((EC, (ARCH, expressionResult)) : (evalContext × (arch × SpecTec.expressionResult)))))))))))) | none => .unmatch)))))))))


noncomputable def «Expr_eval:clause:4» (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : typedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC : evalContext := input1; (let ARCH : arch := input2; (match input3 with | .«% '#' %» «exec:1» «exec:2» => (let expressionIR : SpecTec.expressionIR := «exec:1»; (let _expressionNoteIR : expressionNoteIR := «exec:2»; (.bind (.guard (((«sub:expressionIR:defaultExpression» expressionIR) = true))) (fun (_ : Unit) => (match («Expr_eval:defaultExpressionIR:downcast:0» expressionIR) with | some «exec:3» => (let «eval:0» : SpecTec.defaultExpression := «exec:3»; (let defaultExpression : SpecTec.defaultExpression := «eval:0»; (.bind (.guard (((SpecTec.defaultExpression.«'...'») : SpecTec.defaultExpression) = defaultExpression)) (fun (_ : Unit) => (let expressionResult : SpecTec.expressionResult := ((SpecTec.expressionResult._CONT ((value.DEFAULT) : value)) : SpecTec.expressionResult); (.pure (((EC, (ARCH, expressionResult)) : (evalContext × (arch × SpecTec.expressionResult)))))))))) | none => .unmatch)))))))))


noncomputable def «Expr_eval:clause:5» (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : SpecTec.typedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC_0 : evalContext := input1; (let ARCH_0 : arch := input2; (match input3 with | .«% '#' %» «exec:1» «exec:2» => (let expressionIR : SpecTec.expressionIR := «exec:1»; (let _expressionNoteIR : expressionNoteIR := «exec:2»; (.bind (.guard (((«sub:expressionIR:unaryExpressionIR» expressionIR) = true))) (fun (_ : Unit) => (match («Expr_eval:abort:downcast:0» expressionIR) with | some «exec:3» => (let «eval:0» : unaryExpressionIR := «exec:3»; (match «eval:0» with | .«% %» «exec:4» «exec:5» => (let unop : SpecTec.unop := «exec:4»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:5»; (.bind (.call ⟨(evalContext × (arch × expressionResult)), SpecTecCall.Expr_eval p EC_0 ARCH_0 typedExpressionIR⟩) (fun («exec:6» : (evalContext × (arch × expressionResult))) => (let EC_1 : evalContext := («exec:6»).1; (let ARCH_1 : arch := ((«exec:6»).2).1; (let expressionResult' : expressionResult := ((«exec:6»).2).2; (.bind (.guard (((«sub:expressionResult:abortResult» expressionResult') = true))) (fun (_ : Unit) => (match («Expr_eval:abort:downcast:1» expressionResult') with | some «exec:7» => (let «eval:1» : SpecTec.abortResult := «exec:7»; (let abortResult : SpecTec.abortResult := «eval:1»; (.pure (((EC_1, (ARCH_1, («cast:abortResult:expressionResult» abortResult))) : (evalContext × (arch × expressionResult))))))) | none => .unmatch)))))))))))) | none => .unmatch)))))))))


noncomputable def «Expr_eval:clause:6» (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : SpecTec.typedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC_0 : evalContext := input1; (let ARCH_0 : arch := input2; (match input3 with | .«% '#' %» «exec:1» «exec:2» => (let expressionIR : SpecTec.expressionIR := «exec:1»; (let _expressionNoteIR : expressionNoteIR := «exec:2»; (.bind (.guard (((«sub:expressionIR:unaryExpressionIR» expressionIR) = true))) (fun (_ : Unit) => (match («Expr_eval:cont:downcast:0» expressionIR) with | some «exec:3» => (let «eval:0» : unaryExpressionIR := «exec:3»; (match «eval:0» with | .«% %» «exec:4» «exec:5» => (let unop : SpecTec.unop := «exec:4»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:5»; (.bind (.call ⟨(evalContext × (arch × SpecTec.expressionResult)), SpecTecCall.Expr_eval p EC_0 ARCH_0 typedExpressionIR⟩) (fun («exec:6» : (evalContext × (arch × SpecTec.expressionResult))) => (let EC_1 : evalContext := («exec:6»).1; (let ARCH_1 : arch := ((«exec:6»).2).1; (let expressionResult' : SpecTec.expressionResult := ((«exec:6»).2).2; (.bind (.guard (((«sub:5bbdc400ae580196ad190cb78bdb96be» expressionResult') = true))) (fun (_ : Unit) => (match («Expr_eval:cont:downcast:1» expressionResult') with | some «exec:7» => (let «eval:1» : (continueResult SpecTec.value) := «exec:7»; (match «eval:1» with | ._CONT «exec:8» => (let value : SpecTec.value := «exec:8»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$un_op» unop value⟩) (fun («exec:9» : SpecTec.value) => (let «eval:2» : SpecTec.value := «exec:9»; (let expressionResult : SpecTec.expressionResult := ((SpecTec.expressionResult._CONT «eval:2») : SpecTec.expressionResult); (.pure (((EC_1, (ARCH_1, expressionResult)) : (evalContext × (arch × SpecTec.expressionResult)))))))))))) | none => .unmatch)))))))))))) | none => .unmatch)))))))))

end SpecTec
