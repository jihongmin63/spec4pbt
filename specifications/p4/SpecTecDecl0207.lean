import SpecTecDecl0206

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$apply_cast:clause:1» (input0 : SpecTec.typedExpressionIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typedExpressionIR : SpecTec.typedExpressionIR := input0; (let «typeIR*» : (_root_.List typeIR) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeIR*» with | «exec:2» :: «exec:1» => (let typeIR_h : typeIR := «exec:2»; (let «typeIR_t*» : (_root_.List typeIR) := «exec:1»; (match typedExpressionIR with | .«% '#' %» «exec:3» «exec:4» => (let _expressionIR : expressionIR := «exec:3»; (match «exec:4» with | .«`( % % `)» «exec:5» «exec:6» => (let _typeIR : typeIR := «exec:5»; (let ctk : SpecTec.ctk := «exec:6»; (let typedExpressionIR_cast : SpecTec.typedExpressionIR := ((SpecTec.typedExpressionIR.«% '#' %» ((expressionIR.«`( % `) %» typeIR_h typedExpressionIR) : expressionIR) ((expressionNoteIR.«`( % % `)» typeIR_h ctk) : expressionNoteIR)) : SpecTec.typedExpressionIR); (.bind (.call ⟨SpecTec.typedExpressionIR, SpecTecCall.«$apply_cast» typedExpressionIR_cast «typeIR_t*»⟩) (fun («exec:7» : SpecTec.typedExpressionIR) => (let «eval:0» : SpecTec.typedExpressionIR := «exec:7»; (.pure ((«eval:0» : SpecTec.typedExpressionIR)))))))))))))) | [] => .unmatch)))))


noncomputable def «$apply_cast_clauses» (input0 : typedExpressionIR) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$apply_cast:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$apply_cast:clause:1»  input0 input1)]


noncomputable def «$compat_lnot:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$compat_lnot:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_lnot:clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_lnot:matches:1:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_lnot» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_lnot:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_lnot:matches:2:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$compat_lnot_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_lnot:clause:0»  input0), fun (_ : _root_.Unit) => («$compat_lnot:clause:1»  input0), fun (_ : _root_.Unit) => («$compat_lnot:clause:2»  input0)]


noncomputable def «$compat_bnot:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bnot:matches:0:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_bnot:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bnot:matches:1:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_bnot:clause:2» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bnot:matches:2:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_bnot» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_bnot:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_bnot:matches:3:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$compat_bnot_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_bnot:clause:0»  input0), fun (_ : _root_.Unit) => («$compat_bnot:clause:1»  input0), fun (_ : _root_.Unit) => («$compat_bnot:clause:2»  input0), fun (_ : _root_.Unit) => («$compat_bnot:clause:3»  input0)]


noncomputable def «$compat_uplusminus:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_uplusminus:matches:0:row» ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_uplusminus:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_uplusminus:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_uplusminus:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_uplusminus:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_uplusminus:clause:3» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_uplusminus:matches:3:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_uplusminus» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_uplusminus:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_uplusminus:matches:4:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$compat_uplusminus_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_uplusminus:clause:0»  input0), fun (_ : _root_.Unit) => («$compat_uplusminus:clause:1»  input0), fun (_ : _root_.Unit) => («$compat_uplusminus:clause:2»  input0), fun (_ : _root_.Unit) => («$compat_uplusminus:clause:3»  input0), fun (_ : _root_.Unit) => («$compat_uplusminus:clause:4»  input0)]


noncomputable def «$compat_plusminusmult:clause:0» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (match input1 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_plusminusmult:matches:0:row» ((typeIR.INT) : typeIR) ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch) | _ => .unmatch)


noncomputable def «$compat_plusminusmult:clause:1» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«INT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_plusminusmult:matches:1:row» ((typeIR.«INT `< % `>» w_l) : typeIR) ((typeIR.«INT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_plusminusmult:clause:2» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«BIT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_plusminusmult:matches:2:row» ((typeIR.«BIT `< % `>» w_l) : typeIR) ((typeIR.«BIT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_plusminusmult:clause:3» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_l : typeIR := «exec:2»; (let typeIR_r : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_plusminusmult:matches:3:row» ((typeIR.TYPEDEF _typeId typeIR_l) : typeIR) typeIR_r))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_plusminusmult» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_plusminusmult:clause:4» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_l : typeIR := input0; (match input1 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_r : typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_plusminusmult:matches:4:row» typeIR_l ((typeIR.TYPEDEF _typeId typeIR_r) : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_plusminusmult» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch))


noncomputable def «$compat_plusminusmult:clause:5» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (let _typeIR' : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_plusminusmult:matches:5:row» _typeIR _typeIR'))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$compat_plusminusmult_clauses» (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_plusminusmult:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$compat_plusminusmult:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$compat_plusminusmult:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$compat_plusminusmult:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$compat_plusminusmult:clause:4»  input0 input1), fun (_ : _root_.Unit) => («$compat_plusminusmult:clause:5»  input0 input1)]


noncomputable def «$compat_satplusminus:clause:0» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«INT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_satplusminus:matches:0:row» ((typeIR.«INT `< % `>» w_l) : typeIR) ((typeIR.«INT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_satplusminus:clause:1» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«BIT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_satplusminus:matches:1:row» ((typeIR.«BIT `< % `>» w_l) : typeIR) ((typeIR.«BIT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_satplusminus:clause:2» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_l : typeIR := «exec:2»; (let typeIR_r : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_satplusminus:matches:2:row» ((typeIR.TYPEDEF _typeId typeIR_l) : typeIR) typeIR_r))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_satplusminus» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_satplusminus:clause:3» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_l : typeIR := input0; (match input1 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_r : typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_satplusminus:matches:3:row» typeIR_l ((typeIR.TYPEDEF _typeId typeIR_r) : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_satplusminus» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch))


noncomputable def «$compat_satplusminus:clause:4» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (let _typeIR' : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_satplusminus:matches:4:row» _typeIR _typeIR'))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$compat_satplusminus_clauses» (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_satplusminus:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$compat_satplusminus:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$compat_satplusminus:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$compat_satplusminus:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$compat_satplusminus:clause:4»  input0 input1)]


noncomputable def «$compat_divmod:clause:0» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (match input1 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_divmod:matches:0:row» ((typeIR.INT) : typeIR) ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch) | _ => .unmatch)


noncomputable def «$compat_divmod:clause:1» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«BIT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_divmod:matches:1:row» ((typeIR.«BIT `< % `>» w_l) : typeIR) ((typeIR.«BIT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)

end SpecTec
