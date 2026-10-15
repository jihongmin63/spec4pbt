import SpecTecDecl0207

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$compat_divmod:clause:2» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_l : typeIR := «exec:2»; (let typeIR_r : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_divmod:matches:2:row» ((typeIR.TYPEDEF _typeId typeIR_l) : typeIR) typeIR_r))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_divmod» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_divmod:clause:3» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_l : typeIR := input0; (match input1 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_r : typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_divmod:matches:3:row» typeIR_l ((typeIR.TYPEDEF _typeId typeIR_r) : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_divmod» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch))


noncomputable def «$compat_divmod:clause:4» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (let _typeIR' : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_divmod:matches:4:row» _typeIR _typeIR'))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$compat_divmod_clauses» (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_divmod:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$compat_divmod:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$compat_divmod:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$compat_divmod:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$compat_divmod:clause:4»  input0 input1)]


noncomputable def «$compat_shift:clause:0» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (match input1 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:0:row» ((typeIR.INT) : typeIR) ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch) | _ => .unmatch)


noncomputable def «$compat_shift:clause:1» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (match input1 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:1:row» ((typeIR.INT) : typeIR) ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch) | _ => .unmatch)


noncomputable def «$compat_shift:clause:2» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (match input1 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:2:row» ((typeIR.INT) : typeIR) ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch) | _ => .unmatch)


noncomputable def «$compat_shift:clause:3» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (match input1 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:3:row» ((typeIR.«INT `< % `>» _nat) : typeIR) ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_shift:clause:4» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (match input1 with | .«INT `< % `>» «exec:2» => (let _nat' : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:4:row» ((typeIR.«INT `< % `>» _nat) : typeIR) ((typeIR.«INT `< % `>» _nat') : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_shift:clause:5» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (match input1 with | .«BIT `< % `>» «exec:2» => (let _nat' : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:5:row» ((typeIR.«INT `< % `>» _nat) : typeIR) ((typeIR.«BIT `< % `>» _nat') : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_shift:clause:6» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (match input1 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:6:row» ((typeIR.«BIT `< % `>» _nat) : typeIR) ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_shift:clause:7» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (match input1 with | .«INT `< % `>» «exec:2» => (let _nat' : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:7:row» ((typeIR.«BIT `< % `>» _nat) : typeIR) ((typeIR.«INT `< % `>» _nat') : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_shift:clause:8» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (match input1 with | .«BIT `< % `>» «exec:2» => (let _nat' : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:8:row» ((typeIR.«BIT `< % `>» _nat) : typeIR) ((typeIR.«BIT `< % `>» _nat') : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_shift:clause:9» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_l : typeIR := «exec:2»; (let typeIR_r : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:9:row» ((typeIR.TYPEDEF _typeId typeIR_l) : typeIR) typeIR_r))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_shift» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_shift:clause:10» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_l : typeIR := input0; (match input1 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_r : typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:10:row» typeIR_l ((typeIR.TYPEDEF _typeId typeIR_r) : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_shift» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch))


noncomputable def «$compat_shift:clause:11» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (let _typeIR' : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_shift:matches:11:row» _typeIR _typeIR'))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$compat_shift_clauses» (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_shift:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$compat_shift:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$compat_shift:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$compat_shift:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$compat_shift:clause:4»  input0 input1), fun (_ : _root_.Unit) => («$compat_shift:clause:5»  input0 input1), fun (_ : _root_.Unit) => («$compat_shift:clause:6»  input0 input1), fun (_ : _root_.Unit) => («$compat_shift:clause:7»  input0 input1), fun (_ : _root_.Unit) => («$compat_shift:clause:8»  input0 input1), fun (_ : _root_.Unit) => («$compat_shift:clause:9»  input0 input1), fun (_ : _root_.Unit) => («$compat_shift:clause:10»  input0 input1), fun (_ : _root_.Unit) => («$compat_shift:clause:11»  input0 input1)]


noncomputable def «$compat_compare:clause:0» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (match input1 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_compare:matches:0:row» ((typeIR.INT) : typeIR) ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch) | _ => .unmatch)


noncomputable def «$compat_compare:clause:1» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«INT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_compare:matches:1:row» ((typeIR.«INT `< % `>» w_l) : typeIR) ((typeIR.«INT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_compare:clause:2» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«BIT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_compare:matches:2:row» ((typeIR.«BIT `< % `>» w_l) : typeIR) ((typeIR.«BIT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_compare:clause:3» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_l : typeIR := «exec:2»; (let typeIR_r : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_compare:matches:3:row» ((typeIR.TYPEDEF _typeId typeIR_l) : typeIR) typeIR_r))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_compare» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_compare:clause:4» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_l : typeIR := input0; (match input1 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_r : typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_compare:matches:4:row» typeIR_l ((typeIR.TYPEDEF _typeId typeIR_r) : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_compare» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch))


noncomputable def «$compat_compare:clause:5» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (let _typeIR' : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_compare:matches:5:row» _typeIR _typeIR'))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$compat_compare_clauses» (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_compare:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$compat_compare:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$compat_compare:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$compat_compare:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$compat_compare:clause:4»  input0 input1), fun (_ : _root_.Unit) => («$compat_compare:clause:5»  input0 input1)]


noncomputable def «$compat_bitwise:clause:0» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«INT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitwise:matches:0:row» ((typeIR.«INT `< % `>» w_l) : typeIR) ((typeIR.«INT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_bitwise:clause:1» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«BIT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitwise:matches:1:row» ((typeIR.«BIT `< % `>» w_l) : typeIR) ((typeIR.«BIT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_bitwise:clause:2» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_l : typeIR := «exec:2»; (let typeIR_r : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitwise:matches:2:row» ((typeIR.TYPEDEF _typeId typeIR_l) : typeIR) typeIR_r))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_bitwise» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_bitwise:clause:3» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_l : typeIR := input0; (match input1 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_r : typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitwise:matches:3:row» typeIR_l ((typeIR.TYPEDEF _typeId typeIR_r) : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_bitwise» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch))


noncomputable def «$compat_bitwise:clause:4» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (let _typeIR' : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitwise:matches:4:row» _typeIR _typeIR'))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$compat_bitwise_clauses» (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_bitwise:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$compat_bitwise:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$compat_bitwise:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$compat_bitwise:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$compat_bitwise:clause:4»  input0 input1)]


noncomputable def «$compat_concat:clause:0» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .STRING  => (match input1 with | .STRING  => (.bind (.guard ((0 : _root_.Nat) = («$compat_concat:matches:0:row» ((typeIR.STRING) : typeIR) ((typeIR.STRING) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch) | _ => .unmatch)


noncomputable def «$compat_concat:clause:1» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (match input1 with | .«INT `< % `>» «exec:2» => (let _nat' : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_concat:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR) ((typeIR.«INT `< % `>» _nat') : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)

end SpecTec
