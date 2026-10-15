import SpecTecDecl0208

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$compat_concat:clause:2» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (match input1 with | .«BIT `< % `>» «exec:2» => (let _nat' : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_concat:matches:2:row» ((typeIR.«INT `< % `>» _nat) : typeIR) ((typeIR.«BIT `< % `>» _nat') : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_concat:clause:3» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (match input1 with | .«INT `< % `>» «exec:2» => (let _nat' : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_concat:matches:3:row» ((typeIR.«BIT `< % `>» _nat) : typeIR) ((typeIR.«INT `< % `>» _nat') : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_concat:clause:4» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (match input1 with | .«BIT `< % `>» «exec:2» => (let _nat' : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_concat:matches:4:row» ((typeIR.«BIT `< % `>» _nat) : typeIR) ((typeIR.«BIT `< % `>» _nat') : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_concat:clause:5» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_l : typeIR := «exec:2»; (let typeIR_r : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_concat:matches:5:row» ((typeIR.TYPEDEF _typeId typeIR_l) : typeIR) typeIR_r))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_concat» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_concat:clause:6» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_l : typeIR := input0; (match input1 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_r : typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_concat:matches:6:row» typeIR_l ((typeIR.TYPEDEF _typeId typeIR_r) : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_concat» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch))


noncomputable def «$compat_concat:clause:7» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (let _typeIR' : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_concat:matches:7:row» _typeIR _typeIR'))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$compat_concat_clauses» (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_concat:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$compat_concat:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$compat_concat:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$compat_concat:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$compat_concat:clause:4»  input0 input1), fun (_ : _root_.Unit) => («$compat_concat:clause:5»  input0 input1), fun (_ : _root_.Unit) => («$compat_concat:clause:6»  input0 input1), fun (_ : _root_.Unit) => («$compat_concat:clause:7»  input0 input1)]


noncomputable def «$compat_logical:clause:0» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (match input1 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$compat_logical:matches:0:row» ((typeIR.BOOL) : typeIR) ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch) | _ => .unmatch)


noncomputable def «$compat_logical:clause:1» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_l : typeIR := «exec:2»; (let typeIR_r : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_logical:matches:1:row» ((typeIR.TYPEDEF _typeId typeIR_l) : typeIR) typeIR_r))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_logical» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_logical:clause:2» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_l : typeIR := input0; (match input1 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_r : typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_logical:matches:2:row» typeIR_l ((typeIR.TYPEDEF _typeId typeIR_r) : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_logical» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch))


noncomputable def «$compat_logical:clause:3» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (let _typeIR' : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_logical:matches:3:row» _typeIR _typeIR'))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$compat_logical_clauses» (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_logical:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$compat_logical:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$compat_logical:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$compat_logical:clause:3»  input0 input1)]


noncomputable def «$compat_array_index:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_array_index:matches:0:row» ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_array_index:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_array_index:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_array_index:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_array_index:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_array_index:clause:3» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_array_index:matches:3:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_array_index» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_array_index:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_array_index:matches:4:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$compat_array_index_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_array_index:clause:0»  input0), fun (_ : _root_.Unit) => («$compat_array_index:clause:1»  input0), fun (_ : _root_.Unit) => («$compat_array_index:clause:2»  input0), fun (_ : _root_.Unit) => («$compat_array_index:clause:3»  input0), fun (_ : _root_.Unit) => («$compat_array_index:clause:4»  input0)]


noncomputable def «$compat_bitslice_base:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_base:matches:0:row» ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_base:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let w : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_base:matches:1:row» ((typeIR.«INT `< % `>» w) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w > (0 : _root_.Nat))) : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_base:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_base:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_base:clause:3» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_base:matches:3:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_bitslice_base» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_base:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_base:matches:4:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$compat_bitslice_base_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_bitslice_base:clause:0»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_base:clause:1»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_base:clause:2»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_base:clause:3»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_base:clause:4»  input0)]


noncomputable def «$compat_bitslice_range_index:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_range_index:matches:0:row» ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_range_index:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_range_index:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_range_index:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_range_index:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_range_index:clause:3» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_range_index:matches:3:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_bitslice_range_index» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_range_index:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_range_index:matches:4:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$compat_bitslice_range_index_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_bitslice_range_index:clause:0»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_range_index:clause:1»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_range_index:clause:2»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_range_index:clause:3»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_range_index:clause:4»  input0)]


noncomputable def «$compat_bitslice_offset_index:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_offset_index:matches:0:row» ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_offset_index:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_offset_index:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)

end SpecTec
