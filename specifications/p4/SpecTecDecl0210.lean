import SpecTecDecl0209

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$compat_bitslice_offset_index:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_offset_index:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_offset_index:clause:3» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_offset_index:matches:3:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_bitslice_offset_index» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_offset_index:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_offset_index:matches:4:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$compat_bitslice_offset_index_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_bitslice_offset_index:clause:0»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_offset_index:clause:1»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_offset_index:clause:2»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_offset_index:clause:3»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_offset_index:clause:4»  input0)]


noncomputable def «$compat_bitslice_offset_width:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_offset_width:matches:0:row» ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_offset_width:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_offset_width:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_offset_width:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_offset_width:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_offset_width:clause:3» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_offset_width:matches:3:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_bitslice_offset_width» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_bitslice_offset_width:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_bitslice_offset_width:matches:4:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$compat_bitslice_offset_width_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_bitslice_offset_width:clause:0»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_offset_width:clause:1»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_offset_width:clause:2»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_offset_width:clause:3»  input0), fun (_ : _root_.Unit) => («$compat_bitslice_offset_width:clause:4»  input0)]


noncomputable def «$is_concrete_extern_object':case_2:pattern-iter:1:clause:0» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List callableId)), ([] : (_root_.List externMethodTypeDefIR))) : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))))) | _ :: _ => .unmatch)


noncomputable def «$is_concrete_extern_object':case_2:pattern-iter:1:clause:1» (input0 : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let _callableId : callableId := «exec:3»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)) := «exec:1»; (.bind (.call ⟨((_root_.List callableId) × (_root_.List SpecTec.externMethodTypeDefIR)), SpecTecCall.«$is_concrete_extern_object':case_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List callableId) × (_root_.List SpecTec.externMethodTypeDefIR))) => (let «pattern-tail:1» : (_root_.List callableId) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.externMethodTypeDefIR) := («exec:5»).2; (.pure ((((_callableId :: «pattern-tail:1»), (externMethodTypeDefIR :: «pattern-tail:2»)) : ((_root_.List callableId) × (_root_.List SpecTec.externMethodTypeDefIR))))))))))))) | [] => .unmatch)


noncomputable def «$is_concrete_extern_object':case_2:pattern-iter:1_clauses» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_concrete_extern_object':case_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$is_concrete_extern_object':case_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «$compat_range:clause:0» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (match input1 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_range:matches:0:row» ((typeIR.INT) : typeIR) ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch) | _ => .unmatch)


noncomputable def «$compat_range:clause:1» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«INT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_range:matches:1:row» ((typeIR.«INT `< % `>» w_l) : typeIR) ((typeIR.«INT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_range:clause:2» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«BIT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_range:matches:2:row» ((typeIR.«BIT `< % `>» w_l) : typeIR) ((typeIR.«BIT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_range:clause:3» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_l : typeIR := «exec:2»; (let typeIR_r : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_range:matches:3:row» ((typeIR.TYPEDEF _typeId typeIR_l) : typeIR) typeIR_r))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_range» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_range:clause:4» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_l : typeIR := input0; (match input1 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_r : typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_range:matches:4:row» typeIR_l ((typeIR.TYPEDEF _typeId typeIR_r) : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_range» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch))


noncomputable def «$compat_range:clause:5» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (let _typeIR' : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_range:matches:5:row» _typeIR _typeIR'))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$compat_range_clauses» (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_range:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$compat_range:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$compat_range:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$compat_range:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$compat_range:clause:4»  input0 input1), fun (_ : _root_.Unit) => («$compat_range:clause:5»  input0 input1)]


noncomputable def «$check_switchLabelIR_default:clause:0» (input0 : (_root_.List switchLabelIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «switchLabelIR*» : (_root_.List switchLabelIR) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «switchLabelIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$check_switchLabelIR_default:clause:1» (input0 : (_root_.List switchLabelIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «switchLabelIR*» : (_root_.List switchLabelIR) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «switchLabelIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «switchLabelIR*» with | «exec:2» :: «exec:1» => (let switchLabelIR_h : switchLabelIR := «exec:2»; (let «switchLabelIR_t*» : (_root_.List switchLabelIR) := «exec:1»; (.bind (.guard (((switchLabelIR.DEFAULT) : switchLabelIR) = switchLabelIR_h)) (fun (_ : Unit) => (.pure (((_root_.List.isEmpty «switchLabelIR_t*») : _root_.Bool))))))) | [] => .unmatch))))


noncomputable def «$check_switchLabelIR_default:clause:2» (input0 : (_root_.List switchLabelIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «switchLabelIR*» : (_root_.List switchLabelIR) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «switchLabelIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «switchLabelIR*» with | «exec:2» :: «exec:1» => (let switchLabelIR_h : switchLabelIR := «exec:2»; (let «switchLabelIR_t*» : (_root_.List switchLabelIR) := «exec:1»; (.bind (.guard ((switchLabelIR_h ≠ ((switchLabelIR.DEFAULT) : switchLabelIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$check_switchLabelIR_default» «switchLabelIR_t*»⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | [] => .unmatch))))


noncomputable def «$check_switchLabelIR_default_clauses» (input0 : (_root_.List switchLabelIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$check_switchLabelIR_default:clause:0»  input0), fun (_ : _root_.Unit) => («$check_switchLabelIR_default:clause:1»  input0), fun (_ : _root_.Unit) => («$check_switchLabelIR_default:clause:2»  input0)]


noncomputable def «$compat_switch:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .ERROR  => (.bind (.guard ((0 : _root_.Nat) = («$compat_switch:matches:0:row» ((typeIR.ERROR) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_switch:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_switch:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_switch:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_switch:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_switch:clause:3» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_switch:matches:3:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_switch» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_switch:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let enumTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_switch:matches:4:row» enumTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$compat_switch:clause:5» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_switch:matches:5:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$compat_switch_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_switch:clause:0»  input0), fun (_ : _root_.Unit) => («$compat_switch:clause:1»  input0), fun (_ : _root_.Unit) => («$compat_switch:clause:2»  input0), fun (_ : _root_.Unit) => («$compat_switch:clause:3»  input0), fun (_ : _root_.Unit) => («$compat_switch:clause:4»  input0), fun (_ : _root_.Unit) => («$compat_switch:clause:5»  input0)]


noncomputable def «InstDecl_non_objectInitializer_ok:rule:iter:1:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)

end SpecTec
