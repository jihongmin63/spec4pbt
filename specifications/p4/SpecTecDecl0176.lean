import SpecTecDecl0175

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$nestable_header:row_8:iter:2:clause:1» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_struct_in_header» typeIR_field⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_header:row_8:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:3» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$nestable_header:row_8:iter:2_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_header:row_8:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_header:row_8:iter:2:clause:1»  input0)]


noncomputable def «$nestable_array_in_header:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_header:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_header:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_header:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_header:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_header:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_header:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«VARBIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_header:matches:3:row» ((typeIR.«VARBIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_header:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_header:matches:4:row» nameTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_array_in_header:clause:5» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_header:matches:5:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_array_in_header» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_header:clause:6» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let newTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_header:matches:6:row» newTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_array_in_header:clause:7» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ARRAY % `[ % `]» «exec:1» «exec:2» => (let typeIR : SpecTec.typeIR := «exec:1»; (let _nat : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_header:matches:7:row» ((SpecTec.typeIR.«ARRAY % `[ % `]» typeIR _nat) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_array_in_header» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_header:clause:8» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let structTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_header:matches:8:row» structTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_array_in_header:clause:9» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let enumTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_header:matches:9:row» enumTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_array_in_header:clause:10» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_header:matches:10:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_array_in_header_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_array_in_header:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_header:clause:1»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_header:clause:2»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_header:clause:3»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_header:clause:4»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_header:clause:5»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_header:clause:6»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_header:clause:7»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_header:clause:8»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_header:clause:9»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_header:clause:10»  input0)]


noncomputable def «$nestable_header:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_header:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_header:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_header:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_header:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_header:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_header:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«VARBIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_header:matches:3:row» ((typeIR.«VARBIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_header:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_header:matches:4:row» nameTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_header:clause:5» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_header:matches:5:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_header» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_header:clause:6» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let newTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_header:matches:6:row» newTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_header:clause:7» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ENUM % `< % `> `{ % `}» «exec:1» «exec:2» «exec:3» => (let _typeId : typeId := «exec:1»; (let _typeIR : typeIR := «exec:2»; (let «_valueFieldIR*» : (_root_.List valueFieldIR) := «exec:3»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_header:matches:7:row» ((typeIR.«ENUM % `< % `> `{ % `}» _typeId _typeIR «_valueFieldIR*») : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))) | _ => .unmatch)


noncomputable def «$nestable_header:clause:8» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«STRUCT % `< % `> `{ % `}» «exec:1» «exec:2» «exec:3» => (let _typeId : typeId := «exec:1»; (let «_typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:2»; (let «eval:1» : (_root_.List fieldTypeIR) := «exec:3»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_header:matches:8:row» ((typeIR.«STRUCT % `< % `> `{ % `}» _typeId «_typeArgumentIR*» «eval:1») : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$nestable_header:row_8:pattern-iter:0» «eval:1»⟩) (fun («exec:4» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:4»).1; (let «_nameIR*» : (_root_.List nameIR) := ((«exec:4»).2).1; (let «typeIR_field*» : (_root_.List typeIR) := ((«exec:4»).2).2; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_header:row_8:iter:2» «typeIR_field*»⟩) (fun («exec:5» : (_root_.List _root_.Bool)) => (let «eval:4» : (_root_.List _root_.Bool) := «exec:5»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$forall_» «eval:4»⟩) (fun («exec:6» : _root_.Bool) => (let «eval:5» : _root_.Bool := «exec:6»; (.pure ((«eval:5» : _root_.Bool))))))))))))))))))) | _ => .unmatch)


noncomputable def «$nestable_header:clause:9» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ARRAY % `[ % `]» «exec:1» «exec:2» => (let typeIR : SpecTec.typeIR := «exec:1»; (let _nat : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_header:matches:9:row» ((SpecTec.typeIR.«ARRAY % `[ % `]» typeIR _nat) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_array_in_header» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_header:clause:10» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_header:matches:10:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_header_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_header:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_header:clause:1»  input0), fun (_ : _root_.Unit) => («$nestable_header:clause:2»  input0), fun (_ : _root_.Unit) => («$nestable_header:clause:3»  input0), fun (_ : _root_.Unit) => («$nestable_header:clause:4»  input0), fun (_ : _root_.Unit) => («$nestable_header:clause:5»  input0), fun (_ : _root_.Unit) => («$nestable_header:clause:6»  input0), fun (_ : _root_.Unit) => («$nestable_header:clause:7»  input0), fun (_ : _root_.Unit) => («$nestable_header:clause:8»  input0), fun (_ : _root_.Unit) => («$nestable_header:clause:9»  input0), fun (_ : _root_.Unit) => («$nestable_header:clause:10»  input0)]


noncomputable def «Type_wf:headerTypeIR:iter:4:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Type_wf:headerTypeIR:iter:4:clause:1» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_header» typeIR_field⟩) (fun («exec:3» : _root_.Bool) => (let «eval:5» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:5» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:headerTypeIR:iter:4» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch)


noncomputable def «Type_wf:headerTypeIR:iter:4_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:headerTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Type_wf:headerTypeIR:iter:4:clause:1»  input0)]


noncomputable def «$nestable_headerUnion:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_headerUnion:matches:0:row» nameTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_headerUnion:clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_headerUnion:matches:1:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_headerUnion» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_headerUnion:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let headerTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_headerUnion:matches:2:row» headerTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))

end SpecTec
