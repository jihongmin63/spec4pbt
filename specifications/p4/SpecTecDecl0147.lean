import SpecTecDecl0146

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$is_defaultable_typeIR:row_9:iter:2_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_defaultable_typeIR:row_9:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$is_defaultable_typeIR:row_9:iter:2:clause:1»  input0)]


noncomputable def «$is_defaultable_typeIR:row_10:iter:2:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$is_defaultable_typeIR:row_10:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_defaultable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_defaultable_typeIR:row_10:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:3» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$is_defaultable_typeIR:row_10:iter:2_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_defaultable_typeIR:row_10:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$is_defaultable_typeIR:row_10:iter:2:clause:1»  input0)]


noncomputable def «$is_defaultable_typeIR:row_11:iter:2:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$is_defaultable_typeIR:row_11:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_defaultable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_defaultable_typeIR:row_11:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:3» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$is_defaultable_typeIR:row_11:iter:2_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_defaultable_typeIR:row_11:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$is_defaultable_typeIR:row_11:iter:2:clause:1»  input0)]


noncomputable def «$is_equalable_typeIR:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .VOID  => (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:0:row» ((typeIR.VOID) : typeIR)))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$is_equalable_typeIR:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | ._NAME «exec:1» => (let typeId : SpecTec.typeId := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:1:row» ((typeIR._NAME typeId) : typeIR)))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$is_equalable_typeIR:clause:2» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:2:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_equalable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$is_equalable_typeIR:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:3:row» externObjectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_equalable_typeIR:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:4:row» parserObjectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_equalable_typeIR:clause:5» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:5:row» controlObjectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_equalable_typeIR:clause:6» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let packageObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:6:row» packageObjectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_equalable_typeIR:clause:7» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:7:row» tableObjectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_equalable_typeIR:clause:8» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .DEFAULT  => (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:8:row» ((typeIR.DEFAULT) : typeIR)))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$is_equalable_typeIR:clause:9» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let sequenceTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:9:row» sequenceTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_equalable_typeIR:clause:10» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let recordTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:10:row» recordTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_equalable_typeIR:clause:11» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .HEADER_INVALID  => (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:11:row» ((typeIR.HEADER_INVALID) : typeIR)))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$is_equalable_typeIR:clause:12» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let setTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:12:row» setTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_equalable_typeIR:clause:13» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableMetadataTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:13:row» tableMetadataTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_equalable_typeIR:clause:14» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_equalable_typeIR:matches:14:row» _typeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$is_equalable_typeIR_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:1»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:2»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:3»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:4»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:5»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:6»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:7»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:8»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:9»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:10»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:11»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:12»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:13»  input0), fun (_ : _root_.Unit) => («$is_equalable_typeIR:clause:14»  input0)]


noncomputable def «$is_assignable_typeIR:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .VOID  => (.bind (.guard ((0 : _root_.Nat) = («$is_assignable_typeIR:matches:0:row» ((typeIR.VOID) : typeIR)))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$is_assignable_typeIR:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .STRING  => (.bind (.guard ((0 : _root_.Nat) = («$is_assignable_typeIR:matches:1:row» ((typeIR.STRING) : typeIR)))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$is_assignable_typeIR:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$is_assignable_typeIR:matches:2:row» ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$is_assignable_typeIR:clause:3» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$is_assignable_typeIR:matches:3:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_assignable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$is_assignable_typeIR:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_assignable_typeIR:matches:4:row» objectTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_assignable_typeIR:clause:5» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let synthesizedTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_assignable_typeIR:matches:5:row» synthesizedTypeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_assignable_typeIR:clause:6» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_assignable_typeIR:matches:6:row» _typeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$is_assignable_typeIR_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_assignable_typeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$is_assignable_typeIR:clause:1»  input0), fun (_ : _root_.Unit) => («$is_assignable_typeIR:clause:2»  input0), fun (_ : _root_.Unit) => («$is_assignable_typeIR:clause:3»  input0), fun (_ : _root_.Unit) => («$is_assignable_typeIR:clause:4»  input0), fun (_ : _root_.Unit) => («$is_assignable_typeIR:clause:5»  input0), fun (_ : _root_.Unit) => («$is_assignable_typeIR:clause:6»  input0)]


noncomputable def «$is_serializable_typeIR:row_10:pattern-iter:0:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)

end SpecTec
