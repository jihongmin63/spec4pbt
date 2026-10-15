import SpecTecDecl0147

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$is_serializable_typeIR:row_10:pattern-iter:0:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$is_serializable_typeIR:row_10:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$is_serializable_typeIR:row_10:pattern-iter:0_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_10:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_10:pattern-iter:0:clause:1»  input0)]


noncomputable def «$is_serializable_typeIR:row_11:pattern-iter:0:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$is_serializable_typeIR:row_11:pattern-iter:0:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$is_serializable_typeIR:row_11:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$is_serializable_typeIR:row_11:pattern-iter:0_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_11:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_11:pattern-iter:0:clause:1»  input0)]


noncomputable def «$is_serializable_typeIR:row_12:pattern-iter:0:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$is_serializable_typeIR:row_12:pattern-iter:0:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$is_serializable_typeIR:row_12:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$is_serializable_typeIR:row_12:pattern-iter:0_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_12:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_12:pattern-iter:0:clause:1»  input0)]


noncomputable def «$is_serializable_typeIR:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«VARBIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:3:row» ((typeIR.«VARBIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:4» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:4:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_serializable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:5» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPE «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:5:row» ((SpecTec.typeIR.TYPE _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_serializable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:6» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ENUM % `< % `> `{ % `}» «exec:1» «exec:2» «exec:3» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (let «_valueFieldIR*» : (_root_.List valueFieldIR) := «exec:3»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:6:row» ((SpecTec.typeIR.«ENUM % `< % `> `{ % `}» _typeId typeIR «_valueFieldIR*») : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_serializable_typeIR» typeIR⟩) (fun («exec:4» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:4»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:7» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«TUPLE `< % `>» «exec:1» => (let «typeIR*» : (_root_.List typeIR) := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:7:row» ((typeIR.«TUPLE `< % `>» «typeIR*») : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_7:iter:0» «typeIR*»⟩) (fun («exec:2» : (_root_.List _root_.Bool)) => (let «eval:2» : (_root_.List _root_.Bool) := «exec:2»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$forall_» «eval:2»⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.pure ((«eval:3» : _root_.Bool)))))))))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:8» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ARRAY % `[ % `]» «exec:1» «exec:2» => (let typeIR : SpecTec.typeIR := «exec:1»; (let _nat : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:8:row» ((SpecTec.typeIR.«ARRAY % `[ % `]» typeIR _nat) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_serializable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:9» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«HEADER_STACK % `[ % `]» «exec:1» «exec:2» => (let typeIR : SpecTec.typeIR := «exec:1»; (let _nat : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:9:row» ((SpecTec.typeIR.«HEADER_STACK % `[ % `]» typeIR _nat) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_serializable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:10» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«STRUCT % `< % `> `{ % `}» «exec:1» «exec:2» «exec:3» => (let _typeId : typeId := «exec:1»; (let «_typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:2»; (let «eval:1» : (_root_.List fieldTypeIR) := «exec:3»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:10:row» ((typeIR.«STRUCT % `< % `> `{ % `}» _typeId «_typeArgumentIR*» «eval:1») : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$is_serializable_typeIR:row_10:pattern-iter:0» «eval:1»⟩) (fun («exec:4» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:4»).1; (let «_nameIR*» : (_root_.List nameIR) := ((«exec:4»).2).1; (let «typeIR*» : (_root_.List typeIR) := ((«exec:4»).2).2; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_10:iter:2» «typeIR*»⟩) (fun («exec:5» : (_root_.List _root_.Bool)) => (let «eval:4» : (_root_.List _root_.Bool) := «exec:5»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$forall_» «eval:4»⟩) (fun («exec:6» : _root_.Bool) => (let «eval:5» : _root_.Bool := «exec:6»; (.pure ((«eval:5» : _root_.Bool))))))))))))))))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:11» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«HEADER % `< % `> `{ % `}» «exec:1» «exec:2» «exec:3» => (let _typeId : typeId := «exec:1»; (let «_typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:2»; (let «eval:1» : (_root_.List fieldTypeIR) := «exec:3»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:11:row» ((typeIR.«HEADER % `< % `> `{ % `}» _typeId «_typeArgumentIR*» «eval:1») : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$is_serializable_typeIR:row_11:pattern-iter:0» «eval:1»⟩) (fun («exec:4» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:4»).1; (let «_nameIR*» : (_root_.List nameIR) := ((«exec:4»).2).1; (let «typeIR*» : (_root_.List typeIR) := ((«exec:4»).2).2; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_11:iter:2» «typeIR*»⟩) (fun («exec:5» : (_root_.List _root_.Bool)) => (let «eval:4» : (_root_.List _root_.Bool) := «exec:5»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$forall_» «eval:4»⟩) (fun («exec:6» : _root_.Bool) => (let «eval:5» : _root_.Bool := «exec:6»; (.pure ((«eval:5» : _root_.Bool))))))))))))))))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:12» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«HEADER_UNION % `< % `> `{ % `}» «exec:1» «exec:2» «exec:3» => (let _typeId : typeId := «exec:1»; (let «_typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:2»; (let «eval:1» : (_root_.List fieldTypeIR) := «exec:3»; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:12:row» ((typeIR.«HEADER_UNION % `< % `> `{ % `}» _typeId «_typeArgumentIR*» «eval:1») : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$is_serializable_typeIR:row_12:pattern-iter:0» «eval:1»⟩) (fun («exec:4» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:4»).1; (let «_nameIR*» : (_root_.List nameIR) := ((«exec:4»).2).1; (let «typeIR*» : (_root_.List typeIR) := ((«exec:4»).2).2; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_12:iter:2» «typeIR*»⟩) (fun («exec:5» : (_root_.List _root_.Bool)) => (let «eval:4» : (_root_.List _root_.Bool) := «exec:5»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$forall_» «eval:4»⟩) (fun («exec:6» : _root_.Bool) => (let «eval:5» : _root_.Bool := «exec:6»; (.pure ((«eval:5» : _root_.Bool))))))))))))))))))) | _ => .unmatch)


noncomputable def «$is_serializable_typeIR:clause:13» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$is_serializable_typeIR:matches:13:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$is_serializable_typeIR_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:1»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:2»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:3»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:4»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:5»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:6»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:7»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:8»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:9»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:10»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:11»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:12»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:clause:13»  input0)]


noncomputable def «$is_serializable_typeIR:row_7:iter:0:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$is_serializable_typeIR:row_7:iter:0:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_serializable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_7:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:1» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$is_serializable_typeIR:row_7:iter:0_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_7:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_7:iter:0:clause:1»  input0)]


noncomputable def «$is_serializable_typeIR:row_10:iter:2:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$is_serializable_typeIR:row_10:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_serializable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_10:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:3» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$is_serializable_typeIR:row_10:iter:2_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_10:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_10:iter:2:clause:1»  input0)]


noncomputable def «$is_serializable_typeIR:row_11:iter:2:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$is_serializable_typeIR:row_11:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_serializable_typeIR» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$is_serializable_typeIR:row_11:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:3» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$is_serializable_typeIR:row_11:iter:2_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_11:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$is_serializable_typeIR:row_11:iter:2:clause:1»  input0)]

end SpecTec
