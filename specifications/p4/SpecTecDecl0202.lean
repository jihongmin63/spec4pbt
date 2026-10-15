import SpecTecDecl0201

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «TableEntry_action_ok:prefixedNonTypeName-argumentList:iter:2_clauses» (input0 : (_root_.List argumentIR)) (input1 : (_root_.List argumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («TableEntry_action_ok:prefixedNonTypeName-argumentList:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («TableEntry_action_ok:prefixedNonTypeName-argumentList:iter:2:clause:1»  input0 input1)]


noncomputable def «TableType_ok:rule:pattern-iter:1:clause:0» (input0 : (_root_.List matchAction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List argumentListIR)), (([] : (_root_.List (_root_.List parameterIR))), ([] : (_root_.List prefixedNameIR)))) : ((_root_.List argumentListIR) × ((_root_.List (_root_.List parameterIR)) × (_root_.List prefixedNameIR)))))) | _ :: _ => .unmatch)


noncomputable def «TableType_ok:rule:pattern-iter:1:clause:1» (input0 : (_root_.List matchAction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% `( % '@' % `)» «exec:3» «exec:4» «exec:5» => (let prefixedNameIR_action : prefixedNameIR := «exec:3»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:4»; (let _argumentListIR : argumentListIR := «exec:5»; (let «pattern-tail:0» : (_root_.List matchAction) := «exec:1»; (.bind (.call ⟨((_root_.List argumentListIR) × ((_root_.List (_root_.List parameterIR)) × (_root_.List prefixedNameIR))), SpecTecCall.«TableType_ok:rule:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List argumentListIR) × ((_root_.List (_root_.List parameterIR)) × (_root_.List prefixedNameIR)))) => (let «pattern-tail:1» : (_root_.List argumentListIR) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List (_root_.List parameterIR)) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List prefixedNameIR) := ((«exec:6»).2).2; (.pure ((((_argumentListIR :: «pattern-tail:1»), ((«_parameterIR*» :: «pattern-tail:2»), (prefixedNameIR_action :: «pattern-tail:3»))) : ((_root_.List argumentListIR) × ((_root_.List (_root_.List parameterIR)) × (_root_.List prefixedNameIR)))))))))))))))) | [] => .unmatch)


noncomputable def «TableType_ok:rule:pattern-iter:1_clauses» (input0 : (_root_.List matchAction)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («TableType_ok:rule:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («TableType_ok:rule:pattern-iter:1:clause:1»  input0)]


noncomputable def «TableType_ok:rule:iter:5:clause:0» (input0 : typeId) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeId_enum : typeId := input0; (match input1 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch))


noncomputable def «TableType_ok:rule:iter:5:clause:1» (input0 : typeId) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeId_enum : typeId := input0; (match input1 with | «exec:2» :: «exec:1» => (let nameIR_enum_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (let value_enum_field : value := ((value.«TABLE_ENUM % '.' %» typeId_enum nameIR_enum_field) : value); (.bind (.call ⟨(_root_.List value), SpecTecCall.«TableType_ok:rule:iter:5» typeId_enum «tail:0»⟩) (fun («exec:3» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:3»; (.pure (((value_enum_field :: «tail:1») : (_root_.List value)))))))))) | [] => .unmatch))


noncomputable def «TableType_ok:rule:iter:5_clauses» (input0 : typeId) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («TableType_ok:rule:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («TableType_ok:rule:iter:5:clause:1»  input0 input1)]


noncomputable def «TableType_ok:rule:iter:7:clause:0» (input0 : typeId) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeId_enum : typeId := input0; (match input1 with | [] => (.pure ((([] : (_root_.List _root_.String)) : (_root_.List _root_.String)))) | _ :: _ => .unmatch))


noncomputable def «TableType_ok:rule:iter:7:clause:1» (input0 : typeId) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeId_enum : typeId := input0; (match input1 with | «exec:2» :: «exec:1» => (let nameIR_enum_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.String), SpecTecCall.«TableType_ok:rule:iter:7» typeId_enum «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.String)) => (let «tail:1» : (_root_.List _root_.String) := «exec:3»; (.pure (((((typeId_enum ++ ".") ++ nameIR_enum_field) :: «tail:1») : (_root_.List _root_.String))))))))) | [] => .unmatch))


noncomputable def «TableType_ok:rule:iter:7_clauses» (input0 : typeId) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («TableType_ok:rule:iter:7:clause:0»  input0 input1), fun (_ : _root_.Unit) => («TableType_ok:rule:iter:7:clause:1»  input0 input1)]


noncomputable def «Decl_ok:errorDeclaration:iter:2:clause:0» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List nameIR)) : (_root_.List nameIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:errorDeclaration:iter:2:clause:1» (input0 : (_root_.List SpecTec.name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let name : SpecTec.name := «exec:2»; (let «tail:0» : (_root_.List SpecTec.name) := «exec:1»; (.bind (.call ⟨SpecTec.nameIR, SpecTecCall.«$name» name⟩) (fun («exec:3» : SpecTec.nameIR) => (let «eval:3» : SpecTec.nameIR := «exec:3»; (let nameIR : SpecTec.nameIR := «eval:3»; (.bind (.call ⟨(_root_.List SpecTec.nameIR), SpecTecCall.«Decl_ok:errorDeclaration:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.nameIR)) => (let «tail:1» : (_root_.List SpecTec.nameIR) := «exec:4»; (.pure (((nameIR :: «tail:1») : (_root_.List SpecTec.nameIR))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:errorDeclaration:iter:2_clauses» (input0 : (_root_.List name)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:errorDeclaration:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:errorDeclaration:iter:2:clause:1»  input0)]


noncomputable def «Decl_ok:errorDeclaration:iter:5:clause:0» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List nameIR)) : (_root_.List nameIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:errorDeclaration:iter:5:clause:1» (input0 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (let nameIR_error : SpecTec.nameIR := ("error." ++ nameIR); (.bind (.call ⟨(_root_.List SpecTec.nameIR), SpecTecCall.«Decl_ok:errorDeclaration:iter:5» «tail:0»⟩) (fun («exec:3» : (_root_.List SpecTec.nameIR)) => (let «tail:1» : (_root_.List SpecTec.nameIR) := «exec:3»; (.pure (((nameIR_error :: «tail:1») : (_root_.List SpecTec.nameIR)))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:errorDeclaration:iter:5_clauses» (input0 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:errorDeclaration:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:errorDeclaration:iter:5:clause:1»  input0)]


noncomputable def «Decl_ok:errorDeclaration:iter:6:clause:0» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:errorDeclaration:iter:6:clause:1» (input0 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (let value_error : value := ((value.«ERROR '.' %» nameIR) : value); (.bind (.call ⟨(_root_.List value), SpecTecCall.«Decl_ok:errorDeclaration:iter:6» «tail:0»⟩) (fun («exec:3» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:3»; (.pure (((value_error :: «tail:1») : (_root_.List value)))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:errorDeclaration:iter:6_clauses» (input0 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:errorDeclaration:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:errorDeclaration:iter:6:clause:1»  input0)]


noncomputable def «Decl_ok:errorDeclaration:iter:7:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List varTypeIR)) : (_root_.List varTypeIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:errorDeclaration:iter:7:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_error : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (let varTypeIR : SpecTec.varTypeIR := ((SpecTec.varTypeIR.«% % % %» ((direction._EMPTY) : direction) ((typeIR.ERROR) : typeIR) ((ctk.LCTK) : ctk) (_root_.Option.some value_error)) : SpecTec.varTypeIR); (.bind (.call ⟨(_root_.List SpecTec.varTypeIR), SpecTecCall.«Decl_ok:errorDeclaration:iter:7» «tail:0»⟩) (fun («exec:3» : (_root_.List SpecTec.varTypeIR)) => (let «tail:1» : (_root_.List SpecTec.varTypeIR) := «exec:3»; (.pure (((varTypeIR :: «tail:1») : (_root_.List SpecTec.varTypeIR)))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:errorDeclaration:iter:7_clauses» (input0 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:errorDeclaration:iter:7:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:errorDeclaration:iter:7:clause:1»  input0)]


noncomputable def «Decl_ok:matchKindDeclaration:iter:2:clause:0» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List nameIR)) : (_root_.List nameIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:matchKindDeclaration:iter:2:clause:1» (input0 : (_root_.List SpecTec.name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let name : SpecTec.name := «exec:2»; (let «tail:0» : (_root_.List SpecTec.name) := «exec:1»; (.bind (.call ⟨SpecTec.nameIR, SpecTecCall.«$name» name⟩) (fun («exec:3» : SpecTec.nameIR) => (let «eval:3» : SpecTec.nameIR := «exec:3»; (let nameIR : SpecTec.nameIR := «eval:3»; (.bind (.call ⟨(_root_.List SpecTec.nameIR), SpecTecCall.«Decl_ok:matchKindDeclaration:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.nameIR)) => (let «tail:1» : (_root_.List SpecTec.nameIR) := «exec:4»; (.pure (((nameIR :: «tail:1») : (_root_.List SpecTec.nameIR))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:matchKindDeclaration:iter:2_clauses» (input0 : (_root_.List name)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:matchKindDeclaration:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:matchKindDeclaration:iter:2:clause:1»  input0)]


noncomputable def «Decl_ok:matchKindDeclaration:iter:5:clause:0» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:matchKindDeclaration:iter:5:clause:1» (input0 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (let value_match_kind : value := ((value.«MATCH_KIND '.' %» nameIR) : value); (.bind (.call ⟨(_root_.List value), SpecTecCall.«Decl_ok:matchKindDeclaration:iter:5» «tail:0»⟩) (fun («exec:3» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:3»; (.pure (((value_match_kind :: «tail:1») : (_root_.List value)))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:matchKindDeclaration:iter:5_clauses» (input0 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:matchKindDeclaration:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:matchKindDeclaration:iter:5:clause:1»  input0)]


noncomputable def «Decl_ok:matchKindDeclaration:iter:6:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List varTypeIR)) : (_root_.List varTypeIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:matchKindDeclaration:iter:6:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_match_kind : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (let varTypeIR : SpecTec.varTypeIR := ((SpecTec.varTypeIR.«% % % %» ((direction._EMPTY) : direction) ((typeIR.MATCH_KIND) : typeIR) ((ctk.LCTK) : ctk) (_root_.Option.some value_match_kind)) : SpecTec.varTypeIR); (.bind (.call ⟨(_root_.List SpecTec.varTypeIR), SpecTecCall.«Decl_ok:matchKindDeclaration:iter:6» «tail:0»⟩) (fun («exec:3» : (_root_.List SpecTec.varTypeIR)) => (let «tail:1» : (_root_.List SpecTec.varTypeIR) := «exec:3»; (.pure (((varTypeIR :: «tail:1») : (_root_.List SpecTec.varTypeIR)))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:matchKindDeclaration:iter:6_clauses» (input0 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:matchKindDeclaration:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:matchKindDeclaration:iter:6:clause:1»  input0)]


noncomputable def «Decl_ok:externObjectDeclaration:iter:9:clause:0» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId externMethodTypeDefIR))) : (_root_.List (pair callTargetId externMethodTypeDefIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)

end SpecTec
