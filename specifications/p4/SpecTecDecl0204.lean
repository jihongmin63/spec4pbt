import SpecTecDecl0203

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Decl_ok:structTypeDeclaration:iter:13:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List typeFieldIR)) : (_root_.List typeFieldIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:structTypeDeclaration:iter:13:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList_field : annotationList := «exec:2»; (let «tail:0» : (_root_.List annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_field : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_field : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List typeFieldIR), SpecTecCall.«Decl_ok:structTypeDeclaration:iter:13» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List typeFieldIR)) => (let «tail:3» : (_root_.List typeFieldIR) := «exec:7»; (.pure (((((typeFieldIR.«% % % ';'» annotationList_field typeIR_field nameIR_field) : typeFieldIR) :: «tail:3») : (_root_.List typeFieldIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_ok:structTypeDeclaration:iter:13_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:structTypeDeclaration:iter:13:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_ok:structTypeDeclaration:iter:13:clause:1»  input0 input1 input2)]


noncomputable def «Decl_ok:headerTypeDeclaration:pattern-iter:2:clause:0» (input0 : (_root_.List typeField)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List name)), ([] : (_root_.List type)))) : ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:headerTypeDeclaration:pattern-iter:2:clause:1» (input0 : (_root_.List typeField)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList_f : annotationList := «exec:3»; (let type_f : type := «exec:4»; (let name_f : name := «exec:5»; (let «pattern-tail:0» : (_root_.List typeField) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List name) × (_root_.List type))), SpecTecCall.«Decl_ok:headerTypeDeclaration:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List name) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List type) := ((«exec:6»).2).2; (.pure ((((annotationList_f :: «pattern-tail:1»), ((name_f :: «pattern-tail:2»), (type_f :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:headerTypeDeclaration:pattern-iter:2_clauses» (input0 : (_root_.List typeField)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:headerTypeDeclaration:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:headerTypeDeclaration:pattern-iter:2:clause:1»  input0)]


noncomputable def «Decl_ok:headerTypeDeclaration:iter:5:clause:0» (input0 : (_root_.List (_root_.List typeId))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:headerTypeDeclaration:iter:5:clause:1» (input0 : (_root_.List (_root_.List typeId))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «typeId'*» : (_root_.List typeId) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List typeId)) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeId'*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Decl_ok:headerTypeDeclaration:iter:5» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:headerTypeDeclaration:iter:5_clauses» (input0 : (_root_.List (_root_.List typeId))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:headerTypeDeclaration:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:headerTypeDeclaration:iter:5:clause:1»  input0)]


noncomputable def «Decl_ok:headerTypeDeclaration:iter:7:clause:0» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List nameIR)) : (_root_.List nameIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:headerTypeDeclaration:iter:7:clause:1» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let name_f : name := «exec:2»; (let «tail:0» : (_root_.List name) := «exec:1»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» name_f⟩) (fun («exec:3» : nameIR) => (let «eval:8» : nameIR := «exec:3»; (let nameIR_f : nameIR := «eval:8»; (.bind (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_ok:headerTypeDeclaration:iter:7» «tail:0»⟩) (fun («exec:4» : (_root_.List nameIR)) => (let «tail:1» : (_root_.List nameIR) := «exec:4»; (.pure (((nameIR_f :: «tail:1») : (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:headerTypeDeclaration:iter:7_clauses» (input0 : (_root_.List name)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:headerTypeDeclaration:iter:7:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:headerTypeDeclaration:iter:7:clause:1»  input0)]


noncomputable def «Decl_ok:headerTypeDeclaration:iter:9:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:headerTypeDeclaration:iter:9:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList_f : annotationList := «exec:2»; (let «tail:0» : (_root_.List annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_f : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_f : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_ok:headerTypeDeclaration:iter:9» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList_f typeIR_f nameIR_f) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_ok:headerTypeDeclaration:iter:9_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:headerTypeDeclaration:iter:9:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_ok:headerTypeDeclaration:iter:9:clause:1»  input0 input1 input2)]


noncomputable def «Decl_ok:headerTypeDeclaration:iter:13:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List typeFieldIR)) : (_root_.List typeFieldIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:headerTypeDeclaration:iter:13:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList_f : annotationList := «exec:2»; (let «tail:0» : (_root_.List annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_f : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_f : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List typeFieldIR), SpecTecCall.«Decl_ok:headerTypeDeclaration:iter:13» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List typeFieldIR)) => (let «tail:3» : (_root_.List typeFieldIR) := «exec:7»; (.pure (((((typeFieldIR.«% % % ';'» annotationList_f typeIR_f nameIR_f) : typeFieldIR) :: «tail:3») : (_root_.List typeFieldIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_ok:headerTypeDeclaration:iter:13_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:headerTypeDeclaration:iter:13:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_ok:headerTypeDeclaration:iter:13:clause:1»  input0 input1 input2)]


noncomputable def «Decl_ok:headerUnionTypeDeclaration:pattern-iter:2:clause:0» (input0 : (_root_.List typeField)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List name)), ([] : (_root_.List type)))) : ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:headerUnionTypeDeclaration:pattern-iter:2:clause:1» (input0 : (_root_.List typeField)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList_f : annotationList := «exec:3»; (let type_f : type := «exec:4»; (let name_f : name := «exec:5»; (let «pattern-tail:0» : (_root_.List typeField) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List name) × (_root_.List type))), SpecTecCall.«Decl_ok:headerUnionTypeDeclaration:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List name) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List type) := ((«exec:6»).2).2; (.pure ((((annotationList_f :: «pattern-tail:1»), ((name_f :: «pattern-tail:2»), (type_f :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:headerUnionTypeDeclaration:pattern-iter:2_clauses» (input0 : (_root_.List typeField)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:headerUnionTypeDeclaration:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:headerUnionTypeDeclaration:pattern-iter:2:clause:1»  input0)]


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:5:clause:0» (input0 : (_root_.List (_root_.List typeId))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:5:clause:1» (input0 : (_root_.List (_root_.List typeId))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «typeId'*» : (_root_.List typeId) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List typeId)) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeId'*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Decl_ok:headerUnionTypeDeclaration:iter:5» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:5_clauses» (input0 : (_root_.List (_root_.List typeId))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:headerUnionTypeDeclaration:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:headerUnionTypeDeclaration:iter:5:clause:1»  input0)]


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:7:clause:0» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List nameIR)) : (_root_.List nameIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:7:clause:1» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let name_f : name := «exec:2»; (let «tail:0» : (_root_.List name) := «exec:1»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» name_f⟩) (fun («exec:3» : nameIR) => (let «eval:8» : nameIR := «exec:3»; (let nameIR_f : nameIR := «eval:8»; (.bind (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_ok:headerUnionTypeDeclaration:iter:7» «tail:0»⟩) (fun («exec:4» : (_root_.List nameIR)) => (let «tail:1» : (_root_.List nameIR) := «exec:4»; (.pure (((nameIR_f :: «tail:1») : (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:7_clauses» (input0 : (_root_.List name)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:headerUnionTypeDeclaration:iter:7:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:headerUnionTypeDeclaration:iter:7:clause:1»  input0)]


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:9:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:9:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList_f : annotationList := «exec:2»; (let «tail:0» : (_root_.List annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_f : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_f : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_ok:headerUnionTypeDeclaration:iter:9» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList_f typeIR_f nameIR_f) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:9_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:headerUnionTypeDeclaration:iter:9:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_ok:headerUnionTypeDeclaration:iter:9:clause:1»  input0 input1 input2)]


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:13:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List typeFieldIR)) : (_root_.List typeFieldIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:13:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList_f : annotationList := «exec:2»; (let «tail:0» : (_root_.List annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_f : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_f : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List typeFieldIR), SpecTecCall.«Decl_ok:headerUnionTypeDeclaration:iter:13» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List typeFieldIR)) => (let «tail:3» : (_root_.List typeFieldIR) := «exec:7»; (.pure (((((typeFieldIR.«% % % ';'» annotationList_f typeIR_f nameIR_f) : typeFieldIR) :: «tail:3») : (_root_.List typeFieldIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)

end SpecTec
