import SpecTecDecl0202

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Decl_ok:externObjectDeclaration:iter:9:clause:1» (input0 : (_root_.List callableId)) (input1 : (_root_.List SpecTec.externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableId_method : callableId := «exec:2»; (let «tail:0» : (_root_.List callableId) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.externMethodTypeDefIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:9» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR))) => (let «tail:2» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId_method externMethodTypeDefIR) : (pair callableId SpecTec.externMethodTypeDefIR)) :: «tail:2») : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_ok:externObjectDeclaration:iter:9_clauses» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:externObjectDeclaration:iter:9:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_ok:externObjectDeclaration:iter:9:clause:1»  input0 input1)]


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:3:clause:0» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List nameIR)) : (_root_.List nameIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:3:clause:1» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let name_field : name := «exec:2»; (let «tail:0» : (_root_.List name) := «exec:1»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» name_field⟩) (fun («exec:3» : nameIR) => (let «eval:4» : nameIR := «exec:3»; (let nameIR_field : nameIR := «eval:4»; (.bind (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_ok:enumTypeDeclaration-non-serializable:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List nameIR)) => (let «tail:1» : (_root_.List nameIR) := «exec:4»; (.pure (((nameIR_field :: «tail:1») : (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:3_clauses» (input0 : (_root_.List name)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-non-serializable:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-non-serializable:iter:3:clause:1»  input0)]


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:7:clause:0» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List id)) : (_root_.List id)))) | _ :: _ => .unmatch))


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:7:clause:1» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let nameIR_field : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (let id_field : id := ((nameIR ++ ".") ++ nameIR_field); (.bind (.call ⟨(_root_.List id), SpecTecCall.«Decl_ok:enumTypeDeclaration-non-serializable:iter:7» nameIR «tail:0»⟩) (fun («exec:3» : (_root_.List id)) => (let «tail:1» : (_root_.List id) := «exec:3»; (.pure (((id_field :: «tail:1») : (_root_.List id)))))))))) | [] => .unmatch))


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:7_clauses» (input0 : nameIR) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-non-serializable:iter:7:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-non-serializable:iter:7:clause:1»  input0 input1)]


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:8:clause:0» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch))


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:8:clause:1» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let nameIR_field : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (let value_field : value := ((value.«% '.' %» nameIR nameIR_field) : value); (.bind (.call ⟨(_root_.List value), SpecTecCall.«Decl_ok:enumTypeDeclaration-non-serializable:iter:8» nameIR «tail:0»⟩) (fun («exec:3» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:3»; (.pure (((value_field :: «tail:1») : (_root_.List value)))))))))) | [] => .unmatch))


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:8_clauses» (input0 : nameIR) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-non-serializable:iter:8:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-non-serializable:iter:8:clause:1»  input0 input1)]


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:3:clause:0» (input0 : (_root_.List namedValueIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:3:clause:1» (input0 : (_root_.List namedValueIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let namedValueIR_field : namedValueIR := «exec:2»; (let «tail:0» : (_root_.List namedValueIR) := «exec:1»; (match namedValueIR_field with | .«% '=' %» «exec:3» «exec:4» => (let nameIR_field : nameIR := «exec:3»; (let value_field : value := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Decl_ok:enumTypeDeclaration-serializable:iter:3» «tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «tail:1»), (value_field :: «tail:2»)) : ((_root_.List nameIR) × (_root_.List value)))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:3_clauses» (input0 : (_root_.List namedValueIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-serializable:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-serializable:iter:3:clause:1»  input0)]


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:4:clause:0» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List id)) : (_root_.List id)))) | _ :: _ => .unmatch))


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:4:clause:1» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let nameIR_field : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (let id_field : id := ((nameIR ++ ".") ++ nameIR_field); (.bind (.call ⟨(_root_.List id), SpecTecCall.«Decl_ok:enumTypeDeclaration-serializable:iter:4» nameIR «tail:0»⟩) (fun («exec:3» : (_root_.List id)) => (let «tail:1» : (_root_.List id) := «exec:3»; (.pure (((id_field :: «tail:1») : (_root_.List id)))))))))) | [] => .unmatch))


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:4_clauses» (input0 : nameIR) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-serializable:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-serializable:iter:4:clause:1»  input0 input1)]


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:5:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List valueFieldIR)) : (_root_.List valueFieldIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:5:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List valueFieldIR), SpecTecCall.«Decl_ok:enumTypeDeclaration-serializable:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List valueFieldIR)) => (let «tail:2» : (_root_.List valueFieldIR) := «exec:5»; (.pure (((((valueFieldIR.«% '=' % ';'» nameIR_field value_field) : valueFieldIR) :: «tail:2») : (_root_.List valueFieldIR))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:5_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-serializable:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_ok:enumTypeDeclaration-serializable:iter:5:clause:1»  input0 input1)]


noncomputable def «Decl_ok:structTypeDeclaration:pattern-iter:2:clause:0» (input0 : (_root_.List typeField)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List name)), ([] : (_root_.List type)))) : ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:structTypeDeclaration:pattern-iter:2:clause:1» (input0 : (_root_.List typeField)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList_field : annotationList := «exec:3»; (let type_field : type := «exec:4»; (let name_field : name := «exec:5»; (let «pattern-tail:0» : (_root_.List typeField) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List name) × (_root_.List type))), SpecTecCall.«Decl_ok:structTypeDeclaration:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List name) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List type) := ((«exec:6»).2).2; (.pure ((((annotationList_field :: «pattern-tail:1»), ((name_field :: «pattern-tail:2»), (type_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:structTypeDeclaration:pattern-iter:2_clauses» (input0 : (_root_.List typeField)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:structTypeDeclaration:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:structTypeDeclaration:pattern-iter:2:clause:1»  input0)]


noncomputable def «Decl_ok:structTypeDeclaration:iter:5:clause:0» (input0 : (_root_.List (_root_.List typeId))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:structTypeDeclaration:iter:5:clause:1» (input0 : (_root_.List (_root_.List typeId))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «typeId'*» : (_root_.List typeId) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List typeId)) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeId'*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Decl_ok:structTypeDeclaration:iter:5» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:structTypeDeclaration:iter:5_clauses» (input0 : (_root_.List (_root_.List typeId))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:structTypeDeclaration:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:structTypeDeclaration:iter:5:clause:1»  input0)]


noncomputable def «Decl_ok:structTypeDeclaration:iter:7:clause:0» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List nameIR)) : (_root_.List nameIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:structTypeDeclaration:iter:7:clause:1» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let name_field : name := «exec:2»; (let «tail:0» : (_root_.List name) := «exec:1»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» name_field⟩) (fun («exec:3» : nameIR) => (let «eval:8» : nameIR := «exec:3»; (let nameIR_field : nameIR := «eval:8»; (.bind (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_ok:structTypeDeclaration:iter:7» «tail:0»⟩) (fun («exec:4» : (_root_.List nameIR)) => (let «tail:1» : (_root_.List nameIR) := «exec:4»; (.pure (((nameIR_field :: «tail:1») : (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:structTypeDeclaration:iter:7_clauses» (input0 : (_root_.List name)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:structTypeDeclaration:iter:7:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:structTypeDeclaration:iter:7:clause:1»  input0)]


noncomputable def «Decl_ok:structTypeDeclaration:iter:9:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:structTypeDeclaration:iter:9:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList_field : annotationList := «exec:2»; (let «tail:0» : (_root_.List annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_field : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_field : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_ok:structTypeDeclaration:iter:9» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList_field typeIR_field nameIR_field) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_ok:structTypeDeclaration:iter:9_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:structTypeDeclaration:iter:9:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_ok:structTypeDeclaration:iter:9:clause:1»  input0 input1 input2)]

end SpecTec
