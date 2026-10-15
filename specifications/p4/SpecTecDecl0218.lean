import SpecTecDecl0217

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:pattern-iter:1:clause:0» (input0 : (_root_.List namedValueIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:pattern-iter:1:clause:1» (input0 : (_root_.List namedValueIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let nameIR_field : nameIR := «exec:3»; (let value_field : value := «exec:4»; (let «pattern-tail:0» : (_root_.List namedValueIR) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-serializable:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:pattern-iter:1_clauses» (input0 : (_root_.List namedValueIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-serializable:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-serializable:pattern-iter:1:clause:1»  input0)]


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:3:clause:0» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List SpecTec.nameIR)) : (_root_.List SpecTec.nameIR)))) | _ :: _ => .unmatch))


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:3:clause:1» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let nameIR_field : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (let nameIR_serenum_field : SpecTec.nameIR := ((nameIR ++ ".") ++ nameIR_field); (.bind (.call ⟨(_root_.List SpecTec.nameIR), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-serializable:iter:3» nameIR «tail:0»⟩) (fun («exec:3» : (_root_.List SpecTec.nameIR)) => (let «tail:1» : (_root_.List SpecTec.nameIR) := «exec:3»; (.pure (((nameIR_serenum_field :: «tail:1») : (_root_.List SpecTec.nameIR)))))))))) | [] => .unmatch))


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:3_clauses» (input0 : nameIR) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-serializable:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-serializable:iter:3:clause:1»  input0 input1)]


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:4:clause:0» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) (input2 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch))


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:4:clause:1» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) (input2 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let nameIR_field : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (match input2 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (let value_serenum_field : value := ((value.«% '.' % '.' %» nameIR nameIR_field value_field) : value); (.bind (.call ⟨(_root_.List value), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-serializable:iter:4» nameIR «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List value)) => (let «tail:2» : (_root_.List value) := «exec:5»; (.pure (((value_serenum_field :: «tail:2») : (_root_.List value)))))))))) | [] => .unmatch))) | [] => .unmatch))


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:4_clauses» (input0 : nameIR) (input1 : (_root_.List nameIR)) (input2 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-serializable:iter:4:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-serializable:iter:4:clause:1»  input0 input1 input2)]


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:6:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List valueFieldIR)) : (_root_.List valueFieldIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:6:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List valueFieldIR), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-serializable:iter:6» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List valueFieldIR)) => (let «tail:2» : (_root_.List valueFieldIR) := «exec:5»; (.pure (((((valueFieldIR.«% '=' % ';'» nameIR_field value_field) : valueFieldIR) :: «tail:2») : (_root_.List valueFieldIR))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_inst:enumTypeDeclarationIR-serializable:iter:6_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-serializable:iter:6:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-serializable:iter:6:clause:1»  input0 input1)]


noncomputable def «Decl_inst:structTypeDeclarationIR:iter:1:clause:0» (input0 : (_root_.List typeFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:structTypeDeclarationIR:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeFieldIR : SpecTec.typeFieldIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeFieldIR) := «exec:1»; (match typeFieldIR with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList_field : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Decl_inst:structTypeDeclarationIR:iter:1» «tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList_field :: «tail:1»), ((nameIR_field :: «tail:2»), (typeIR_field :: «tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))))))))))))))))) | [] => .unmatch)


noncomputable def «Decl_inst:structTypeDeclarationIR:iter:1_clauses» (input0 : (_root_.List typeFieldIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:structTypeDeclarationIR:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:structTypeDeclarationIR:iter:1:clause:1»  input0)]


noncomputable def «Decl_inst:structTypeDeclarationIR:iter:2:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:structTypeDeclarationIR:iter:2:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList_field : annotationList := «exec:2»; (let «tail:0» : (_root_.List annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_field : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_field : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_inst:structTypeDeclarationIR:iter:2» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList_field typeIR_field nameIR_field) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_inst:structTypeDeclarationIR:iter:2_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:structTypeDeclarationIR:iter:2:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_inst:structTypeDeclarationIR:iter:2:clause:1»  input0 input1 input2)]


noncomputable def «Decl_inst:headerTypeDeclarationIR:iter:1:clause:0» (input0 : (_root_.List typeFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:headerTypeDeclarationIR:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeFieldIR : SpecTec.typeFieldIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeFieldIR) := «exec:1»; (match typeFieldIR with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList_field : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Decl_inst:headerTypeDeclarationIR:iter:1» «tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList_field :: «tail:1»), ((nameIR_field :: «tail:2»), (typeIR_field :: «tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))))))))))))))))) | [] => .unmatch)


noncomputable def «Decl_inst:headerTypeDeclarationIR:iter:1_clauses» (input0 : (_root_.List typeFieldIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:headerTypeDeclarationIR:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:headerTypeDeclarationIR:iter:1:clause:1»  input0)]


noncomputable def «Decl_inst:headerTypeDeclarationIR:iter:2:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:headerTypeDeclarationIR:iter:2:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList_field : annotationList := «exec:2»; (let «tail:0» : (_root_.List annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_field : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_field : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_inst:headerTypeDeclarationIR:iter:2» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList_field typeIR_field nameIR_field) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_inst:headerTypeDeclarationIR:iter:2_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:headerTypeDeclarationIR:iter:2:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_inst:headerTypeDeclarationIR:iter:2:clause:1»  input0 input1 input2)]


noncomputable def «Decl_inst:headerUnionTypeDeclarationIR:iter:1:clause:0» (input0 : (_root_.List typeFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:headerUnionTypeDeclarationIR:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeFieldIR : SpecTec.typeFieldIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeFieldIR) := «exec:1»; (match typeFieldIR with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList_field : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Decl_inst:headerUnionTypeDeclarationIR:iter:1» «tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList_field :: «tail:1»), ((nameIR_field :: «tail:2»), (typeIR_field :: «tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))))))))))))))))) | [] => .unmatch)


noncomputable def «Decl_inst:headerUnionTypeDeclarationIR:iter:1_clauses» (input0 : (_root_.List typeFieldIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:headerUnionTypeDeclarationIR:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:headerUnionTypeDeclarationIR:iter:1:clause:1»  input0)]


noncomputable def «Decl_inst:headerUnionTypeDeclarationIR:iter:2:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:headerUnionTypeDeclarationIR:iter:2:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList_field : annotationList := «exec:2»; (let «tail:0» : (_root_.List annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_field : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_field : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_inst:headerUnionTypeDeclarationIR:iter:2» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList_field typeIR_field nameIR_field) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_inst:headerUnionTypeDeclarationIR:iter:2_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:headerUnionTypeDeclarationIR:iter:2:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_inst:headerUnionTypeDeclarationIR:iter:2:clause:1»  input0 input1 input2)]


noncomputable def «Decl_inst:packageTypeDeclarationIR:iter:1:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:packageTypeDeclarationIR:iter:1:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«Decl_inst:packageTypeDeclarationIR:iter:1» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)

end SpecTec
