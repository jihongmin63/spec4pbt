import SpecTecDecl0216

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Expr_inst:header:pattern-iter:3:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let id_field : id := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_inst:header:pattern-iter:3» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List id) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((id_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List id) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Expr_inst:header:pattern-iter:3_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:header:pattern-iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_inst:header:pattern-iter:3:clause:1»  input0)]


noncomputable def «Expr_inst:header:iter:5:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_inst:header:iter:5:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_field : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_inst:header:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((id_field, value_field) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_inst:header:iter:5_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:header:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_inst:header:iter:5:clause:1»  input0 input1)]


noncomputable def «Expr_inst:header-union:pattern-iter:3:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List value))) : ((_root_.List id) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Expr_inst:header-union:pattern-iter:3:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let id_field : id := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_inst:header-union:pattern-iter:3» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List id) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((id_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List id) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Expr_inst:header-union:pattern-iter:3_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:header-union:pattern-iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_inst:header-union:pattern-iter:3:clause:1»  input0)]


noncomputable def «Expr_inst:header-union:iter:5:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_inst:header-union:iter:5:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_field : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_inst:header-union:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((id_field, value_field) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_inst:header-union:iter:5_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:header-union:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_inst:header-union:iter:5:clause:1»  input0 input1)]


noncomputable def «Decl_inst:errorDeclarationIR:iter:1:clause:0» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List nameIR)) : (_root_.List nameIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:errorDeclarationIR:iter:1:clause:1» (input0 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (.bind (.call ⟨_root_.String, SpecTecCall.«$concat_text» (["error.", nameIR] : (_root_.List _root_.String))⟩) (fun («exec:3» : _root_.String) => (let «eval:2» : _root_.String := «exec:3»; (let nameIR_error : SpecTec.nameIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.nameIR), SpecTecCall.«Decl_inst:errorDeclarationIR:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.nameIR)) => (let «tail:1» : (_root_.List SpecTec.nameIR) := «exec:4»; (.pure (((nameIR_error :: «tail:1») : (_root_.List SpecTec.nameIR))))))))))))) | [] => .unmatch)


noncomputable def «Decl_inst:errorDeclarationIR:iter:1_clauses» (input0 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:errorDeclarationIR:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:errorDeclarationIR:iter:1:clause:1»  input0)]


noncomputable def «Decl_inst:errorDeclarationIR:iter:3:clause:0» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:errorDeclarationIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (let value_error : value := ((value.«ERROR '.' %» nameIR) : value); (.bind (.call ⟨(_root_.List value), SpecTecCall.«Decl_inst:errorDeclarationIR:iter:3» «tail:0»⟩) (fun («exec:3» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:3»; (.pure (((value_error :: «tail:1») : (_root_.List value)))))))))) | [] => .unmatch)


noncomputable def «Decl_inst:errorDeclarationIR:iter:3_clauses» (input0 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:errorDeclarationIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:errorDeclarationIR:iter:3:clause:1»  input0)]


noncomputable def «Decl_inst:matchKindDeclarationIR:iter:1:clause:0» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:matchKindDeclarationIR:iter:1:clause:1» (input0 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (let value_match_kind : value := ((value.«MATCH_KIND '.' %» nameIR) : value); (.bind (.call ⟨(_root_.List value), SpecTecCall.«Decl_inst:matchKindDeclarationIR:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:3»; (.pure (((value_match_kind :: «tail:1») : (_root_.List value)))))))))) | [] => .unmatch)


noncomputable def «Decl_inst:matchKindDeclarationIR:iter:1_clauses» (input0 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:matchKindDeclarationIR:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:matchKindDeclarationIR:iter:1:clause:1»  input0)]


noncomputable def «Decl_inst:non-constructor:iter:5:clause:0» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId externMethodTypeDefIR))) : (_root_.List (pair callTargetId externMethodTypeDefIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:non-constructor:iter:5:clause:1» (input0 : (_root_.List callableId)) (input1 : (_root_.List SpecTec.externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableId_method : callableId := «exec:2»; (let «tail:0» : (_root_.List callableId) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.externMethodTypeDefIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)), SpecTecCall.«Decl_inst:non-constructor:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR))) => (let «tail:2» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId_method externMethodTypeDefIR) : (pair callableId SpecTec.externMethodTypeDefIR)) :: «tail:2») : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_inst:non-constructor:iter:5_clauses» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:non-constructor:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_inst:non-constructor:iter:5:clause:1»  input0 input1)]


noncomputable def «Decl_inst:constructor:iter:5:clause:0» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId externMethodTypeDefIR))) : (_root_.List (pair callTargetId externMethodTypeDefIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:constructor:iter:5:clause:1» (input0 : (_root_.List callableId)) (input1 : (_root_.List SpecTec.externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableId_method : callableId := «exec:2»; (let «tail:0» : (_root_.List callableId) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.externMethodTypeDefIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)), SpecTecCall.«Decl_inst:constructor:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR))) => (let «tail:2» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId_method externMethodTypeDefIR) : (pair callableId SpecTec.externMethodTypeDefIR)) :: «tail:2») : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Decl_inst:constructor:iter:5_clauses» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:constructor:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_inst:constructor:iter:5:clause:1»  input0 input1)]


noncomputable def «Decl_inst:enumTypeDeclarationIR-non-serializable:iter:1:clause:0» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List SpecTec.nameIR)) : (_root_.List SpecTec.nameIR)))) | _ :: _ => .unmatch))


noncomputable def «Decl_inst:enumTypeDeclarationIR-non-serializable:iter:1:clause:1» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let nameIR_field : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (let nameIR_enum_field : SpecTec.nameIR := ((nameIR ++ ".") ++ nameIR_field); (.bind (.call ⟨(_root_.List SpecTec.nameIR), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-non-serializable:iter:1» nameIR «tail:0»⟩) (fun («exec:3» : (_root_.List SpecTec.nameIR)) => (let «tail:1» : (_root_.List SpecTec.nameIR) := «exec:3»; (.pure (((nameIR_enum_field :: «tail:1») : (_root_.List SpecTec.nameIR)))))))))) | [] => .unmatch))


noncomputable def «Decl_inst:enumTypeDeclarationIR-non-serializable:iter:1_clauses» (input0 : nameIR) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-non-serializable:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-non-serializable:iter:1:clause:1»  input0 input1)]


noncomputable def «Decl_inst:enumTypeDeclarationIR-non-serializable:iter:2:clause:0» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch))


noncomputable def «Decl_inst:enumTypeDeclarationIR-non-serializable:iter:2:clause:1» (input0 : SpecTec.nameIR) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let nameIR_field : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (let value_enum_field : value := ((value.«% '.' %» nameIR nameIR_field) : value); (.bind (.call ⟨(_root_.List value), SpecTecCall.«Decl_inst:enumTypeDeclarationIR-non-serializable:iter:2» nameIR «tail:0»⟩) (fun («exec:3» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:3»; (.pure (((value_enum_field :: «tail:1») : (_root_.List value)))))))))) | [] => .unmatch))


noncomputable def «Decl_inst:enumTypeDeclarationIR-non-serializable:iter:2_clauses» (input0 : nameIR) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-non-serializable:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Decl_inst:enumTypeDeclarationIR-non-serializable:iter:2:clause:1»  input0 input1)]

end SpecTec
