import SpecTecDecl0199

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Expr_ok:header:iter:9:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_f : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_f : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Expr_ok:header:iter:9» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × typeIR))) => (let «tail:2» : (_root_.List (_root_.String × typeIR)) := «exec:5»; (.pure ((((nameIR_f, typeIR_f) :: «tail:2») : (_root_.List (_root_.String × typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_ok:header:iter:9_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:header:iter:9:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_ok:header:iter:9:clause:1»  input0 input1)]


noncomputable def «Expr_ok:header-union:pattern-iter:6:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:header-union:pattern-iter:6:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_f : typeIR := «exec:4»; (let nameIR_f : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Expr_ok:header-union:pattern-iter:6» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_f :: «pattern-tail:2»), (typeIR_f :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:header-union:pattern-iter:6_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:header-union:pattern-iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:header-union:pattern-iter:6:clause:1»  input0)]


noncomputable def «Expr_ok:header-union:iter:9:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × typeIR))) : (_root_.List (_root_.String × typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:header-union:iter:9:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_f : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_f : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Expr_ok:header-union:iter:9» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × typeIR))) => (let «tail:2» : (_root_.List (_root_.String × typeIR)) := «exec:5»; (.pure ((((nameIR_f, typeIR_f) :: «tail:2») : (_root_.List (_root_.String × typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_ok:header-union:iter:9_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:header-union:iter:9:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_ok:header-union:iter:9:clause:1»  input0 input1)]


noncomputable def «Expr_ok:non-typeArgumentList-static_assert:iter:2:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:non-typeArgumentList-static_assert:iter:2:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_infer : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:non-typeArgumentList-static_assert:iter:2» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeId_infer) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:non-typeArgumentList-static_assert:iter:2_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:non-typeArgumentList-static_assert:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:non-typeArgumentList-static_assert:iter:2:clause:1»  input0)]


noncomputable def «Expr_ok:non-typeArgumentList:iter:2:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:non-typeArgumentList:iter:2:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_infer : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:non-typeArgumentList:iter:2» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeId_infer) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:non-typeArgumentList:iter:2_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:non-typeArgumentList:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:non-typeArgumentList:iter:2:clause:1»  input0)]


noncomputable def «Expr_ok:typeArgumentList:iter:2:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:typeArgumentList:iter:2:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_inserted : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:typeArgumentList:iter:2» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeId_inserted) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:typeArgumentList:iter:2_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:typeArgumentList:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:typeArgumentList:iter:2:clause:1»  input0)]


noncomputable def «Expr_ok:prefixedTypeName:iter:3:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:prefixedTypeName:iter:3:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_impl : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:prefixedTypeName:iter:3» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeId_impl) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:prefixedTypeName:iter:3_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:prefixedTypeName:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:prefixedTypeName:iter:3:clause:1»  input0)]


noncomputable def «Expr_ok:specializedType:iter:3:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:specializedType:iter:3:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_inserted : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:specializedType:iter:3» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeId_inserted) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:specializedType:iter:3_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:specializedType:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:specializedType:iter:3:clause:1»  input0)]


noncomputable def «Lvalue_ok:structTypeIR:pattern-iter:2:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Lvalue_ok:structTypeIR:pattern-iter:2:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Lvalue_ok:structTypeIR:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Lvalue_ok:structTypeIR:pattern-iter:2_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Lvalue_ok:structTypeIR:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Lvalue_ok:structTypeIR:pattern-iter:2:clause:1»  input0)]


noncomputable def «Lvalue_ok:structTypeIR:iter:5:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × typeIR))) : (_root_.List (_root_.String × typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Lvalue_ok:structTypeIR:iter:5:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_field : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Lvalue_ok:structTypeIR:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × typeIR))) => (let «tail:2» : (_root_.List (_root_.String × typeIR)) := «exec:5»; (.pure ((((nameIR_field, typeIR_field) :: «tail:2») : (_root_.List (_root_.String × typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Lvalue_ok:structTypeIR:iter:5_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Lvalue_ok:structTypeIR:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Lvalue_ok:structTypeIR:iter:5:clause:1»  input0 input1)]


noncomputable def «Lvalue_ok:headerTypeIR:pattern-iter:2:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Lvalue_ok:headerTypeIR:pattern-iter:2:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Lvalue_ok:headerTypeIR:pattern-iter:2» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Lvalue_ok:headerTypeIR:pattern-iter:2_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Lvalue_ok:headerTypeIR:pattern-iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Lvalue_ok:headerTypeIR:pattern-iter:2:clause:1»  input0)]

end SpecTec
