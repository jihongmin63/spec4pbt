import SpecTecDecl0198

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Expr_ok:multiple-non-default:iter:16_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:multiple-non-default:iter:16:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_ok:multiple-non-default:iter:16:clause:1»  input0 input1)]


noncomputable def «Expr_ok:multiple-default:pattern-iter:3:clause:0» (input0 : (_root_.List namedExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List expression)), ([] : (_root_.List name))) : ((_root_.List expression) × (_root_.List name))))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:multiple-default:pattern-iter:3:clause:1» (input0 : (_root_.List namedExpression)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let name_f_t : name := «exec:3»; (let expression_f_t : expression := «exec:4»; (let «pattern-tail:0» : (_root_.List namedExpression) := «exec:1»; (.bind (.call ⟨((_root_.List expression) × (_root_.List name)), SpecTecCall.«Expr_ok:multiple-default:pattern-iter:3» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List expression) × (_root_.List name))) => (let «pattern-tail:1» : (_root_.List expression) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List name) := («exec:5»).2; (.pure ((((expression_f_t :: «pattern-tail:1»), (name_f_t :: «pattern-tail:2»)) : ((_root_.List expression) × (_root_.List name))))))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:multiple-default:pattern-iter:3_clauses» (input0 : (_root_.List namedExpression)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:multiple-default:pattern-iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:multiple-default:pattern-iter:3:clause:1»  input0)]


noncomputable def «Expr_ok:multiple-default:iter:5:clause:0» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List nameIR)) : (_root_.List nameIR)))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:multiple-default:iter:5:clause:1» (input0 : (_root_.List name)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let name_f : name := «exec:2»; (let «tail:0» : (_root_.List name) := «exec:1»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» name_f⟩) (fun («exec:3» : nameIR) => (let «eval:6» : nameIR := «exec:3»; (let nameIR_f : nameIR := «eval:6»; (.bind (.call ⟨(_root_.List nameIR), SpecTecCall.«Expr_ok:multiple-default:iter:5» «tail:0»⟩) (fun («exec:4» : (_root_.List nameIR)) => (let «tail:1» : (_root_.List nameIR) := «exec:4»; (.pure (((nameIR_f :: «tail:1») : (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:multiple-default:iter:5_clauses» (input0 : (_root_.List name)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:multiple-default:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:multiple-default:iter:5:clause:1»  input0)]


noncomputable def «Expr_ok:multiple-default:iter:9:clause:0» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:multiple-default:iter:9:clause:1» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typedExpressionIR_f : typedExpressionIR := «exec:2»; (let «tail:0» : (_root_.List typedExpressionIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$type_of_typedExpressionIR» typedExpressionIR_f⟩) (fun («exec:3» : typeIR) => (let «eval:10» : typeIR := «exec:3»; (let typeIR_f : typeIR := «eval:10»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«Expr_ok:multiple-default:iter:9» «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_f :: «tail:1») : (_root_.List typeIR))))))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:multiple-default:iter:9_clauses» (input0 : (_root_.List typedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:multiple-default:iter:9:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:multiple-default:iter:9:clause:1»  input0)]


noncomputable def «Expr_ok:multiple-default:iter:11:clause:0» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List ctk)) : (_root_.List ctk)))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:multiple-default:iter:11:clause:1» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typedExpressionIR_f : typedExpressionIR := «exec:2»; (let «tail:0» : (_root_.List typedExpressionIR) := «exec:1»; (.bind (.call ⟨ctk, SpecTecCall.«$ctk_of_typedExpressionIR» typedExpressionIR_f⟩) (fun («exec:3» : ctk) => (let «eval:12» : ctk := «exec:3»; (let ctk_f : ctk := «eval:12»; (.bind (.call ⟨(_root_.List ctk), SpecTecCall.«Expr_ok:multiple-default:iter:11» «tail:0»⟩) (fun («exec:4» : (_root_.List ctk)) => (let «tail:1» : (_root_.List ctk) := «exec:4»; (.pure (((ctk_f :: «tail:1») : (_root_.List ctk))))))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:multiple-default:iter:11_clauses» (input0 : (_root_.List typedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:multiple-default:iter:11:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:multiple-default:iter:11:clause:1»  input0)]


noncomputable def «Expr_ok:multiple-default:iter:13:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:multiple-default:iter:13:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_f : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_f : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Expr_ok:multiple-default:iter:13» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldTypeIR)) => (let «tail:2» : (_root_.List fieldTypeIR) := «exec:5»; (.pure (((((fieldTypeIR.«% % % ';'» ((annotationList._EMPTY) : annotationList) typeIR_f nameIR_f) : fieldTypeIR) :: «tail:2») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_ok:multiple-default:iter:13_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:multiple-default:iter:13:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_ok:multiple-default:iter:13:clause:1»  input0 input1)]


noncomputable def «Expr_ok:multiple-default:iter:16:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List namedExpressionIR)) : (_root_.List namedExpressionIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:multiple-default:iter:16:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_f : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typedExpressionIR_f : typedExpressionIR := «exec:4»; (let «tail:1» : (_root_.List typedExpressionIR) := «exec:3»; (.bind (.call ⟨(_root_.List namedExpressionIR), SpecTecCall.«Expr_ok:multiple-default:iter:16» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List namedExpressionIR)) => (let «tail:2» : (_root_.List namedExpressionIR) := «exec:5»; (.pure (((((namedExpressionIR.«% '=' %» nameIR_f typedExpressionIR_f) : namedExpressionIR) :: «tail:2») : (_root_.List namedExpressionIR))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_ok:multiple-default:iter:16_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:multiple-default:iter:16:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_ok:multiple-default:iter:16:clause:1»  input0 input1)]


noncomputable def «Expr_ok:serenum:pattern-iter:8:clause:0» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List value)), ([] : (_root_.List nameIR))) : ((_root_.List value) × (_root_.List nameIR))))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:serenum:pattern-iter:8:clause:1» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' % ';'» «exec:3» «exec:4» => (let nameIR_field : nameIR := «exec:3»; (let _value : value := «exec:4»; (let «pattern-tail:0» : (_root_.List valueFieldIR) := «exec:1»; (.bind (.call ⟨((_root_.List value) × (_root_.List nameIR)), SpecTecCall.«Expr_ok:serenum:pattern-iter:8» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List value) × (_root_.List nameIR))) => (let «pattern-tail:1» : (_root_.List value) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List nameIR) := («exec:5»).2; (.pure ((((_value :: «pattern-tail:1»), (nameIR_field :: «pattern-tail:2»)) : ((_root_.List value) × (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:serenum:pattern-iter:8_clauses» (input0 : (_root_.List valueFieldIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:serenum:pattern-iter:8:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:serenum:pattern-iter:8:clause:1»  input0)]


noncomputable def «Expr_ok:struct:pattern-iter:6:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:struct:pattern-iter:6:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_f : typeIR := «exec:4»; (let nameIR_f : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Expr_ok:struct:pattern-iter:6» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_f :: «pattern-tail:2»), (typeIR_f :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:struct:pattern-iter:6_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:struct:pattern-iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:struct:pattern-iter:6:clause:1»  input0)]


noncomputable def «Expr_ok:struct:iter:9:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × typeIR))) : (_root_.List (_root_.String × typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:struct:iter:9:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_f : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_f : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × typeIR)), SpecTecCall.«Expr_ok:struct:iter:9» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × typeIR))) => (let «tail:2» : (_root_.List (_root_.String × typeIR)) := «exec:5»; (.pure ((((nameIR_f, typeIR_f) :: «tail:2») : (_root_.List (_root_.String × typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_ok:struct:iter:9_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:struct:iter:9:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_ok:struct:iter:9:clause:1»  input0 input1)]


noncomputable def «Expr_ok:header:pattern-iter:6:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Expr_ok:header:pattern-iter:6:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_f : typeIR := «exec:4»; (let nameIR_f : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Expr_ok:header:pattern-iter:6» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_f :: «pattern-tail:2»), (typeIR_f :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Expr_ok:header:pattern-iter:6_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_ok:header:pattern-iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_ok:header:pattern-iter:6:clause:1»  input0)]


noncomputable def «Expr_ok:header:iter:9:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × typeIR))) : (_root_.List (_root_.String × typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)

end SpecTec
