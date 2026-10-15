import SpecTecDecl0222

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Expr_eval:non-default-cont_2:pattern-iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:non-default-cont_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval:non-default-cont_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «Expr_eval:non-default-cont_2:iter:4:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:non-default-cont_2:iter:4:clause:1» (input0 : (_root_.List SpecTec.nameIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_eval:non-default-cont_2:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value nameIR) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval:non-default-cont_2:iter:4_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:non-default-cont_2:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_eval:non-default-cont_2:iter:4:clause:1»  input0 input1)]


noncomputable def «Expr_eval:default-abort_2:pattern-iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List typedExpressionIR))) : ((_root_.List nameIR) × (_root_.List typedExpressionIR))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:default-abort_2:pattern-iter:1:clause:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:4»; (let «pattern-tail:0» : (_root_.List namedExpressionIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR)), SpecTecCall.«Expr_eval:default-abort_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typedExpressionIR) := («exec:5»).2; (.pure ((((nameIR :: «pattern-tail:1»), (typedExpressionIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval:default-abort_2:pattern-iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:default-abort_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval:default-abort_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «Expr_eval:default-cont_2:pattern-iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List typedExpressionIR))) : ((_root_.List nameIR) × (_root_.List typedExpressionIR))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:default-cont_2:pattern-iter:1:clause:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:4»; (let «pattern-tail:0» : (_root_.List namedExpressionIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR)), SpecTecCall.«Expr_eval:default-cont_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typedExpressionIR) := («exec:5»).2; (.pure ((((nameIR :: «pattern-tail:1»), (typedExpressionIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval:default-cont_2:pattern-iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:default-cont_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval:default-cont_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «Expr_eval:default-cont_2:iter:4:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:default-cont_2:iter:4:clause:1» (input0 : (_root_.List SpecTec.nameIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_eval:default-cont_2:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value nameIR) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval:default-cont_2:iter:4_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:default-cont_2:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_eval:default-cont_2:iter:4:clause:1»  input0 input1)]


noncomputable def «Expr_eval:serenum:pattern-iter:5:clause:0» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:serenum:pattern-iter:5:clause:1» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' % ';'» «exec:3» «exec:4» => (let nameIR_member : nameIR := «exec:3»; (let value_member : value := «exec:4»; (let «pattern-tail:0» : (_root_.List valueFieldIR) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Expr_eval:serenum:pattern-iter:5» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_member :: «pattern-tail:1»), (value_member :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval:serenum:pattern-iter:5_clauses» (input0 : (_root_.List valueFieldIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:serenum:pattern-iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval:serenum:pattern-iter:5:clause:1»  input0)]


noncomputable def «Expr_eval:serenum:iter:7:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:serenum:iter:7:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_member : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_member : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval:serenum:iter:7» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((nameIR_member, value_member) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval:serenum:iter:7_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:serenum:iter:7:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_eval:serenum:iter:7:clause:1»  input0 input1)]


noncomputable def «Expr_eval:struct:pattern-iter:4:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List value))) : ((_root_.List id) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:struct:pattern-iter:4:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let id_field : id := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_eval:struct:pattern-iter:4» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List id) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((id_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List id) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval:struct:pattern-iter:4_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:struct:pattern-iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval:struct:pattern-iter:4:clause:1»  input0)]


noncomputable def «Expr_eval:struct:iter:6:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:struct:iter:6:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_field : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval:struct:iter:6» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((id_field, value_field) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval:struct:iter:6_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:struct:iter:6:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_eval:struct:iter:6:clause:1»  input0 input1)]


noncomputable def «Expr_eval:header:pattern-iter:4:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List value))) : ((_root_.List id) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:header:pattern-iter:4:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let id_field : id := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_eval:header:pattern-iter:4» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List id) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((id_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List id) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval:header:pattern-iter:4_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:header:pattern-iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval:header:pattern-iter:4:clause:1»  input0)]


noncomputable def «Expr_eval:header:iter:6:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:header:iter:6:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_field : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval:header:iter:6» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((id_field, value_field) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval:header:iter:6_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:header:iter:6:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_eval:header:iter:6:clause:1»  input0 input1)]


noncomputable def «Expr_eval:headerunion:pattern-iter:4:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List value))) : ((_root_.List id) × (_root_.List value))))) | _ :: _ => .unmatch)

end SpecTec
