import SpecTecDecl0181

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «ConstructorType_wf:packageObjectTypeIR:iter:4_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ConstructorType_wf:packageObjectTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («ConstructorType_wf:packageObjectTypeIR:iter:4:clause:1»  input0)]


noncomputable def «$definable_constructor:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$definable_constructor:matches:0:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$definable_constructor» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$definable_constructor:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$definable_constructor:matches:1:row» externObjectTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$definable_constructor:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$definable_constructor:matches:2:row» parserObjectTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$definable_constructor:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$definable_constructor:matches:3:row» controlObjectTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$definable_constructor:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let packageObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$definable_constructor:matches:4:row» packageObjectTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$definable_constructor:clause:5» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$definable_constructor:matches:5:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$definable_constructor_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$definable_constructor:clause:0»  input0), fun (_ : _root_.Unit) => («$definable_constructor:clause:1»  input0), fun (_ : _root_.Unit) => («$definable_constructor:clause:2»  input0), fun (_ : _root_.Unit) => («$definable_constructor:clause:3»  input0), fun (_ : _root_.Unit) => («$definable_constructor:clause:4»  input0), fun (_ : _root_.Unit) => («$definable_constructor:clause:5»  input0)]


noncomputable def «Expr_eval_lctk:non-default_2:pattern-iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List typedExpressionIR))) : ((_root_.List nameIR) × (_root_.List typedExpressionIR))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:non-default_2:pattern-iter:1:clause:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:4»; (let «pattern-tail:0» : (_root_.List namedExpressionIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR)), SpecTecCall.«Expr_eval_lctk:non-default_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typedExpressionIR) := («exec:5»).2; (.pure ((((nameIR :: «pattern-tail:1»), (typedExpressionIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:non-default_2:pattern-iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:non-default_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval_lctk:non-default_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «Expr_eval_lctk:non-default_2:iter:4:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:non-default_2:iter:4:clause:1» (input0 : (_root_.List SpecTec.nameIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_eval_lctk:non-default_2:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value nameIR) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:non-default_2:iter:4_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:non-default_2:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_eval_lctk:non-default_2:iter:4:clause:1»  input0 input1)]


noncomputable def «Expr_eval_lctk:default_2:pattern-iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List typedExpressionIR))) : ((_root_.List nameIR) × (_root_.List typedExpressionIR))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:default_2:pattern-iter:1:clause:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:4»; (let «pattern-tail:0» : (_root_.List namedExpressionIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR)), SpecTecCall.«Expr_eval_lctk:default_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typedExpressionIR) := («exec:5»).2; (.pure ((((nameIR :: «pattern-tail:1»), (typedExpressionIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:default_2:pattern-iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:default_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval_lctk:default_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «Expr_eval_lctk:default_2:iter:4:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:default_2:iter:4:clause:1» (input0 : (_root_.List SpecTec.nameIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_eval_lctk:default_2:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value nameIR) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:default_2:iter:4_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:default_2:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_eval_lctk:default_2:iter:4:clause:1»  input0 input1)]


noncomputable def «Expr_eval_lctk:serenum:pattern-iter:6:clause:0» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:serenum:pattern-iter:6:clause:1» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' % ';'» «exec:3» «exec:4» => (let nameIR_field : nameIR := «exec:3»; (let value_field : value := «exec:4»; (let «pattern-tail:0» : (_root_.List valueFieldIR) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Expr_eval_lctk:serenum:pattern-iter:6» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:serenum:pattern-iter:6_clauses» (input0 : (_root_.List valueFieldIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:serenum:pattern-iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval_lctk:serenum:pattern-iter:6:clause:1»  input0)]


noncomputable def «Expr_eval_lctk:serenum:iter:8:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:serenum:iter:8:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval_lctk:serenum:iter:8» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((nameIR_field, value_field) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:serenum:iter:8_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:serenum:iter:8:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_eval_lctk:serenum:iter:8:clause:1»  input0 input1)]


noncomputable def «Expr_eval_lctk:struct:pattern-iter:3:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:struct:pattern-iter:3:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let nameIR_field : nameIR := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Expr_eval_lctk:struct:pattern-iter:3» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:struct:pattern-iter:3_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:struct:pattern-iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval_lctk:struct:pattern-iter:3:clause:1»  input0)]


noncomputable def «Expr_eval_lctk:struct:iter:5:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:struct:iter:5:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval_lctk:struct:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((nameIR_field, value_field) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:struct:iter:5_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:struct:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_eval_lctk:struct:iter:5:clause:1»  input0 input1)]

end SpecTec
