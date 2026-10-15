import SpecTecDecl0215

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$add_callableDef_non_overload_i:case_2:pattern-iter:1:clause:1» (input0 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% `( % `)» «exec:3» «exec:4» => (let id_k : id := «exec:3»; (let «_id'*» : (_root_.List id) := «exec:4»; (let «pattern-tail:0» : (_root_.List callTargetId) := «exec:1»; (.bind (.call ⟨((_root_.List (_root_.List id)) × (_root_.List id)), SpecTecCall.«$add_callableDef_non_overload_i:case_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List (_root_.List id)) × (_root_.List id))) => (let «pattern-tail:1» : (_root_.List (_root_.List id)) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List id) := («exec:5»).2; (.pure ((((«_id'*» :: «pattern-tail:1»), (id_k :: «pattern-tail:2»)) : ((_root_.List (_root_.List id)) × (_root_.List id))))))))))))) | [] => .unmatch)


noncomputable def «$add_callableDef_non_overload_i:case_2:pattern-iter:1_clauses» (input0 : (_root_.List callTargetId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_callableDef_non_overload_i:case_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$add_callableDef_non_overload_i:case_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «$add_constructorDef_i:clause:0» (input0 : instContext) (input1 : SpecTec.callableId) (input2 : SpecTec.constructorDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC : instContext := input0; (let callableId : SpecTec.callableId := input1; (let constructorDef : SpecTec.constructorDef := input2; (.bind (.call ⟨(map SpecTec.callableId SpecTec.constructorDef), SpecTecCall.«$add_map» SpecTec.callableId SpecTec.constructorDef (globalInstLayer.CONSTRUCTOR (instContext.GLOBAL IC)) callableId constructorDef⟩) (fun («exec:1» : (map SpecTec.callableId SpecTec.constructorDef)) => (let «eval:0» : (map SpecTec.callableId SpecTec.constructorDef) := «exec:1»; (let constructorDefEnv : SpecTec.constructorDefEnv := «eval:0»; (.pure ((({ IC with GLOBAL := ({ (instContext.GLOBAL IC) with CONSTRUCTOR := constructorDefEnv } : globalInstLayer) } : instContext) : instContext))))))))))


noncomputable def «$add_constructorDef_i_clauses» (input0 : instContext) (input1 : callableId) (input2 : constructorDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_constructorDef_i:clause:0»  input0 input1 input2)]


noncomputable def «$add_constructorDefs_i:clause:0» (input0 : instContext) (input1 : (_root_.List callableId)) (input2 : (_root_.List constructorDef)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC : instContext := input0; (let «callableId*» : (_root_.List callableId) := input1; (let «constructorDef*» : (_root_.List constructorDef) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «callableId*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «constructorDef*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((IC : instContext))))))))))


noncomputable def «$add_constructorDefs_i:clause:1» (input0 : instContext) (input1 : (_root_.List callableId)) (input2 : (_root_.List constructorDef)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC : instContext := input0; (let «callableId*» : (_root_.List callableId) := input1; (let «constructorDef*» : (_root_.List constructorDef) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «callableId*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «callableId*» with | «exec:2» :: «exec:1» => (let callableId_h : callableId := «exec:2»; (let «callableId_t*» : (_root_.List callableId) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «constructorDef*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «constructorDef*» with | «exec:4» :: «exec:3» => (let constructorDef_h : constructorDef := «exec:4»; (let «constructorDef_t*» : (_root_.List constructorDef) := «exec:3»; (.bind (.call ⟨instContext, SpecTecCall.«$add_constructorDef_i» IC callableId_h constructorDef_h⟩) (fun («exec:5» : instContext) => (let «eval:0» : instContext := «exec:5»; (let IC' : instContext := «eval:0»; (.bind (.call ⟨instContext, SpecTecCall.«$add_constructorDefs_i» IC' «callableId_t*» «constructorDef_t*»⟩) (fun («exec:6» : instContext) => (let «eval:1» : instContext := «exec:6»; (let IC'' : instContext := «eval:1»; (.pure ((IC'' : instContext))))))))))))) | [] => .unmatch))))) | [] => .unmatch))))))


noncomputable def «$add_constructorDefs_i_clauses» (input0 : instContext) (input1 : (_root_.List callableId)) (input2 : (_root_.List constructorDef)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_constructorDefs_i:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$add_constructorDefs_i:clause:1»  input0 input1 input2)]


noncomputable def «Expr_inst:non-default_2:pattern-iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List typedExpressionIR))) : ((_root_.List nameIR) × (_root_.List typedExpressionIR))))) | _ :: _ => .unmatch)


noncomputable def «Expr_inst:non-default_2:pattern-iter:1:clause:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:4»; (let «pattern-tail:0» : (_root_.List namedExpressionIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR)), SpecTecCall.«Expr_inst:non-default_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typedExpressionIR) := («exec:5»).2; (.pure ((((nameIR :: «pattern-tail:1»), (typedExpressionIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))))))))))))) | [] => .unmatch)


noncomputable def «Expr_inst:non-default_2:pattern-iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:non-default_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_inst:non-default_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «Expr_inst:non-default_2:iter:3:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_inst:non-default_2:iter:3:clause:1» (input0 : (_root_.List SpecTec.nameIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_inst:non-default_2:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value nameIR) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_inst:non-default_2:iter:3_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:non-default_2:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_inst:non-default_2:iter:3:clause:1»  input0 input1)]


noncomputable def «Expr_inst:default_2:pattern-iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List typedExpressionIR))) : ((_root_.List nameIR) × (_root_.List typedExpressionIR))))) | _ :: _ => .unmatch)


noncomputable def «Expr_inst:default_2:pattern-iter:1:clause:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:4»; (let «pattern-tail:0» : (_root_.List namedExpressionIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR)), SpecTecCall.«Expr_inst:default_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typedExpressionIR) := («exec:5»).2; (.pure ((((nameIR :: «pattern-tail:1»), (typedExpressionIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))))))))))))) | [] => .unmatch)


noncomputable def «Expr_inst:default_2:pattern-iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:default_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_inst:default_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «Expr_inst:default_2:iter:3:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_inst:default_2:iter:3:clause:1» (input0 : (_root_.List SpecTec.nameIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_inst:default_2:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value nameIR) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_inst:default_2:iter:3_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:default_2:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_inst:default_2:iter:3:clause:1»  input0 input1)]


noncomputable def «Expr_inst:serenum:pattern-iter:5:clause:0» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List value))) : ((_root_.List id) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Expr_inst:serenum:pattern-iter:5:clause:1» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' % ';'» «exec:3» «exec:4» => (let id_member : id := «exec:3»; (let value_member : value := «exec:4»; (let «pattern-tail:0» : (_root_.List valueFieldIR) := «exec:1»; (.bind (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_inst:serenum:pattern-iter:5» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List id) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((id_member :: «pattern-tail:1»), (value_member :: «pattern-tail:2»)) : ((_root_.List id) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Expr_inst:serenum:pattern-iter:5_clauses» (input0 : (_root_.List valueFieldIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:serenum:pattern-iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_inst:serenum:pattern-iter:5:clause:1»  input0)]


noncomputable def «Expr_inst:serenum:iter:7:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_inst:serenum:iter:7:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_member : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_member : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_inst:serenum:iter:7» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((id_member, value_member) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_inst:serenum:iter:7_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:serenum:iter:7:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_inst:serenum:iter:7:clause:1»  input0 input1)]


noncomputable def «Expr_inst:struct:pattern-iter:3:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List value))) : ((_root_.List id) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Expr_inst:struct:pattern-iter:3:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let id_field : id := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_inst:struct:pattern-iter:3» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List id) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((id_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List id) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Expr_inst:struct:pattern-iter:3_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:struct:pattern-iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_inst:struct:pattern-iter:3:clause:1»  input0)]


noncomputable def «Expr_inst:struct:iter:5:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_inst:struct:iter:5:clause:1» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_field : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_inst:struct:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((id_field, value_field) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_inst:struct:iter:5_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_inst:struct:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_inst:struct:iter:5:clause:1»  input0 input1)]


noncomputable def «Expr_inst:header:pattern-iter:3:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List value))) : ((_root_.List id) × (_root_.List value))))) | _ :: _ => .unmatch)

end SpecTec
