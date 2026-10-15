import SpecTecDecl0182

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Expr_eval_lctk:header:pattern-iter:3:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:header:pattern-iter:3:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let nameIR_field : nameIR := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Expr_eval_lctk:header:pattern-iter:3» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:header:pattern-iter:3_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:header:pattern-iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval_lctk:header:pattern-iter:3:clause:1»  input0)]


noncomputable def «Expr_eval_lctk:header:iter:5:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:header:iter:5:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval_lctk:header:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((nameIR_field, value_field) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:header:iter:5_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:header:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_eval_lctk:header:iter:5:clause:1»  input0 input1)]


noncomputable def «Expr_eval_lctk:header-union:pattern-iter:3:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:header-union:pattern-iter:3:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let nameIR_field : nameIR := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Expr_eval_lctk:header-union:pattern-iter:3» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:header-union:pattern-iter:3_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:header-union:pattern-iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval_lctk:header-union:pattern-iter:3:clause:1»  input0)]


noncomputable def «Expr_eval_lctk:header-union:iter:5:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:header-union:iter:5:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval_lctk:header-union:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((nameIR_field, value_field) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:header-union:iter:5_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:header-union:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Expr_eval_lctk:header-union:iter:5:clause:1»  input0 input1)]


noncomputable def «Expr_eval_lctk:static_assert:iter:4:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List nameIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:static_assert:iter:4:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let nameIR_param : nameIR := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))), SpecTecCall.«Expr_eval_lctk:static_assert:iter:4» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List nameIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((_typeIR :: «tail:4»), (nameIR_param :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:static_assert:iter:4_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:static_assert:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval_lctk:static_assert:iter:4:clause:1»  input0)]


noncomputable def «Expr_eval_lctk:static_assert:iter:8:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List direction)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × ((_root_.List nameIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:static_assert:iter:8:clause:1» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_aligned : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (match parameterIR_aligned with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList' : annotationList := «exec:3»; (let direction_param_aligned : direction := «exec:4»; (let typeIR_param_aligned : typeIR := «exec:5»; (let nameIR_param_aligned : nameIR := «exec:6»; (let _parameterInitializerOptIR' : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × ((_root_.List nameIR) × (_root_.List typeIR))))), SpecTecCall.«Expr_eval_lctk:static_assert:iter:8» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × ((_root_.List nameIR) × (_root_.List typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List parameterInitializerOptIR) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List direction) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List nameIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList' :: «tail:1»), ((_parameterInitializerOptIR' :: «tail:2»), ((direction_param_aligned :: «tail:3»), ((nameIR_param_aligned :: «tail:4»), (typeIR_param_aligned :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × ((_root_.List nameIR) × (_root_.List typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:static_assert:iter:8_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:static_assert:iter:8:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval_lctk:static_assert:iter:8:clause:1»  input0)]


noncomputable def «Expr_eval_lctk:static_assert:iter:9:clause:0» (input0 : (_root_.List direction)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List varTypeIR)) : (_root_.List varTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Expr_eval_lctk:static_assert:iter:9:clause:1» (input0 : (_root_.List direction)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let direction_param_aligned : direction := «exec:2»; (let «tail:0» : (_root_.List direction) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_param_aligned : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let value_argument : value := «exec:6»; (let «tail:2» : (_root_.List value) := «exec:5»; (let varTypeIR : SpecTec.varTypeIR := ((SpecTec.varTypeIR.«% % % %» direction_param_aligned typeIR_param_aligned ((ctk.LCTK) : ctk) (_root_.Option.some value_argument)) : SpecTec.varTypeIR); (.bind (.call ⟨(_root_.List SpecTec.varTypeIR), SpecTecCall.«Expr_eval_lctk:static_assert:iter:9» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List SpecTec.varTypeIR)) => (let «tail:3» : (_root_.List SpecTec.varTypeIR) := «exec:7»; (.pure (((varTypeIR :: «tail:3») : (_root_.List SpecTec.varTypeIR)))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Expr_eval_lctk:static_assert:iter:9_clauses» (input0 : (_root_.List direction)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval_lctk:static_assert:iter:9:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Expr_eval_lctk:static_assert:iter:9:clause:1»  input0 input1 input2)]


noncomputable def «TypeParameterListOpt_ok:rule:iter:1:clause:0» (input0 : (_root_.List typeParameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeId)) : (_root_.List typeId)))) | _ :: _ => .unmatch)


noncomputable def «TypeParameterListOpt_ok:rule:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeParameter)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameter : SpecTec.typeParameter := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeParameter) := «exec:1»; (.bind (.call ⟨nameIR, SpecTecCall.«$name» typeParameter⟩) (fun («exec:3» : nameIR) => (let «eval:2» : nameIR := «exec:3»; (let typeId : SpecTec.typeId := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.typeId), SpecTecCall.«TypeParameterListOpt_ok:rule:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeId)) => (let «tail:1» : (_root_.List SpecTec.typeId) := «exec:4»; (.pure (((typeId :: «tail:1») : (_root_.List SpecTec.typeId))))))))))))) | [] => .unmatch)


noncomputable def «TypeParameterListOpt_ok:rule:iter:1_clauses» (input0 : (_root_.List typeParameter)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («TypeParameterListOpt_ok:rule:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («TypeParameterListOpt_ok:rule:iter:1:clause:1»  input0)]


noncomputable def «Cast_expl_neq:listTypeIR:iter:4:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:listTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:listTypeIR:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:listTypeIR:iter:4_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:listTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:listTypeIR:iter:4:clause:1»  input0)]


noncomputable def «Cast_expl_neq:tupleTypeIR:iter:4:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:tupleTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:tupleTypeIR:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:tupleTypeIR:iter:4_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:tupleTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:tupleTypeIR:iter:4:clause:1»  input0)]


noncomputable def «Cast_expl_neq:arrayTypeIR:iter:4:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:arrayTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (match castResult with | .OK «exec:3» => (let «typeIR_cast*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«Cast_expl_neq:arrayTypeIR:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List typeIR))) => (let «tail:1» : (_root_.List (_root_.List typeIR)) := «exec:4»; (.pure (((«typeIR_cast*» :: «tail:1») : (_root_.List (_root_.List typeIR))))))))) | _ => .unmatch))) | [] => .unmatch)

end SpecTec
