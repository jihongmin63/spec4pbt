import SpecTecDecl0140

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$bin_eq:case_15:iter:2:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$bin_eq:case_15:iter:2:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let fieldValue_a : fieldValue := «exec:2»; (let «tail:0» : (_root_.List fieldValue) := «exec:1»; (match fieldValue_a with | .«% % ';'» «exec:3» «exec:4» => (let value_field_a : value := «exec:3»; (let nameIR_field_a : nameIR := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_15:iter:2» «tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field_a :: «tail:1»), (value_field_a :: «tail:2»)) : ((_root_.List nameIR) × (_root_.List value)))))))))))))) | [] => .unmatch)


noncomputable def «$bin_eq:case_15:iter:2_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_15:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$bin_eq:case_15:iter:2:clause:1»  input0)]


noncomputable def «$bin_eq:case_15:iter:3:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$bin_eq:case_15:iter:3:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let fieldValue_b : fieldValue := «exec:2»; (let «tail:0» : (_root_.List fieldValue) := «exec:1»; (match fieldValue_b with | .«% % ';'» «exec:3» «exec:4» => (let value_field_b : value := «exec:3»; (let nameIR_field_b : nameIR := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_15:iter:3» «tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field_b :: «tail:1»), (value_field_b :: «tail:2»)) : ((_root_.List nameIR) × (_root_.List value)))))))))))))) | [] => .unmatch)


noncomputable def «$bin_eq:case_15:iter:3_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_15:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$bin_eq:case_15:iter:3:clause:1»  input0)]


noncomputable def «$bin_eq:case_15:iter:8:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$bin_eq:case_15:iter:8:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field_a : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_field_b : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_15:iter:8» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List _root_.Bool)) => (let «tail:2» : (_root_.List _root_.Bool) := «exec:5»; (.pure ((((_root_.Decidable.decide (nameIR_field_a = nameIR_field_b)) :: «tail:2») : (_root_.List _root_.Bool))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$bin_eq:case_15:iter:8_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_15:iter:8:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$bin_eq:case_15:iter:8:clause:1»  input0 input1)]


noncomputable def «$bin_eq:case_16:iter:2:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$bin_eq:case_16:iter:2:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let fieldValue_a : fieldValue := «exec:2»; (let «tail:0» : (_root_.List fieldValue) := «exec:1»; (match fieldValue_a with | .«% % ';'» «exec:3» «exec:4» => (let value_field_a : value := «exec:3»; (let nameIR_field_a : nameIR := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_16:iter:2» «tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field_a :: «tail:1»), (value_field_a :: «tail:2»)) : ((_root_.List nameIR) × (_root_.List value)))))))))))))) | [] => .unmatch)


noncomputable def «$bin_eq:case_16:iter:2_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_16:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$bin_eq:case_16:iter:2:clause:1»  input0)]


noncomputable def «$bin_eq:case_16:iter:3:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$bin_eq:case_16:iter:3:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let fieldValue_b : fieldValue := «exec:2»; (let «tail:0» : (_root_.List fieldValue) := «exec:1»; (match fieldValue_b with | .«% % ';'» «exec:3» «exec:4» => (let value_field_b : value := «exec:3»; (let nameIR_field_b : nameIR := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_16:iter:3» «tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field_b :: «tail:1»), (value_field_b :: «tail:2»)) : ((_root_.List nameIR) × (_root_.List value)))))))))))))) | [] => .unmatch)


noncomputable def «$bin_eq:case_16:iter:3_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_16:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$bin_eq:case_16:iter:3:clause:1»  input0)]


noncomputable def «$bin_eq:case_16:iter:8:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$bin_eq:case_16:iter:8:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field_a : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_field_b : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_16:iter:8» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List _root_.Bool)) => (let «tail:2» : (_root_.List _root_.Bool) := «exec:5»; (.pure ((((_root_.Decidable.decide (nameIR_field_a = nameIR_field_b)) :: «tail:2») : (_root_.List _root_.Bool))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$bin_eq:case_16:iter:8_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_16:iter:8:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$bin_eq:case_16:iter:8:clause:1»  input0 input1)]


noncomputable def «$default:case_17:pattern-iter:1:clause:0» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$default:case_17:pattern-iter:1:clause:1» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' % ';'» «exec:3» «exec:4» => (let nameIR_field : nameIR := «exec:3»; (let value_field : value := «exec:4»; (let «pattern-tail:0» : (_root_.List valueFieldIR) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$default:case_17:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «$default:case_17:pattern-iter:1_clauses» (input0 : (_root_.List valueFieldIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:case_17:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$default:case_17:pattern-iter:1:clause:1»  input0)]


noncomputable def «$default:case_17:iter:4:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (value × _root_.String))) : (_root_.List (value × _root_.String))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$default:case_17:iter:4:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (value × _root_.String)), SpecTecCall.«$default:case_17:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (value × _root_.String))) => (let «tail:2» : (_root_.List (value × _root_.String)) := «exec:5»; (.pure ((((value_field, nameIR_field) :: «tail:2») : (_root_.List (value × _root_.String)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$default:case_17:iter:4_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:case_17:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$default:case_17:iter:4:clause:1»  input0 input1)]


noncomputable def «$default:case_18:pattern-iter:1:clause:0» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$default:case_18:pattern-iter:1:clause:1» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' % ';'» «exec:3» «exec:4» => (let nameIR_field : nameIR := «exec:3»; (let value_field : value := «exec:4»; (let «pattern-tail:0» : (_root_.List valueFieldIR) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$default:case_18:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «$default:case_18:pattern-iter:1_clauses» (input0 : (_root_.List valueFieldIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:case_18:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$default:case_18:pattern-iter:1:clause:1»  input0)]


noncomputable def «$default:case_18:iter:4:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (value × _root_.String))) : (_root_.List (value × _root_.String))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$default:case_18:iter:4:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (value × _root_.String)), SpecTecCall.«$default:case_18:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (value × _root_.String))) => (let «tail:2» : (_root_.List (value × _root_.String)) := «exec:5»; (.pure ((((value_field, nameIR_field) :: «tail:2») : (_root_.List (value × _root_.String)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$default:case_18:iter:4_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:case_18:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$default:case_18:iter:4:clause:1»  input0 input1)]


noncomputable def «$cast_struct:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$cast_struct:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let nameIR_field : nameIR := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_struct:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)

end SpecTec
