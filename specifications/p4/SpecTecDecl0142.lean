import SpecTecDecl0141

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$cast_struct:case_1:pattern-iter:0_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_struct:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_struct:case_1:pattern-iter:0:clause:1»  input0)]


noncomputable def «$cast_struct:case_1:iter:3:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_struct:case_1:iter:3:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_struct:case_1:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value_field nameIR_field) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_struct:case_1:iter:3_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_struct:case_1:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_struct:case_1:iter:3:clause:1»  input0 input1)]


noncomputable def «$cast_header:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$cast_header:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let nameIR_field : nameIR := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_header:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «$cast_header:case_1:pattern-iter:0_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_header:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_header:case_1:pattern-iter:0:clause:1»  input0)]


noncomputable def «$cast_header:case_1:iter:3:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_header:case_1:iter:3:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_header:case_1:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value_field nameIR_field) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_header:case_1:iter:3_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_header:case_1:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_header:case_1:iter:3:clause:1»  input0 input1)]


noncomputable def «$cast_header_union:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$cast_header_union:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let nameIR_field : nameIR := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_header_union:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «$cast_header_union:case_1:pattern-iter:0_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_header_union:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_header_union:case_1:pattern-iter:0:clause:1»  input0)]


noncomputable def «$cast_header_union:case_1:iter:3:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_header_union:case_1:iter:3:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_header_union:case_1:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value_field nameIR_field) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_header_union:case_1:iter:3_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_header_union:case_1:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_header_union:case_1:iter:3:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_7:iter:5:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_7:iter:5:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_cast : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_sequence:case_7:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value_cast nameIR_field) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_7:iter:5_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_7:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_7:iter:5:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_8:iter:5:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_8:iter:5:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_cast : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_sequence:case_8:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value_cast nameIR_field) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_8:iter:5_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_8:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_8:iter:5:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_13:iter:8:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_13:iter:8:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_cast : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_sequence:case_13:iter:8» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value_cast nameIR_field) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_13:iter:8_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_13:iter:8:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_13:iter:8:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_14:iter:8:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List fieldValue)) : (_root_.List fieldValue)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_14:iter:8:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_cast : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List fieldValue), SpecTecCall.«$cast_sequence:case_14:iter:8» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List fieldValue)) => (let «tail:2» : (_root_.List fieldValue) := «exec:5»; (.pure (((((fieldValue.«% % ';'» value_cast nameIR_field) : fieldValue) :: «tail:2») : (_root_.List fieldValue))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_14:iter:8_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_14:iter:8:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_14:iter:8:clause:1»  input0 input1)]


noncomputable def «$cast_record:case_1:pattern-iter:3:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$cast_record:case_1:pattern-iter:3:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % ';'» «exec:3» «exec:4» => (let value_field : value := «exec:3»; (let nameIR_field : nameIR := «exec:4»; (let «pattern-tail:0» : (_root_.List fieldValue) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$cast_record:case_1:pattern-iter:3» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field :: «pattern-tail:1»), (value_field :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «$cast_record:case_1:pattern-iter:3_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_record:case_1:pattern-iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_record:case_1:pattern-iter:3:clause:1»  input0)]


noncomputable def «$cast_record:case_1:iter:6:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String value))) : (_root_.List (pair _root_.String value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)

end SpecTec
