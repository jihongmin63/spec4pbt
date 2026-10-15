import SpecTecDecl0332

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$cast_sequence:case_6:iter:1:clause:1» (input0 : SpecTec.typeIR) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let value : SpecTec.value := «exec:2»; (let «tail:0» : (_root_.List SpecTec.value) := «exec:1»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_op» typeIR value⟩) (fun («exec:3» : SpecTec.value) => (let «eval:2» : SpecTec.value := «exec:3»; (let value_cast : SpecTec.value := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.value), SpecTecCall.«$cast_sequence:case_6:iter:1» typeIR «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.value)) => (let «tail:1» : (_root_.List SpecTec.value) := «exec:4»; (.pure (((value_cast :: «tail:1») : (_root_.List SpecTec.value))))))))))))) | [] => .unmatch))


noncomputable def «$cast_sequence:case_6:iter:1_clauses» (input0 : typeIR) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_6:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_6:iter:1:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_7:iter:3:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_7:iter:3:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_op» typeIR_field value⟩) (fun («exec:5» : SpecTec.value) => (let «eval:4» : SpecTec.value := «exec:5»; (let value_cast : SpecTec.value := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.value), SpecTecCall.«$cast_sequence:case_7:iter:3» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.value)) => (let «tail:2» : (_root_.List SpecTec.value) := «exec:6»; (.pure (((value_cast :: «tail:2») : (_root_.List SpecTec.value))))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_7:iter:3_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_7:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_7:iter:3:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_8:iter:3:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_8:iter:3:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_op» typeIR_field value⟩) (fun («exec:5» : SpecTec.value) => (let «eval:4» : SpecTec.value := «exec:5»; (let value_cast : SpecTec.value := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.value), SpecTecCall.«$cast_sequence:case_8:iter:3» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.value)) => (let «tail:2» : (_root_.List SpecTec.value) := «exec:6»; (.pure (((value_cast :: «tail:2») : (_root_.List SpecTec.value))))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_8:iter:3_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_8:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_8:iter:3:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_9:iter:1:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_9:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_op» typeIR value⟩) (fun («exec:5» : SpecTec.value) => (let «eval:2» : SpecTec.value := «exec:5»; (let value_cast : SpecTec.value := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.value), SpecTecCall.«$cast_sequence:case_9:iter:1» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.value)) => (let «tail:2» : (_root_.List SpecTec.value) := «exec:6»; (.pure (((value_cast :: «tail:2») : (_root_.List SpecTec.value))))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_9:iter:1_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_9:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_9:iter:1:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_10:iter:2:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_10:iter:2:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_given : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_op» typeIR_given value⟩) (fun («exec:5» : SpecTec.value) => (let «eval:3» : SpecTec.value := «exec:5»; (let value_given : SpecTec.value := «eval:3»; (.bind (.call ⟨(_root_.List SpecTec.value), SpecTecCall.«$cast_sequence:case_10:iter:2» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.value)) => (let «tail:2» : (_root_.List SpecTec.value) := «exec:6»; (.pure (((value_given :: «tail:2») : (_root_.List SpecTec.value))))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_10:iter:2_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_10:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_10:iter:2:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_10:iter:4:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_10:iter:4:clause:1» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_rest : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨value, SpecTecCall.«$default» typeIR_rest⟩) (fun («exec:3» : value) => (let «eval:5» : value := «exec:3»; (let value_rest : value := «eval:5»; (.bind (.call ⟨(_root_.List value), SpecTecCall.«$cast_sequence:case_10:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:4»; (.pure (((value_rest :: «tail:1») : (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_10:iter:4_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_10:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_sequence:case_10:iter:4:clause:1»  input0)]


noncomputable def «$cast_sequence:case_11:iter:1:clause:0» (input0 : SpecTec.typeIR) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch))


noncomputable def «$cast_sequence:case_11:iter:1:clause:1» (input0 : SpecTec.typeIR) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let value : SpecTec.value := «exec:2»; (let «tail:0» : (_root_.List SpecTec.value) := «exec:1»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_op» typeIR value⟩) (fun («exec:3» : SpecTec.value) => (let «eval:2» : SpecTec.value := «exec:3»; (let value_given : SpecTec.value := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.value), SpecTecCall.«$cast_sequence:case_11:iter:1» typeIR «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.value)) => (let «tail:1» : (_root_.List SpecTec.value) := «exec:4»; (.pure (((value_given :: «tail:1») : (_root_.List SpecTec.value))))))))))))) | [] => .unmatch))


noncomputable def «$cast_sequence:case_11:iter:1_clauses» (input0 : typeIR) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_11:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_11:iter:1:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_12:iter:1:clause:0» (input0 : SpecTec.typeIR) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (match input1 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch))


noncomputable def «$cast_sequence:case_12:iter:1:clause:1» (input0 : SpecTec.typeIR) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (match input1 with | «exec:2» :: «exec:1» => (let value : SpecTec.value := «exec:2»; (let «tail:0» : (_root_.List SpecTec.value) := «exec:1»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_op» typeIR value⟩) (fun («exec:3» : SpecTec.value) => (let «eval:2» : SpecTec.value := «exec:3»; (let value_given : SpecTec.value := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.value), SpecTecCall.«$cast_sequence:case_12:iter:1» typeIR «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.value)) => (let «tail:1» : (_root_.List SpecTec.value) := «exec:4»; (.pure (((value_given :: «tail:1») : (_root_.List SpecTec.value))))))))))))) | [] => .unmatch))


noncomputable def «$cast_sequence:case_12:iter:1_clauses» (input0 : typeIR) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_12:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_12:iter:1:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_13:iter:4:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_13:iter:4:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field_given : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_op» typeIR_field_given value⟩) (fun («exec:5» : SpecTec.value) => (let «eval:5» : SpecTec.value := «exec:5»; (let value_given : SpecTec.value := «eval:5»; (.bind (.call ⟨(_root_.List SpecTec.value), SpecTecCall.«$cast_sequence:case_13:iter:4» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.value)) => (let «tail:2» : (_root_.List SpecTec.value) := «exec:6»; (.pure (((value_given :: «tail:2») : (_root_.List SpecTec.value))))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_13:iter:4_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_13:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_13:iter:4:clause:1»  input0 input1)]


noncomputable def «$cast_sequence:case_13:iter:6:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_13:iter:6:clause:1» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field_rest : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨value, SpecTecCall.«$default» typeIR_field_rest⟩) (fun («exec:3» : value) => (let «eval:7» : value := «exec:3»; (let value_rest : value := «eval:7»; (.bind (.call ⟨(_root_.List value), SpecTecCall.«$cast_sequence:case_13:iter:6» «tail:0»⟩) (fun («exec:4» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:4»; (.pure (((value_rest :: «tail:1») : (_root_.List value))))))))))))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_13:iter:6_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_13:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_sequence:case_13:iter:6:clause:1»  input0)]


noncomputable def «$cast_sequence:case_14:iter:4:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_14:iter:4:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List SpecTec.value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field_given : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value : SpecTec.value := «exec:4»; (let «tail:1» : (_root_.List SpecTec.value) := «exec:3»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_op» typeIR_field_given value⟩) (fun («exec:5» : SpecTec.value) => (let «eval:5» : SpecTec.value := «exec:5»; (let value_given : SpecTec.value := «eval:5»; (.bind (.call ⟨(_root_.List SpecTec.value), SpecTecCall.«$cast_sequence:case_14:iter:4» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List SpecTec.value)) => (let «tail:2» : (_root_.List SpecTec.value) := «exec:6»; (.pure (((value_given :: «tail:2») : (_root_.List SpecTec.value))))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_14:iter:4_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_14:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$cast_sequence:case_14:iter:4:clause:1»  input0 input1)]

end SpecTec
