import SpecTecDecl0327

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$bin_eq:case_14:iter:4:clause:1» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_field_a : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field_b : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» value_field_a value_field_b⟩) (fun («exec:5» : _root_.Bool) => (let «eval:5» : _root_.Bool := «exec:5»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_14:iter:4» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List _root_.Bool)) => (let «tail:2» : (_root_.List _root_.Bool) := «exec:6»; (.pure (((«eval:5» :: «tail:2») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$bin_eq:case_14:iter:4_clauses» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_14:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$bin_eq:case_14:iter:4:clause:1»  input0 input1)]


noncomputable def «$bin_eq:case_15:iter:4:clause:0» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$bin_eq:case_15:iter:4:clause:1» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_field_a : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field_b : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» value_field_a value_field_b⟩) (fun («exec:5» : _root_.Bool) => (let «eval:5» : _root_.Bool := «exec:5»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_15:iter:4» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List _root_.Bool)) => (let «tail:2» : (_root_.List _root_.Bool) := «exec:6»; (.pure (((«eval:5» :: «tail:2») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$bin_eq:case_15:iter:4_clauses» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_15:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$bin_eq:case_15:iter:4:clause:1»  input0 input1)]


noncomputable def «$bin_eq:case_16:iter:4:clause:0» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$bin_eq:case_16:iter:4:clause:1» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_field_a : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field_b : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» value_field_a value_field_b⟩) (fun («exec:5» : _root_.Bool) => (let «eval:5» : _root_.Bool := «exec:5»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_16:iter:4» «tail:0» «tail:1»⟩) (fun («exec:6» : (_root_.List _root_.Bool)) => (let «tail:2» : (_root_.List _root_.Bool) := «exec:6»; (.pure (((«eval:5» :: «tail:2») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$bin_eq:case_16:iter:4_clauses» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_16:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$bin_eq:case_16:iter:4:clause:1»  input0 input1)]


noncomputable def «$bin_ne:clause:0» (input0 : value) (input1 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value_l : value := input0; (let value_r : value := input1; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» value_l value_r⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure (((!«eval:0») : _root_.Bool))))))))


noncomputable def «$bin_ne_clauses» (input0 : value) (input1 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_ne:clause:0»  input0 input1)]


noncomputable def «$bin_op:clause:0» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'+'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_plus» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:1» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'|+|'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_satplus» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:2» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'-'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_minus» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:3» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'|-|'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_satminus» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:4» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'*'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_mul» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:5» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'/'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_div» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:6» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'%'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_mod» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:7» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'<<'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_shl» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:8» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'>>'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_shr» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:9» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'<='» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_le» value_l value_r⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((((value._B «eval:0») : value) : value)))))))))))


noncomputable def «$bin_op:clause:10» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'>='» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_ge» value_l value_r⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((((value._B «eval:0») : value) : value)))))))))))


noncomputable def «$bin_op:clause:11» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'<'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_lt» value_l value_r⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((((value._B «eval:0») : value) : value)))))))))))


noncomputable def «$bin_op:clause:12» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'>'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_gt» value_l value_r⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((((value._B «eval:0») : value) : value)))))))))))


noncomputable def «$bin_op:clause:13» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'=='» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_eq» value_l value_r⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((((value._B «eval:0») : value) : value)))))))))))


noncomputable def «$bin_op:clause:14» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'!='» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$bin_ne» value_l value_r⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((((value._B «eval:0») : value) : value)))))))))))


noncomputable def «$bin_op:clause:15» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'&'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_band» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:16» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'^'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_bxor» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:17» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'|'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_bor» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op:clause:18» (input0 : SpecTec.binop) (input1 : value) (input2 : value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let binop : SpecTec.binop := input0; (let value_l : value := input1; (let value_r : value := input2; (.bind (.guard (((«exec:match:binop:'++'» binop) = true))) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$bin_concat» value_l value_r⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value)))))))))))


noncomputable def «$bin_op_clauses» (input0 : binop) (input1 : value) (input2 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_op:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:3»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:4»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:5»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:6»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:7»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:8»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:9»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:10»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:11»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:12»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:13»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:14»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:15»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:16»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:17»  input0 input1 input2), fun (_ : _root_.Unit) => («$bin_op:clause:18»  input0 input1 input2)]


noncomputable def «$cast_op:clause:0» (input0 : SpecTec.typeIR) (input1 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let value : SpecTec.value := input1; (.bind (.guard (((«sub:value:boolValue» value) = true))) (fun (_ : Unit) => (match («$cast_op:case_1:downcast:0» value) with | some «exec:1» => (let «eval:0» : SpecTec.boolValue := «exec:1»; (let boolValue : SpecTec.boolValue := «eval:0»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$unroll_typeIR» typeIR⟩) (fun («exec:2» : SpecTec.typeIR) => (let «eval:1» : SpecTec.typeIR := «exec:2»; (let typeIR_unroll : SpecTec.typeIR := «eval:1»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_bool» typeIR_unroll boolValue⟩) (fun («exec:3» : SpecTec.value) => (let «eval:2» : SpecTec.value := «exec:3»; (.pure ((«eval:2» : SpecTec.value)))))))))))) | none => .unmatch)))))


noncomputable def «$cast_op:clause:1» (input0 : SpecTec.typeIR) (input1 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let value : SpecTec.value := input1; (.bind (.guard (((«sub:value:integerValue» value) = true))) (fun (_ : Unit) => (match («$cast_op:case_2:downcast:0» value) with | some «exec:1» => (let «eval:0» : SpecTec.integerValue := «exec:1»; (let integerValue : SpecTec.integerValue := «eval:0»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$unroll_typeIR» typeIR⟩) (fun («exec:2» : SpecTec.typeIR) => (let «eval:1» : SpecTec.typeIR := «exec:2»; (let typeIR_unroll : SpecTec.typeIR := «eval:1»; (.bind (.call ⟨SpecTec.value, SpecTecCall.«$cast_int» typeIR_unroll integerValue⟩) (fun («exec:3» : SpecTec.value) => (let «eval:2» : SpecTec.value := «exec:3»; (.pure ((«eval:2» : SpecTec.value)))))))))))) | none => .unmatch)))))

end SpecTec
