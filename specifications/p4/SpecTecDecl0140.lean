import SpecTecDecl0139

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Type_alpha:serializable:iter:4_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:serializable:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:serializable:iter:4:clause:1»  input0 input1)]


noncomputable def «Type_alpha:non-default_2:iter:6:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List annotationList)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:non-default_2:iter:6:clause:1» (input0 : (_root_.List SpecTec.annotationList)) (input1 : (_root_.List SpecTec.annotationList)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList : SpecTec.annotationList := «exec:2»; (let «tail:0» : (_root_.List SpecTec.annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let annotationList' : SpecTec.annotationList := «exec:4»; (let «tail:1» : (_root_.List SpecTec.annotationList) := «exec:3»; (.bind (.guard (annotationList = annotationList')) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:non-default_2:iter:6» «tail:0» «tail:1»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:non-default_2:iter:6_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List annotationList)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:non-default_2:iter:6:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:non-default_2:iter:6:clause:1»  input0 input1)]


noncomputable def «Type_alpha:non-default_2:iter:7:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:non-default_2:iter:7:clause:1» (input0 : (_root_.List SpecTec.nameIR)) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR : SpecTec.nameIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.nameIR) := «exec:3»; (.bind (.guard (nameIR_field = nameIR)) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:non-default_2:iter:7» «tail:0» «tail:1»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:non-default_2:iter:7_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:non-default_2:iter:7:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:non-default_2:iter:7:clause:1»  input0 input1)]


noncomputable def «Type_alpha:default_2:iter:6:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List annotationList)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:default_2:iter:6:clause:1» (input0 : (_root_.List SpecTec.annotationList)) (input1 : (_root_.List SpecTec.annotationList)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList : SpecTec.annotationList := «exec:2»; (let «tail:0» : (_root_.List SpecTec.annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let annotationList' : SpecTec.annotationList := «exec:4»; (let «tail:1» : (_root_.List SpecTec.annotationList) := «exec:3»; (.bind (.guard (annotationList = annotationList')) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:default_2:iter:6» «tail:0» «tail:1»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:default_2:iter:6_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List annotationList)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:default_2:iter:6:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:default_2:iter:6:clause:1»  input0 input1)]


noncomputable def «Type_alpha:default_2:iter:7:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Type_alpha:default_2:iter:7:clause:1» (input0 : (_root_.List SpecTec.nameIR)) (input1 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR : SpecTec.nameIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.nameIR) := «exec:3»; (.bind (.guard (nameIR_field = nameIR)) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Type_alpha:default_2:iter:7» «tail:0» «tail:1»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Type_alpha:default_2:iter:7_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_alpha:default_2:iter:7:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Type_alpha:default_2:iter:7:clause:1»  input0 input1)]


noncomputable def «$shl:clause:0» (input0 : _root_.Int) (input1 : _root_.Int) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let base : _root_.Int := input0; (let offset : _root_.Int := input1; (.bind (.guard ((offset ≤ (2048 : _root_.Int)))) (fun (_ : Unit) => (.pure (((_root_.Nat.repeat (fun (value : _root_.Int) => (value * (2 : _root_.Int))) (_root_.Int.toNat offset) base) : _root_.Int)))))))


noncomputable def «$shl_clauses» (input0 : _root_.Int) (input1 : _root_.Int) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$shl:clause:0»  input0 input1)]


noncomputable def «$shr:clause:0» (input0 : _root_.Int) (input1 : _root_.Int) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let base : _root_.Int := input0; (let offset : _root_.Int := input1; (.bind (.guard ((offset ≤ (2048 : _root_.Int)))) (fun (_ : Unit) => (.pure (((_root_.Nat.repeat (fun (value : _root_.Int) => (_root_.Int.tdiv value (2 : _root_.Int))) (_root_.Int.toNat offset) base) : _root_.Int)))))))


noncomputable def «$shr_clauses» (input0 : _root_.Int) (input1 : _root_.Int) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$shr:clause:0»  input0 input1)]


noncomputable def «$shr_arith:clause:0» (input0 : _root_.Int) (input1 : _root_.Int) (input2 : _root_.Int) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let base : _root_.Int := input0; (let offset : _root_.Int := input1; (let modulus : _root_.Int := input2; (.bind (.guard ((offset ≤ (2048 : _root_.Int)))) (fun (_ : Unit) => (.pure (((_root_.Nat.repeat (fun (value : _root_.Int) => ((_root_.Int.tdiv value (2 : _root_.Int)) + modulus)) (_root_.Int.toNat offset) base) : _root_.Int))))))))


noncomputable def «$shr_arith_clauses» (input0 : _root_.Int) (input1 : _root_.Int) (input2 : _root_.Int) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$shr_arith:clause:0»  input0 input1 input2)]


noncomputable def «$bitacc:clause:0» (input0 : _root_.Int) (input1 : _root_.Int) (input2 : _root_.Int) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let base : _root_.Int := input0; (let high : _root_.Int := input1; (let low : _root_.Int := input2; (.bind (.guard (((0 : _root_.Int) ≤ low))) (fun (_ : Unit) => (.bind (.guard ((low ≤ (4611686018427387903 : _root_.Int)))) (fun (_ : Unit) => (let result : _root_.Int := («$bitacc:band» (_root_.Int.shiftRight base (_root_.Int.toNat low)) (((2 : _root_.Int) ^ (_root_.Int.toNat ((high + (1 : _root_.Int)) - low))) - (1 : _root_.Int))); (.pure ((result : _root_.Int)))))))))))


noncomputable def «$bitacc_clauses» (input0 : _root_.Int) (input1 : _root_.Int) (input2 : _root_.Int) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bitacc:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => .abort "builtin $bitacc failed"]


noncomputable def «$bitacc_replace:clause:0» (input0 : _root_.Int) (input1 : _root_.Int) (input2 : _root_.Int) (input3 : _root_.Int) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let base : _root_.Int := input0; (let high : _root_.Int := input1; (let low : _root_.Int := input2; (let replacement : _root_.Int := input3; (.bind (.guard (((0 : _root_.Int) ≤ low))) (fun (_ : Unit) => (.bind (.guard ((low ≤ (4611686018427387903 : _root_.Int)))) (fun (_ : Unit) => (let result : _root_.Int := («$bitacc_replace:bxor» («$bitacc_replace:band» base ((-(«$bitacc_replace:bxor» (((2 : _root_.Int) ^ (_root_.Int.toNat (high + (1 : _root_.Int)))) - (1 : _root_.Int)) (((2 : _root_.Int) ^ (_root_.Int.toNat low)) - (1 : _root_.Int)))) - (1 : _root_.Int))) (_root_.Int.shiftLeft replacement (_root_.Int.toNat low))); (.pure ((result : _root_.Int))))))))))))


noncomputable def «$bitacc_replace_clauses» (input0 : _root_.Int) (input1 : _root_.Int) (input2 : _root_.Int) (input3 : _root_.Int) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bitacc_replace:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => .abort "builtin $bitacc_replace failed"]


noncomputable def «$bin_eq:case_14:iter:2:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$bin_eq:case_14:iter:2:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let fieldValue_a : fieldValue := «exec:2»; (let «tail:0» : (_root_.List fieldValue) := «exec:1»; (match fieldValue_a with | .«% % ';'» «exec:3» «exec:4» => (let value_field_a : value := «exec:3»; (let nameIR_field_a : nameIR := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_14:iter:2» «tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field_a :: «tail:1»), (value_field_a :: «tail:2»)) : ((_root_.List nameIR) × (_root_.List value)))))))))))))) | [] => .unmatch)


noncomputable def «$bin_eq:case_14:iter:2_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_14:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$bin_eq:case_14:iter:2:clause:1»  input0)]


noncomputable def «$bin_eq:case_14:iter:3:clause:0» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List value))) : ((_root_.List nameIR) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$bin_eq:case_14:iter:3:clause:1» (input0 : (_root_.List fieldValue)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let fieldValue_b : fieldValue := «exec:2»; (let «tail:0» : (_root_.List fieldValue) := «exec:1»; (match fieldValue_b with | .«% % ';'» «exec:3» «exec:4» => (let value_field_b : value := «exec:3»; (let nameIR_field_b : nameIR := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«$bin_eq:case_14:iter:3» «tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List value))) => (let «tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «tail:2» : (_root_.List value) := («exec:5»).2; (.pure ((((nameIR_field_b :: «tail:1»), (value_field_b :: «tail:2»)) : ((_root_.List nameIR) × (_root_.List value)))))))))))))) | [] => .unmatch)


noncomputable def «$bin_eq:case_14:iter:3_clauses» (input0 : (_root_.List fieldValue)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_14:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$bin_eq:case_14:iter:3:clause:1»  input0)]


noncomputable def «$bin_eq:case_14:iter:8:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$bin_eq:case_14:iter:8:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field_a : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_field_b : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$bin_eq:case_14:iter:8» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List _root_.Bool)) => (let «tail:2» : (_root_.List _root_.Bool) := «exec:5»; (.pure ((((_root_.Decidable.decide (nameIR_field_a = nameIR_field_b)) :: «tail:2») : (_root_.List _root_.Bool))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$bin_eq:case_14:iter:8_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bin_eq:case_14:iter:8:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$bin_eq:case_14:iter:8:clause:1»  input0 input1)]

end SpecTec
