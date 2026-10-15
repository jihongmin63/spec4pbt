import SpecTecDecl0137

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$extend_map:case_1:iter:9:clause:1» (K : Type) (V : Type) (input0 : (_root_.List K)) (input1 : (_root_.List V)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let K_c : K := «exec:2»; (let «tail:0» : (_root_.List K) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let V_c : V := «exec:4»; (let «tail:1» : (_root_.List V) := «exec:3»; (.bind (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$extend_map:case_1:iter:9» K V «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair K V))) => (let «tail:2» : (_root_.List (pair K V)) := «exec:5»; (.pure (((((pair.«% ':' %» K_c V_c) : (pair K V)) :: «tail:2») : (_root_.List (pair K V)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$extend_map:case_1:iter:9_clauses» (K : Type) (V : Type) (input0 : (_root_.List K)) (input1 : (_root_.List V)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$extend_map:case_1:iter:9:clause:0» K V input0 input1), fun (_ : _root_.Unit) => («$extend_map:case_1:iter:9:clause:1» K V input0 input1)]


noncomputable def «$extend_map:clause:0» (K : Type) (V : Type) (input0 : (map K V)) (input1 : (map K V)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «eval:1» : (_root_.List (pair K V)) := «exec:1»; (match input1 with | .«`{ % `}» «exec:2» => (let «eval:3» : (_root_.List (pair K V)) := «exec:2»; (.bind (.call ⟨((_root_.List K) × (_root_.List V)), SpecTecCall.«$extend_map:case_1:pattern-iter:0» K V «eval:1»⟩) (fun («exec:3» : ((_root_.List K) × (_root_.List V))) => (let «K_a*» : (_root_.List K) := («exec:3»).1; (let «V_a*» : (_root_.List V) := («exec:3»).2; (.bind (.call ⟨((_root_.List K) × (_root_.List V)), SpecTecCall.«$extend_map:case_1:pattern-iter:2» K V «eval:3»⟩) (fun («exec:4» : ((_root_.List K) × (_root_.List V))) => (let «K_b*» : (_root_.List K) := («exec:4»).1; (let «V_b*» : (_root_.List V) := («exec:4»).2; (.bind (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$extend_map:case_1:iter:4» K V «K_a*» «V_a*»⟩) (fun («exec:5» : (_root_.List (pair K V))) => (let «eval:5» : (_root_.List (pair K V)) := «exec:5»; (.bind (.call ⟨(map K V), SpecTecCall.«$adds_map» K V ((set.«`{ % `}» «eval:5») : (set (pair K V))) «K_b*» «V_b*»⟩) (fun («exec:6» : (map K V)) => (let «eval:6» : (map K V) := «exec:6»; (match «eval:6» with | .«`{ % `}» «exec:7» => (let «eval:8» : (_root_.List (pair K V)) := «exec:7»; (.bind (.call ⟨((_root_.List K) × (_root_.List V)), SpecTecCall.«$extend_map:case_1:pattern-iter:7» K V «eval:8»⟩) (fun («exec:8» : ((_root_.List K) × (_root_.List V))) => (let «K_c*» : (_root_.List K) := («exec:8»).1; (let «V_c*» : (_root_.List V) := («exec:8»).2; (.bind (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$extend_map:case_1:iter:9» K V «K_c*» «V_c*»⟩) (fun («exec:9» : (_root_.List (pair K V))) => (let «eval:10» : (_root_.List (pair K V)) := «exec:9»; (.pure ((((set.«`{ % `}» «eval:10») : (set (pair K V))) : (map K V)))))))))))))))))))))))))))))))


noncomputable def «$extend_map_clauses» (K : Type) (V : Type) (input0 : (map K V)) (input1 : (map K V)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$extend_map:clause:0» K V input0 input1)]


noncomputable def «$print_:clause:0» (X : Type) [_root_.SpecTecPrint X] (input0 : X) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : X := input0; (match (_root_.SpecTecPrint.print? value) with | some «exec:1» => (let result : _root_.String := «exec:1»; (.pure ((result : _root_.String)))) | none => .unmatch))


noncomputable def «$print__clauses» (X : Type) [_root_.SpecTecPrint X] (input0 : X) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$print_:clause:0» X input0), fun (_ : _root_.Unit) => .abort "builtin $print_ failed"]


noncomputable def «$modulo:clause:0» (input0 : _root_.Nat) (input1 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n_a : _root_.Nat := input0; (let n_b : _root_.Nat := input1; (.bind (.guard ((n_b ≠ (0 : _root_.Nat)))) (fun (_ : Unit) => (.bind (SpecTecExecution.require ((n_b ≠ (0 : _root_.Nat))) "division by zero") (fun (_ : Unit) => (.pure (((_root_.Option.some (n_a % n_b)) : (_root_.Option _root_.Nat))))))))))


noncomputable def «$modulo:clause:1» (input0 : _root_.Nat) (input1 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n_a : _root_.Nat := input0; (let n_b : _root_.Nat := input1; (.bind (.guard ((0 : _root_.Nat) = n_b)) (fun (_ : Unit) => (.pure ((((_root_.Option.none) : (_root_.Option _root_.Nat)) : (_root_.Option _root_.Nat))))))))


noncomputable def «$modulo_clauses» (input0 : _root_.Nat) (input1 : _root_.Nat) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$modulo:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$modulo:clause:1»  input0 input1)]


noncomputable def «$modulo_42:clause:0» (input0 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n : _root_.Nat := input0; (.bind (.call ⟨(_root_.Option _root_.Nat), SpecTecCall.«$modulo» n (42 : _root_.Nat)⟩) (fun («exec:1» : (_root_.Option _root_.Nat)) => (let «eval:0» : (_root_.Option _root_.Nat) := «exec:1»; (let nat? : (_root_.Option _root_.Nat) := «eval:0»; (.bind (.guard (((_root_.Option.isSome nat?) = true))) (fun (_ : Unit) => (match nat? with | some «exec:2» => (let n_result : _root_.Nat := «exec:2»; (.pure ((n_result : _root_.Nat)))) | none => .unmatch))))))))


noncomputable def «$modulo_42_clauses» (input0 : _root_.Nat) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$modulo_42:clause:0»  input0)]


noncomputable def «$name:clause:0» (input0 : SpecTec.name) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let name : SpecTec.name := input0; (.bind (.call ⟨_root_.String, SpecTecCall.«$print_» SpecTec.name name⟩) (fun («exec:1» : _root_.String) => (let «eval:0» : _root_.String := «exec:1»; (.pure ((«eval:0» : nameIR)))))))


noncomputable def «$name_clauses» (input0 : name) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$name:clause:0»  input0)]


noncomputable def «$tableCustomName:clause:0» (input0 : SpecTec.tableCustomName) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableCustomName : SpecTec.tableCustomName := input0; (.bind (.call ⟨_root_.String, SpecTecCall.«$print_» SpecTec.tableCustomName tableCustomName⟩) (fun («exec:1» : _root_.String) => (let «eval:0» : _root_.String := «exec:1»; (.pure ((«eval:0» : nameIR)))))))


noncomputable def «$tableCustomName_clauses» (input0 : tableCustomName) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableCustomName:clause:0»  input0)]


noncomputable def «$fresh_typeIds:clause:0» (input0 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nat : _root_.Nat := input0; (.bind (.guard ((0 : _root_.Nat) = nat)) (fun (_ : Unit) => (.pure ((([] : (_root_.List typeId)) : (_root_.List typeId)))))))


noncomputable def «$fresh_typeIds:clause:1» (input0 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let n : _root_.Nat := input0; (.bind (.guard ((n ≠ (0 : _root_.Nat)))) (fun (_ : Unit) => (let i : _root_.Int := ((_root_.Int.ofNat n) - (_root_.Int.ofNat (1 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let n' : _root_.Nat := (_root_.Int.toNat i); (.bind (.call ⟨typeId, SpecTecCall.«$fresh_typeId»⟩) (fun («exec:1» : typeId) => (let «eval:0» : typeId := «exec:1»; (.bind (.call ⟨(_root_.List typeId), SpecTecCall.«$fresh_typeIds» n'⟩) (fun («exec:2» : (_root_.List typeId)) => (let «eval:1» : (_root_.List typeId) := «exec:2»; (.pure (((«eval:0» :: «eval:1») : (_root_.List typeId)))))))))))))))))))


noncomputable def «$fresh_typeIds_clauses» (input0 : _root_.Nat) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$fresh_typeIds:clause:0»  input0), fun (_ : _root_.Unit) => («$fresh_typeIds:clause:1»  input0)]


noncomputable def «$objectId_ends_with:clause:0» (input0 : SpecTec.objectId) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectId : SpecTec.objectId := input0; (let nameIR : SpecTec.nameIR := input1; (let «nameIR''*» : (_root_.List SpecTec.nameIR) := («$rev_» (X := id) objectId); (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «nameIR''*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «nameIR''*» with | «exec:2» :: «exec:1» => (let nameIR' : SpecTec.nameIR := «exec:2»; (let «_nameIR*» : (_root_.List SpecTec.nameIR) := «exec:1»; (.bind (.guard (nameIR = nameIR')) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))) | [] => .unmatch))))))


noncomputable def «$objectId_ends_with:clause:1» (input0 : SpecTec.objectId) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectId : SpecTec.objectId := input0; (let nameIR : SpecTec.nameIR := input1; (.pure ((false : _root_.Bool)))))


noncomputable def «$objectId_ends_with_clauses» (input0 : objectId) (input1 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$objectId_ends_with:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$objectId_ends_with:clause:1»  input0 input1)]


noncomputable def «$bitstr_to_int:clause:0» (input0 : _root_.Int) (input1 : _root_.Int) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let width : _root_.Int := input0; (let value : _root_.Int := input1; (.bind (.guard ((width ≤ (0 : _root_.Int)))) (fun (_ : Unit) => (.pure (((0 : _root_.Int) : _root_.Int)))))))


noncomputable def «$bitstr_to_int:clause:1» (input0 : _root_.Int) (input1 : _root_.Int) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let width : _root_.Int := input0; (let value : _root_.Int := input1; (.bind (.guard (((0 : _root_.Int) < width))) (fun (_ : Unit) => (.bind (.guard ((width ≤ (2048 : _root_.Int)))) (fun (_ : Unit) => (.pure ((((_root_.Int.emod (value + (_root_.Int.tdiv ((2 : _root_.Int) ^ (_root_.Int.toNat width)) (2 : _root_.Int))) ((2 : _root_.Int) ^ (_root_.Int.toNat width))) - (_root_.Int.tdiv ((2 : _root_.Int) ^ (_root_.Int.toNat width)) (2 : _root_.Int))) : _root_.Int)))))))))


noncomputable def «$bitstr_to_int_clauses» (input0 : _root_.Int) (input1 : _root_.Int) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bitstr_to_int:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$bitstr_to_int:clause:1»  input0 input1)]


noncomputable def «$int_to_bitstr:clause:0» (input0 : _root_.Int) (input1 : _root_.Int) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let width : _root_.Int := input0; (let value : _root_.Int := input1; (.bind (.guard ((width ≤ (2048 : _root_.Int)))) (fun (_ : Unit) => (.pure (((_root_.Int.emod value ((2 : _root_.Int) ^ (_root_.Int.toNat width))) : _root_.Int)))))))


noncomputable def «$int_to_bitstr_clauses» (input0 : _root_.Int) (input1 : _root_.Int) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$int_to_bitstr:clause:0»  input0 input1)]


noncomputable def «$bits_to_int_signed:clause:0» (input0 : bits) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let sign : _root_.Bool := «exec:2»; (let tail : (_root_.List _root_.Bool) := «exec:1»; (let result : _root_.Int := («$bits_to_int_signed:convert» (sign :: tail)); (.pure ((result : _root_.Int)))))) | [] => .unmatch)


noncomputable def «$bits_to_int_signed_clauses» (input0 : bits) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bits_to_int_signed:clause:0»  input0)]


noncomputable def «$int_to_bits_unsigned:clause:0» (input0 : _root_.Nat) (input1 : _root_.Int) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let width : _root_.Nat := input0; (let value : _root_.Int := input1; (.bind (.guard ((width ≤ (2048 : _root_.Nat)))) (fun (_ : Unit) => (let result : bits := (_root_.List.map (fun (index : _root_.Nat) => (_root_.Decidable.decide ((_root_.Int.emod (_root_.Int.shiftRight value index) (2 : _root_.Int)) = (1 : _root_.Int)))) (_root_.List.reverse (_root_.List.range width))); (.pure ((result : bits))))))))


noncomputable def «$int_to_bits_unsigned_clauses» (input0 : _root_.Nat) (input1 : _root_.Int) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$int_to_bits_unsigned:clause:0»  input0 input1)]


noncomputable def «$int_to_bits_signed:clause:0» (input0 : _root_.Nat) (input1 : _root_.Int) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let width : _root_.Nat := input0; (let value : _root_.Int := input1; (.bind (.guard ((width ≤ (2048 : _root_.Nat)))) (fun (_ : Unit) => (let result : bits := (_root_.List.map (fun (index : _root_.Nat) => (_root_.Decidable.decide ((_root_.Int.emod (_root_.Int.shiftRight value index) (2 : _root_.Int)) = (1 : _root_.Int)))) (_root_.List.reverse (_root_.List.range width))); (.pure ((result : bits))))))))


noncomputable def «$int_to_bits_signed_clauses» (input0 : _root_.Nat) (input1 : _root_.Int) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$int_to_bits_signed:clause:0»  input0 input1)]

end SpecTec
