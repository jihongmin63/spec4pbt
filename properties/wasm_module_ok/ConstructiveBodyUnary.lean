import properties.wasm_module_ok.ConstructiveBodyScalarSizes
import properties.wasm_module_ok.ConstructiveBodyOperatorProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyUnary
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore
open ConstructiveBodyOperatorTypes ConstructiveBodyScalarSizes ConstructiveBodyOperatorProductions ConstructiveBodyEnvironment ConstructiveBodyProductions

def unaryExtends : unop_ → Bool
  | .I32 (.ExtendS _) | .I64 (.ExtendS _) => true
  | _ => false

theorem extends_call (op : unop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$check_uop_extends» op⟩) n (.success (.of (unaryExtends op))) n := by
  cases op with
  | I32 u =>
    cases u with
    | Clz =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$check_uop_extends_clauses» (.I32 (.Clz))) ())
        n (.success (.of false)) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«$check_uop_extends:clause:2»
      exact SpecTecExecution.Eval.pure _
    | Ctz =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$check_uop_extends_clauses» (.I32 (.Ctz))) ())
        n (.success (.of false)) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«$check_uop_extends:clause:2»
      exact SpecTecExecution.Eval.pure _
    | Popcnt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$check_uop_extends_clauses» (.I32 (.Popcnt))) ())
        n (.success (.of false)) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«$check_uop_extends:clause:2»
      exact SpecTecExecution.Eval.pure _
    | ExtendS pt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$check_uop_extends_clauses» (.I32 (.ExtendS pt))) ())
        n (.success (.of true)) n
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«$check_uop_extends:clause:0»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.pure _
  | I64 u =>
    cases u with
    | Clz =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$check_uop_extends_clauses» (.I64 (.Clz))) ())
        n (.success (.of false)) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«$check_uop_extends:clause:2»
      exact SpecTecExecution.Eval.pure _
    | Ctz =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$check_uop_extends_clauses» (.I64 (.Ctz))) ())
        n (.success (.of false)) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«$check_uop_extends:clause:2»
      exact SpecTecExecution.Eval.pure _
    | Popcnt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$check_uop_extends_clauses» (.I64 (.Popcnt))) ())
        n (.success (.of false)) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«$check_uop_extends:clause:2»
      exact SpecTecExecution.Eval.pure _
    | ExtendS pt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$check_uop_extends_clauses» (.I64 (.ExtendS pt))) ())
        n (.success (.of true)) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_uop_extends:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«$check_uop_extends:clause:1»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.pure _
  | F32 u =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$check_uop_extends_clauses» (.F32 u)) ())
      n (.success (.of false)) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · unfold SpecTec.«$check_uop_extends:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · unfold SpecTec.«$check_uop_extends:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
    apply SpecTecExecution.firstSuccess_cons_success
    unfold SpecTec.«$check_uop_extends:clause:2»
    exact SpecTecExecution.Eval.pure _
  | F64 u =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$check_uop_extends_clauses» (.F64 u)) ())
      n (.success (.of false)) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · unfold SpecTec.«$check_uop_extends:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · unfold SpecTec.«$check_uop_extends:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
    apply SpecTecExecution.firstSuccess_cons_success
    unfold SpecTec.«$check_uop_extends:clause:2»
    exact SpecTecExecution.Eval.pure _

def legal : unop_ → Bool
  | .I32 (.ExtendS .I8) | .I32 (.ExtendS .I16) => true
  | .I64 (.ExtendS .I8) | .I64 (.ExtendS .I16) | .I64 (.ExtendS .I32) => true
  | .I32 (.ExtendS _) | .I64 (.ExtendS _) => false
  | _ => true

theorem unop_outcome (op : unop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Unop_ok op⟩)
      n (if legal op then .success (.of ()) else .unmatch) n := by
  cases op with
  | I32 u =>
    cases u with
    | Clz =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I32 .Clz)) ()) n (.success (.of ())) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«Unop_ok:clause:2»
      apply SpecTecExecution.Eval.bind_success (extends_call (.I32 .Clz) n)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp [unaryExtends])) (SpecTecExecution.Eval.pure _)
    | Ctz =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I32 .Ctz)) ()) n (.success (.of ())) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«Unop_ok:clause:2»
      apply SpecTecExecution.Eval.bind_success (extends_call (.I32 .Ctz) n)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp [unaryExtends])) (SpecTecExecution.Eval.pure _)
    | Popcnt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I32 .Popcnt)) ()) n (.success (.of ())) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«Unop_ok:clause:2»
      apply SpecTecExecution.Eval.bind_success (extends_call (.I32 .Popcnt) n)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp [unaryExtends])) (SpecTecExecution.Eval.pure _)
    | ExtendS pt =>
      cases pt with
      | I8 =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I32 (.ExtendS .I8))) ()) n (.success (.of ())) n
        apply SpecTecExecution.firstSuccess_cons_success
        unfold SpecTec.«Unop_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        apply SpecTecExecution.Eval.bind_success (numeric_type_call (.I32 (.ExtendS .I8) : unop_) n)
        apply SpecTecExecution.Eval.bind_success (num_size .I32T n)
        apply SpecTecExecution.Eval.bind_success (pack_ok 4 .I8 n (by decide))
        exact SpecTecExecution.Eval.pure _
      | I16 =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I32 (.ExtendS .I16))) ()) n (.success (.of ())) n
        apply SpecTecExecution.firstSuccess_cons_success
        unfold SpecTec.«Unop_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        apply SpecTecExecution.Eval.bind_success (numeric_type_call (.I32 (.ExtendS .I16) : unop_) n)
        apply SpecTecExecution.Eval.bind_success (num_size .I32T n)
        apply SpecTecExecution.Eval.bind_success (pack_ok 4 .I16 n (by decide))
        exact SpecTecExecution.Eval.pure _
      | I32 =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I32 (.ExtendS .I32))) ()) n (.unmatch) n
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:0»
          apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
          apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
          apply SpecTecExecution.Eval.bind_success (numeric_type_call (.I32 (.ExtendS .I32) : unop_) n)
          apply SpecTecExecution.Eval.bind_success (num_size .I32T n)
          exact SpecTecExecution.Eval.bind_unmatch (pack_bad 4 .I32 n (by decide))
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:1»
          exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:2»
          apply SpecTecExecution.Eval.bind_success (extends_call (.I32 (.ExtendS .I32)) n)
          exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [unaryExtends]))
        exact SpecTecExecution.Eval.unmatch
      | I64 =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I32 (.ExtendS .I64))) ()) n (.unmatch) n
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:0»
          apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
          apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
          apply SpecTecExecution.Eval.bind_success (numeric_type_call (.I32 (.ExtendS .I64) : unop_) n)
          apply SpecTecExecution.Eval.bind_success (num_size .I32T n)
          exact SpecTecExecution.Eval.bind_unmatch (pack_bad 4 .I64 n (by decide))
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:1»
          exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:2»
          apply SpecTecExecution.Eval.bind_success (extends_call (.I32 (.ExtendS .I64)) n)
          exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [unaryExtends]))
        exact SpecTecExecution.Eval.unmatch
  | I64 u =>
    cases u with
    | Clz =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I64 .Clz)) ()) n (.success (.of ())) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«Unop_ok:clause:2»
      apply SpecTecExecution.Eval.bind_success (extends_call (.I64 .Clz) n)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp [unaryExtends])) (SpecTecExecution.Eval.pure _)
    | Ctz =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I64 .Ctz)) ()) n (.success (.of ())) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«Unop_ok:clause:2»
      apply SpecTecExecution.Eval.bind_success (extends_call (.I64 .Ctz) n)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp [unaryExtends])) (SpecTecExecution.Eval.pure _)
    | Popcnt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I64 .Popcnt)) ()) n (.success (.of ())) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«Unop_ok:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:iunop:ExtendS»]))
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«Unop_ok:clause:2»
      apply SpecTecExecution.Eval.bind_success (extends_call (.I64 .Popcnt) n)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp [unaryExtends])) (SpecTecExecution.Eval.pure _)
    | ExtendS pt =>
      cases pt with
      | I8 =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I64 (.ExtendS .I8))) ()) n (.success (.of ())) n
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:0»
          exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
        apply SpecTecExecution.firstSuccess_cons_success
        unfold SpecTec.«Unop_ok:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        apply SpecTecExecution.Eval.bind_success (numeric_type_call (.I64 (.ExtendS .I8) : unop_) n)
        apply SpecTecExecution.Eval.bind_success (num_size .I64T n)
        apply SpecTecExecution.Eval.bind_success (pack_ok 8 .I8 n (by decide))
        exact SpecTecExecution.Eval.pure _
      | I16 =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I64 (.ExtendS .I16))) ()) n (.success (.of ())) n
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:0»
          exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
        apply SpecTecExecution.firstSuccess_cons_success
        unfold SpecTec.«Unop_ok:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        apply SpecTecExecution.Eval.bind_success (numeric_type_call (.I64 (.ExtendS .I16) : unop_) n)
        apply SpecTecExecution.Eval.bind_success (num_size .I64T n)
        apply SpecTecExecution.Eval.bind_success (pack_ok 8 .I16 n (by decide))
        exact SpecTecExecution.Eval.pure _
      | I32 =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I64 (.ExtendS .I32))) ()) n (.success (.of ())) n
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:0»
          exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
        apply SpecTecExecution.firstSuccess_cons_success
        unfold SpecTec.«Unop_ok:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        apply SpecTecExecution.Eval.bind_success (numeric_type_call (.I64 (.ExtendS .I32) : unop_) n)
        apply SpecTecExecution.Eval.bind_success (num_size .I64T n)
        apply SpecTecExecution.Eval.bind_success (pack_ok 8 .I32 n (by decide))
        exact SpecTecExecution.Eval.pure _
      | I64 =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.I64 (.ExtendS .I64))) ()) n (.unmatch) n
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:0»
          exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:1»
          apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
          apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
          apply SpecTecExecution.Eval.bind_success (numeric_type_call (.I64 (.ExtendS .I64) : unop_) n)
          apply SpecTecExecution.Eval.bind_success (num_size .I64T n)
          exact SpecTecExecution.Eval.bind_unmatch (pack_bad 8 .I64 n (by decide))
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · unfold SpecTec.«Unop_ok:clause:2»
          apply SpecTecExecution.Eval.bind_success (extends_call (.I64 (.ExtendS .I64)) n)
          exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [unaryExtends]))
        exact SpecTecExecution.Eval.unmatch
  | F32 u =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.F32 u)) ()) n (.success (.of ())) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · unfold SpecTec.«Unop_ok:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · unfold SpecTec.«Unop_ok:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
    apply SpecTecExecution.firstSuccess_cons_success
    unfold SpecTec.«Unop_ok:clause:2»
    apply SpecTecExecution.Eval.bind_success (extends_call (.F32 u) n)
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp [unaryExtends])) (SpecTecExecution.Eval.pure _)
  | F64 u =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses (.F64 u)) ()) n (.success (.of ())) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · unfold SpecTec.«Unop_ok:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I32»]))
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · unfold SpecTec.«Unop_ok:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:op:I64»]))
    apply SpecTecExecution.firstSuccess_cons_success
    unfold SpecTec.«Unop_ok:clause:2»
    apply SpecTecExecution.Eval.bind_success (extends_call (.F64 u) n)
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp [unaryExtends])) (SpecTecExecution.Eval.pure _)

theorem unop_exact (op : unop_) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Unop_ok op⟩) n (.success (.of ())) finish ↔ legal op=true ∧ finish=n := by
  constructor
  · intro h
    obtain ⟨he,hn⟩ := SpecTecExecution.eval_deterministic (by intro request a b h; cases h) h (unop_outcome op n)
    cases hl : legal op <;> simp [hl] at he
    exact ⟨rfl,hn⟩
  · rintro ⟨hl,hn⟩
    subst finish
    simpa [hl] using unop_outcome op n

#print axioms unop_outcome
end properties.wasm_module_ok.ConstructiveBodyUnary
