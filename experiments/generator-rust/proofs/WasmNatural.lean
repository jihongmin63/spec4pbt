import GeneratorRust

set_option autoImplicit false

namespace RustWasm
open Aeneas Aeneas.Std generator_rust
open wasm.natural

def positiveValue : Positive → Nat
  | .One => 1
  | .Bit0 tail => 2 * positiveValue tail
  | .Bit1 tail => 2 * positiveValue tail + 1

def naturalValue : Natural → Nat
  | .Zero => 0
  | .Positive value => positiveValue value

theorem positiveValue_pos (value : Positive) : 0 < positiveValue value := by
  induction value <;> simp_all [positiveValue]

@[simp] theorem copy_positive_eq (value : Positive) :
    wasm.natural.copy_positive value = Result.ok value := by
  induction value with
  | One => rw [wasm.natural.copy_positive]
  | Bit0 tail ih => rw [wasm.natural.copy_positive]; simp [ih]
  | Bit1 tail ih => rw [wasm.natural.copy_positive]; simp [ih]

@[simp] theorem copy_natural_eq (value : Natural) :
    wasm.natural.copy value = Result.ok value := by
  cases value <;> simp [wasm.natural.copy]

theorem increment_positive_total (value : Positive) :
    ∃ next, wasm.natural.increment_positive value = Result.ok next ∧
      positiveValue next = positiveValue value + 1 := by
  induction value with
  | One => exact ⟨.Bit0 .One, by rw [wasm.natural.increment_positive], rfl⟩
  | Bit0 tail => exact ⟨.Bit1 tail, by rw [wasm.natural.increment_positive], rfl⟩
  | Bit1 tail ih =>
      obtain ⟨next, run, value⟩ := ih
      refine ⟨.Bit0 next, ?_, ?_⟩
      · rw [wasm.natural.increment_positive]; simp [run]
      · simp only [positiveValue]; omega

/-- Every binary cursor advances successfully, including values above any machine word. -/
theorem increment_total (value : Natural) :
    ∃ next, wasm.natural.increment value = Result.ok next ∧
      naturalValue next = naturalValue value + 1 := by
  cases value with
  | Zero => exact ⟨.Positive .One, rfl, rfl⟩
  | Positive value =>
      obtain ⟨next, run, equation⟩ := increment_positive_total value
      exact ⟨.Positive next, by simp [wasm.natural.increment, run], equation⟩

theorem predecessor_total (value : Positive) :
    ∃ previous, wasm.natural.predecessor value = Result.ok previous ∧
      naturalValue previous + 1 = positiveValue value := by
  induction value with
  | One => exact ⟨.Zero, by rw [wasm.natural.predecessor], rfl⟩
  | Bit0 tail ih =>
      obtain ⟨previous, run, equation⟩ := ih
      cases previous with
      | Zero =>
          refine ⟨.Positive .One, ?_, ?_⟩
          · rw [wasm.natural.predecessor]; simp [run]
          · simp only [naturalValue, positiveValue] at *; omega
      | Positive previous =>
          refine ⟨.Positive (.Bit1 previous), ?_, ?_⟩
          · rw [wasm.natural.predecessor]; simp [run]
          · simp only [naturalValue, positiveValue] at *; omega
  | Bit1 tail =>
      exact ⟨.Positive (.Bit0 tail), by rw [wasm.natural.predecessor], rfl⟩

/-- Successful budget subtraction is exact; zero fails in the actual translated code. -/
theorem decrement_total (value : Natural) (positive : 0 < naturalValue value) :
    ∃ previous, wasm.natural.decrement value = Result.ok (some previous) ∧
      naturalValue previous + 1 = naturalValue value := by
  cases value with
  | Zero => simp [naturalValue] at positive
  | Positive value =>
      obtain ⟨previous, run, equation⟩ := predecessor_total value
      exact ⟨previous, by simp [wasm.natural.decrement, run], equation⟩

/-- Representation coverage has no u64/usize premise and uses actual increment execution. -/
theorem natural_representable (value : Nat) : ∃ encoded, naturalValue encoded = value := by
  induction value with
  | zero => exact ⟨.Zero, rfl⟩
  | succ value ih =>
      obtain ⟨encoded, equation⟩ := ih
      obtain ⟨next, _, nextValue⟩ := increment_total encoded
      exact ⟨next, by omega⟩

/-- Constructor-only encoding used for explicit finite replay witnesses. -/
def positiveLiteral (value : Nat) : Positive :=
  if value ≤ 1 then .One else
    let tail := positiveLiteral (value / 2)
    if value % 2 = 0 then .Bit0 tail else .Bit1 tail
termination_by value

def naturalLiteral (value : Nat) : Natural :=
  if value = 0 then .Zero else .Positive (positiveLiteral value)

theorem wp_eq_ok {α : Type} (computation : Result α) (value : α)
    (h : computation ⦃ result => result = value ⦄) : computation = Result.ok value := by
  cases computation using Result.cases <;> simp_all

end RustWasm
