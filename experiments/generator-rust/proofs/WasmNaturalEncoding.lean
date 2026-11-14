import WasmNatural

set_option autoImplicit false

namespace RustWasm
open Aeneas.Std generator_rust wasm.natural

theorem positiveValue_injective : Function.Injective positiveValue := by
  intro first
  induction first with
  | One =>
      intro second equal
      cases second with
      | One => rfl
      | Bit0 tail =>
          have := positiveValue_pos tail
          simp only [positiveValue] at equal
          omega
      | Bit1 tail =>
          have := positiveValue_pos tail
          simp only [positiveValue] at equal
          omega
  | Bit0 first ih =>
      intro second equal
      cases second with
      | One =>
          have := positiveValue_pos first
          simp only [positiveValue] at equal
          omega
      | Bit0 second =>
          congr 1
          apply ih
          simp only [positiveValue] at equal
          omega
      | Bit1 second => simp only [positiveValue] at equal; omega
  | Bit1 first ih =>
      intro second equal
      cases second with
      | One =>
          have := positiveValue_pos first
          simp only [positiveValue] at equal
          omega
      | Bit0 second => simp only [positiveValue] at equal; omega
      | Bit1 second =>
          congr 1
          apply ih
          simp only [positiveValue] at equal
          omega

theorem naturalValue_injective : Function.Injective naturalValue := by
  intro first second equal
  cases first with
  | Zero =>
      cases second with
      | Zero => rfl
      | Positive second =>
          have := positiveValue_pos second
          simp only [naturalValue] at equal
          omega
  | Positive first =>
      cases second with
      | Zero =>
          have := positiveValue_pos first
          simp only [naturalValue] at equal
          omega
      | Positive second => exact congrArg Natural.Positive (positiveValue_injective equal)

theorem positiveLiteral_value (value : Nat) (positive : 0 < value) :
    positiveValue (positiveLiteral value) = value := by
  revert positive
  induction value using Nat.strong_induction_on with
  | h value ih =>
      intro positive
      rw [positiveLiteral]
      split
      · have equal : value = 1 := by omega
        subst value
        rfl
      · have smaller : value / 2 < value := Nat.div_lt_self (by omega) (by decide)
        have nonzero : 0 < value / 2 := Nat.div_pos (by omega) (by decide)
        have tail := ih (value / 2) smaller nonzero
        split <;> simp only [positiveValue, tail] <;> omega

@[simp] theorem naturalLiteral_value (value : Nat) :
    naturalValue (naturalLiteral value) = value := by
  unfold naturalLiteral
  split
  · subst value; rfl
  · exact positiveLiteral_value value (by omega)

/-- Binary numeral inputs execute the actual translated increment and decrement. -/
theorem increment_literal (value : Nat) :
    wasm.natural.increment (naturalLiteral value) = Result.ok (naturalLiteral (value + 1)) := by
  obtain ⟨next, run, equation⟩ := increment_total (naturalLiteral value)
  have equal : next = naturalLiteral (value + 1) := by
    apply naturalValue_injective
    simpa using equation
  simpa [equal] using run

theorem decrement_literal (value : Nat) :
    wasm.natural.decrement (naturalLiteral (value + 1)) = Result.ok (some (naturalLiteral value)) := by
  obtain ⟨previous, run, equation⟩ := decrement_total (naturalLiteral (value + 1)) (by simp)
  have equal : previous = naturalLiteral value := by
    apply naturalValue_injective
    simp only [naturalLiteral_value] at equation ⊢
    omega
  simpa [equal] using run

@[simp] theorem decrement_zero : wasm.natural.decrement (naturalLiteral 0) = Result.ok none := by
  simp [naturalLiteral, wasm.natural.decrement]

end RustWasm
