import WasmNaturalEncoding

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.natural

/-- The optional word conversion is exact, including its overflow result. -/
def wordEncoding (value : Nat) : Option U64 :=
  if bounded : value < 18446744073709551616 then
    some (UScalar.ofNatCore (ty := .U64) value bounded)
  else none

private theorem max_word_half : core.num.U64.MAX / 2#u64 = Result.ok 9223372036854775807#u64 := by
  apply wp_eq_ok
  step* <;> simp_all [U64.rMax, UScalar.eq_equiv] <;> scalar_tac

theorem positive_to_word (value : Positive) :
    wasm.natural.positive_to_u64 value = Result.ok (wordEncoding (positiveValue value)) := by
  induction value with
  | One => simp [wasm.natural.positive_to_u64, positiveValue, wordEncoding]
  | Bit0 tail ih =>
      rw [wasm.natural.positive_to_u64, ih]
      by_cases bounded : positiveValue tail < 18446744073709551616
      · simp only [wordEncoding, dif_pos bounded, bind_tc_ok, max_word_half]
        by_cases half : positiveValue tail > 9223372036854775807
        · have overflow : ¬ 2 * positiveValue tail < 18446744073709551616 := by omega
          simp [positiveValue, overflow, half]
        · have fits : 2 * positiveValue tail < 18446744073709551616 := by omega
          simp only [positiveValue, dif_pos fits]
          apply wp_eq_ok
          step* <;> simp_all [UScalar.eq_equiv] <;> scalar_tac
      · have overflow : ¬ 2 * positiveValue tail < 18446744073709551616 := by omega
        simp [wordEncoding, bounded, positiveValue, overflow]
  | Bit1 tail ih =>
      rw [wasm.natural.positive_to_u64, ih]
      by_cases bounded : positiveValue tail < 18446744073709551616
      · simp only [wordEncoding, dif_pos bounded, bind_tc_ok, max_word_half]
        by_cases half : positiveValue tail > 9223372036854775807
        · have overflow : ¬ 2 * positiveValue tail + 1 < 18446744073709551616 := by omega
          simp [positiveValue, overflow, half]
        · have fits : 2 * positiveValue tail + 1 < 18446744073709551616 := by omega
          simp only [positiveValue, dif_pos fits]
          apply wp_eq_ok
          step* <;> simp_all [UScalar.eq_equiv] <;> scalar_tac
      · have overflow : ¬ 2 * positiveValue tail + 1 < 18446744073709551616 := by omega
        simp [wordEncoding, bounded, positiveValue, overflow]

theorem natural_to_word (value : Natural) :
    wasm.natural.to_u64 value = Result.ok (wordEncoding (naturalValue value)) := by
  cases value with
  | Zero => simp [wasm.natural.to_u64, naturalValue, wordEncoding]
  | Positive value => exact positive_to_word value

theorem literal_to_word (value : Nat) :
    wasm.natural.to_u64 (naturalLiteral value) = Result.ok (wordEncoding value) := by
  simpa using natural_to_word (naturalLiteral value)

private theorem positive_from_word (value : U64) (positive : 0 < value.val) :
    wasm.natural.positive_from_u64 value = Result.ok (positiveLiteral value.val) := by
  generalize size : value.val = n
  induction n using Nat.strong_induction_on generalizing value with
  | h n ih =>
      rw [← size]
      rw [wasm.natural.positive_from_u64]
      by_cases small : value.val ≤ 1
      · have scalarSmall : value ≤ 1#u64 := by scalar_tac
        rw [positiveLiteral]
        simp only [scalarSmall, small, ↓reduceIte]
      · have scalarLarge : ¬ value ≤ 1#u64 := by scalar_tac
        simp only [scalarLarge, ↓reduceIte]
        obtain ⟨quotient, divide, quotientValue⟩ := UScalar.div_spec value (y := 2#u64) (by decide)
        simp only [UScalar.ofNatCore_val_eq] at quotientValue
        have smaller : quotient.val < n := by
          rw [quotientValue, ← size]
          exact Nat.div_lt_self positive (by decide)
        have quotientPositive : 0 < quotient.val := by omega
        have recurse := ih quotient.val smaller quotient quotientPositive rfl
        rw [divide]
        simp only [bind_ok, bind_tc_ok]
        rw [recurse]
        simp only [bind_ok, bind_tc_ok]
        have expression : positiveLiteral value.val =
            if value.val % 2 = 0 then .Bit0 (positiveLiteral quotient.val)
            else .Bit1 (positiveLiteral quotient.val) := by
          rw [positiveLiteral]
          simp [small, quotientValue]
        rw [expression]
        apply wp_eq_ok
        step* <;> simp_all [UScalar.eq_equiv]

theorem natural_from_word (value : U64) :
    wasm.natural.from_u64 value = Result.ok (naturalLiteral value.val) := by
  rw [wasm.natural.from_u64]
  by_cases zero : value.val = 0
  · have scalarZero : value = 0#u64 := by scalar_tac
    simp [scalarZero, naturalLiteral]
  · have scalarNonzero : value ≠ 0#u64 := by scalar_tac
    simp [scalarNonzero, positive_from_word value (by omega), naturalLiteral, zero]

#print axioms positive_to_word
#print axioms natural_to_word
#print axioms literal_to_word
#print axioms natural_from_word

end RustWasm
