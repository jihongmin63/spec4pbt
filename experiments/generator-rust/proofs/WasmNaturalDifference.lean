import WasmNaturalEncoding

set_option autoImplicit false

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.natural

theorem double_total (value : Natural) :
    ∃ output, wasm.natural.double value = Result.ok output ∧
      naturalValue output = 2 * naturalValue value := by
  cases value with
  | Zero => exact ⟨.Zero, rfl, rfl⟩
  | Positive value => exact ⟨.Positive (.Bit0 value), rfl, rfl⟩

theorem double_plus_one_total (value : Natural) :
    ∃ output, wasm.natural.double_plus_one value = Result.ok output ∧
      naturalValue output = 2 * naturalValue value + 1 := by
  cases value with
  | Zero => exact ⟨.Positive .One, rfl, rfl⟩
  | Positive value => exact ⟨.Positive (.Bit1 value), rfl, rfl⟩

theorem positive_difference_total (left right : Positive) :
    ∃ output, wasm.natural.positive_difference left right = Result.ok output ∧
      match output with
      | none => positiveValue left < positiveValue right
      | some value => naturalValue value + positiveValue right = positiveValue left := by
  induction left generalizing right with
  | One =>
      cases right with
      | One => exact ⟨some .Zero, by rw [wasm.natural.positive_difference], rfl⟩
      | Bit0 right =>
          refine ⟨none, by rw [wasm.natural.positive_difference], ?_⟩
          have := positiveValue_pos right
          simp only [positiveValue]
          omega
      | Bit1 right =>
          refine ⟨none, by rw [wasm.natural.positive_difference], ?_⟩
          have := positiveValue_pos right
          simp only [positiveValue]
          omega
  | Bit0 left ih =>
      cases right with
      | One =>
          obtain ⟨previous, run, equation⟩ := predecessor_total (.Bit0 left)
          refine ⟨some previous, ?_, equation⟩
          rw [wasm.natural.positive_difference]
          simp [run]
      | Bit0 right =>
          obtain ⟨output, run, equation⟩ := ih right
          cases output with
          | none =>
              refine ⟨none, ?_, ?_⟩
              · rw [wasm.natural.positive_difference]; simp [run]
              · simp only [positiveValue]; omega
          | some value =>
              obtain ⟨doubled, doubleRun, doubleValue⟩ := double_total value
              refine ⟨some doubled, ?_, ?_⟩
              · rw [wasm.natural.positive_difference]; simp [run, doubleRun]
              · simp only [positiveValue]; omega
      | Bit1 right =>
          obtain ⟨output, run, equation⟩ := ih right
          cases output with
          | none =>
              refine ⟨none, ?_, ?_⟩
              · rw [wasm.natural.positive_difference]; simp [run]
              · simp only [positiveValue]; omega
          | some value =>
              cases value with
              | Zero =>
                  refine ⟨none, ?_, ?_⟩
                  · rw [wasm.natural.positive_difference]
                    simp [run, wasm.natural.decrement]
                  · simp only [naturalValue] at equation
                    simp only [positiveValue]
                    omega
              | Positive value =>
                  obtain ⟨previous, decrementRun, decrementValue⟩ :=
                    decrement_total (.Positive value) (positiveValue_pos value)
                  obtain ⟨doubled, doubleRun, doubleValue⟩ := double_plus_one_total previous
                  refine ⟨some doubled, ?_, ?_⟩
                  · rw [wasm.natural.positive_difference]
                    simp [run, decrementRun, doubleRun]
                  · simp only [positiveValue]; omega
  | Bit1 left ih =>
      cases right with
      | One =>
          obtain ⟨previous, run, equation⟩ := predecessor_total (.Bit1 left)
          refine ⟨some previous, ?_, equation⟩
          rw [wasm.natural.positive_difference]
          simp [run]
      | Bit0 right =>
          obtain ⟨output, run, equation⟩ := ih right
          cases output with
          | none =>
              refine ⟨none, ?_, ?_⟩
              · rw [wasm.natural.positive_difference]; simp [run]
              · simp only [positiveValue]; omega
          | some value =>
              obtain ⟨doubled, doubleRun, doubleValue⟩ := double_plus_one_total value
              refine ⟨some doubled, ?_, ?_⟩
              · rw [wasm.natural.positive_difference]; simp [run, doubleRun]
              · simp only [positiveValue]; omega
      | Bit1 right =>
          obtain ⟨output, run, equation⟩ := ih right
          cases output with
          | none =>
              refine ⟨none, ?_, ?_⟩
              · rw [wasm.natural.positive_difference]; simp [run]
              · simp only [positiveValue]; omega
          | some value =>
              obtain ⟨doubled, doubleRun, doubleValue⟩ := double_total value
              refine ⟨some doubled, ?_, ?_⟩
              · rw [wasm.natural.positive_difference]; simp [run, doubleRun]
              · simp only [positiveValue]; omega

/-- Borrowed binary subtraction always terminates and reports underflow exactly. -/
theorem natural_difference_total (left right : Natural) :
    ∃ output, wasm.natural.difference left right = Result.ok output ∧
      match output with
      | none => naturalValue left < naturalValue right
      | some value => naturalValue value + naturalValue right = naturalValue left := by
  cases right with
  | Zero => exact ⟨some left, by simp [wasm.natural.difference], by simp [naturalValue]⟩
  | Positive right =>
      cases left with
      | Zero => exact ⟨none, rfl, positiveValue_pos right⟩
      | Positive left => exact positive_difference_total left right

/-- Exact execution for every pair of mathematical naturals, with no word bound. -/
theorem natural_difference_literal (left right : Nat) :
    wasm.natural.difference (naturalLiteral left) (naturalLiteral right) =
      Result.ok (if right ≤ left then some (naturalLiteral (left - right)) else none) := by
  obtain ⟨output, run, equation⟩ :=
    natural_difference_total (naturalLiteral left) (naturalLiteral right)
  cases output with
  | none =>
      simp only [naturalLiteral_value] at equation
      simpa [show ¬right ≤ left by omega] using run
  | some value =>
      simp only [naturalLiteral_value] at equation
      have bounded : right ≤ left := by omega
      have equal : value = naturalLiteral (left - right) := by
        apply naturalValue_injective
        simp only [naturalLiteral_value]
        omega
      simpa [bounded, equal] using run

open Lean Elab Command in
run_cmd do
  let declarations := [
    ``double_total, ``double_plus_one_total, ``positive_difference_total,
    ``natural_difference_total, ``natural_difference_literal]
  for declaration in declarations do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"

end RustWasm
