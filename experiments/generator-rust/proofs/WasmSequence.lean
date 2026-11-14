import WasmNaturalEncoding

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.sequence

def sequenceLiteral {α : Type} : List α → Sequence α
  | [] => .Empty
  | head :: tail => .Cons (head, sequenceLiteral tail)

def sequenceValues {α : Type} : Sequence α → List α
  | .Empty => []
  | .Cons (head, tail) => head :: sequenceValues tail

@[simp] theorem sequence_roundtrip {α : Type} (values : List α) :
    sequenceValues (sequenceLiteral values) = values := by
  induction values <;> simp_all [sequenceLiteral, sequenceValues]

@[simp] theorem sequence_literal_values {α : Type} (values : Sequence α) :
    sequenceLiteral (sequenceValues values) = values := by
  cases values with
  | Empty => rfl
  | Cons cell =>
      rcases cell with ⟨head, tail⟩
      simp only [sequenceValues, sequenceLiteral]
      rw [sequence_literal_values tail]
termination_by sizeOf values

/-- The actual recursive Rust container appends without a word-sized length. -/
theorem sequence_append {α : Type} (left right : List α) :
    wasm.sequence.append (sequenceLiteral left) (sequenceLiteral right) =
      Result.ok (sequenceLiteral (left ++ right)) := by
  induction left with
  | nil => simp [sequenceLiteral, wasm.sequence.append]
  | cons head tail ih =>
      rw [sequenceLiteral, wasm.sequence.append]
      simp [ih, wasm.sequence.cons, sequenceLiteral, ↓uncurry_apply_pair]

theorem sequence_snoc {α : Type} (values : List α) (value : α) :
    wasm.sequence.snoc (sequenceLiteral values) value =
      Result.ok (sequenceLiteral (values ++ [value])) := by
  simpa [wasm.sequence.snoc, wasm.sequence.cons, sequenceLiteral] using
    sequence_append values [value]

/-- Length computation returns a canonical unbounded Natural. -/
theorem sequence_length {α : Type} (values : List α) :
    wasm.sequence.length (sequenceLiteral values) = Result.ok (naturalLiteral values.length) := by
  induction values with
  | nil => simp [sequenceLiteral, wasm.sequence.length, naturalLiteral]
  | cons head tail ih =>
      rw [sequenceLiteral, wasm.sequence.length]
      simp [ih, increment_literal, ↓uncurry_apply_pair]

/-- Every shared lookup executes the mathematical list lookup, including misses. -/
theorem sequence_get {α : Type} (values : List α) (index : Nat) :
    wasm.sequence.get (sequenceLiteral values) (naturalLiteral index) =
      Result.ok values[index]? := by
  induction values generalizing index with
  | nil => simp [sequenceLiteral, wasm.sequence.get]
  | cons head tail ih =>
      cases index with
      | zero => simp [sequenceLiteral, wasm.sequence.get, decrement_zero, ↓uncurry_apply_pair]
      | succ index =>
          rw [sequenceLiteral, wasm.sequence.get]
          simp [decrement_literal, ih, ↓uncurry_apply_pair]

/-- Consuming selection has the same exact support as the shared lookup. -/
theorem sequence_select {α : Type} (values : List α) (index : Nat) :
    wasm.sequence.select (sequenceLiteral values) (naturalLiteral index) =
      Result.ok values[index]? := by
  induction values generalizing index with
  | nil => simp [sequenceLiteral, wasm.sequence.select]
  | cons head tail ih =>
      cases index with
      | zero => simp [sequenceLiteral, wasm.sequence.select, decrement_zero, ↓uncurry_apply_pair]
      | succ index =>
          rw [sequenceLiteral, wasm.sequence.select]
          simp [decrement_literal, ih, ↓uncurry_apply_pair]

/-- The last element is preserved, including the empty sequence case. -/
theorem sequence_last {α : Type} (values : List α) :
    wasm.sequence.last (sequenceLiteral values) = Result.ok values.getLast? := by
  induction values with
  | nil => simp [sequenceLiteral, wasm.sequence.last]
  | cons head tail ih =>
      rw [sequenceLiteral, wasm.sequence.last]
      cases tail with
      | nil => simp [sequenceLiteral, ↓uncurry_apply_pair]
      | cons next rest => simpa [sequenceLiteral, ↓uncurry_apply_pair] using ih

theorem sequence_reverse_into {α : Type} (values output : List α) :
    wasm.sequence.reverse_into (sequenceLiteral values) (sequenceLiteral output) =
      Result.ok (sequenceLiteral (values.reverse ++ output)) := by
  induction values generalizing output with
  | nil => simp [sequenceLiteral, wasm.sequence.reverse_into]
  | cons head tail ih =>
      rw [sequenceLiteral, wasm.sequence.reverse_into]
      simp only [↓uncurry_apply_pair, wasm.sequence.cons, bind_ok]
      simpa only [sequenceLiteral, List.reverse_cons, List.singleton_append,
        List.append_assoc] using ih (head :: output)

/-- Source order is restored without a machine-sized cursor. -/
theorem sequence_reverse {α : Type} (values : List α) :
    wasm.sequence.reverse (sequenceLiteral values) = Result.ok (sequenceLiteral values.reverse) := by
  simpa [wasm.sequence.reverse, sequenceLiteral] using sequence_reverse_into values []

/-- An exact split succeeds iff the requested prefix exists; it never truncates. -/
theorem sequence_split {α : Type} (values : List α) (count : Nat) :
    wasm.sequence.split_at (sequenceLiteral values) (naturalLiteral count) =
      Result.ok (if count ≤ values.length then
        some (sequenceLiteral (values.take count), sequenceLiteral (values.drop count)) else none) := by
  induction values generalizing count with
  | nil =>
      cases count with
      | zero => simp [sequenceLiteral, wasm.sequence.split_at, decrement_zero]
      | succ count => simp [sequenceLiteral, wasm.sequence.split_at, decrement_literal]
  | cons head tail ih =>
      cases count with
      | zero =>
          rw [wasm.sequence.split_at]
          simp [decrement_zero, sequenceLiteral]
      | succ count =>
          rw [wasm.sequence.split_at]
          simp only [decrement_literal, bind_ok, sequenceLiteral, ↓uncurry_apply_pair]
          rw [ih]
          by_cases fits : count ≤ tail.length
          · simp [fits, wasm.sequence.cons, sequenceLiteral, ↓uncurry_apply_pair]
          · simp [fits, ↓uncurry_apply_pair]

open Lean Elab Command in
run_cmd do
  let declarations := [
    ``sequence_roundtrip, ``sequence_literal_values, ``sequence_append, ``sequence_snoc,
    ``sequence_length, ``sequence_get, ``sequence_select, ``sequence_last,
    ``sequence_reverse_into, ``sequence_reverse, ``sequence_split]
  for declaration in declarations do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"

end RustWasm
