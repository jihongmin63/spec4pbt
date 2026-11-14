import WasmNaturalDifference
import WasmSequence
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast wasm.natural

/-- The actual equality helper terminates and compares mathematical natural values. -/
theorem same_natural_total (left right : Natural) :
    wasm.type_matching.same_natural left right =
      Result.ok (decide (naturalValue left = naturalValue right)) := by
  obtain ⟨output, run, equation⟩ := natural_difference_total left right
  cases output with
  | none =>
      have different : naturalValue left ≠ naturalValue right := by omega
      simp [wasm.type_matching.same_natural, run, different]
  | some value =>
      cases value with
      | Zero =>
          change 0 + naturalValue right = naturalValue left at equation
          have equal : naturalValue left = naturalValue right := by omega
          simp [wasm.type_matching.same_natural, run, equal]
      | Positive value =>
          have positive := positiveValue_pos value
          change positiveValue value + naturalValue right = naturalValue left at equation
          have different : naturalValue left ≠ naturalValue right := by omega
          simp [wasm.type_matching.same_natural, run, different]

/-- The newest completed result for this exact ordered pair of mathematical indices. -/
def comparisonLookup : List wasm.type_matching.Comparison → Nat → Nat → Option Bool
  | [], _, _ => none
  | head :: tail, left, right =>
      if naturalValue head.left = left ∧ naturalValue head.right = right then
        some head.equal
      else comparisonLookup tail left right

/-- The actual cache lookup terminates and uses both exact unbounded index values. -/
theorem completed_lookup (comparisons : List wasm.type_matching.Comparison)
    (left right : Natural) :
    wasm.type_matching.completed (sequenceLiteral comparisons) left right =
      Result.ok (comparisonLookup comparisons (naturalValue left) (naturalValue right)) := by
  induction comparisons with
  | nil => simp [wasm.type_matching.completed, sequenceLiteral, comparisonLookup]
  | cons head tail ih =>
      by_cases leftEqual : naturalValue head.left = naturalValue left
      · by_cases rightEqual : naturalValue head.right = naturalValue right
        all_goals simp [wasm.type_matching.completed, sequenceLiteral, comparisonLookup,
          same_natural_total, leftEqual, rightEqual, ih]
      · simp [wasm.type_matching.completed, sequenceLiteral, comparisonLookup,
          same_natural_total, leftEqual, ih]

/-- A cache hit always comes from a completed record for both requested indices. -/
theorem comparison_lookup_sound (comparisons : List wasm.type_matching.Comparison)
    (left right : Nat) (equal : Bool)
    (found : comparisonLookup comparisons left right = some equal) :
    ∃ entry ∈ comparisons,
      naturalValue entry.left = left ∧ naturalValue entry.right = right ∧ entry.equal = equal := by
  induction comparisons with
  | nil => simp [comparisonLookup] at found
  | cons head tail ih =>
      by_cases matching : naturalValue head.left = left ∧ naturalValue head.right = right
      · have value : head.equal = equal := by simpa [comparisonLookup, matching] using found
        exact ⟨head, by simp, matching.1, matching.2, value⟩
      · have remaining : comparisonLookup tail left right = some equal := by
          simpa [comparisonLookup, matching] using found
        obtain ⟨entry, present, matched⟩ := ih remaining
        exact ⟨entry, by simp [present], matched⟩

/-- Only indices inside this group roll to relative recursive variables. -/
theorem recursive_index_literal (index base width : Nat) :
    wasm.type_matching.recursive_index (naturalLiteral index) (naturalLiteral base)
      (naturalLiteral width) =
      Result.ok (if base ≤ index ∧ index < base + width then
        some (naturalLiteral (index - base)) else none) := by
  rw [wasm.type_matching.recursive_index, natural_difference_literal]
  by_cases lower : base ≤ index
  · by_cases upper : index < base + width
    · have under : ¬width ≤ index - base := by omega
      simp [lower, upper, natural_difference_literal, under]
    · have over : width ≤ index - base := by omega
      simp [lower, upper, natural_difference_literal, over]
  · simp [lower]

/-- Flat type indices count members, including zero members in an empty group. -/
def typeMemberCount : List RecGroup → Nat
  | [] => 0
  | group :: tail => (sequenceValues group.members).length + typeMemberCount tail

private theorem group_length (group : RecGroup) :
    wasm.sequence.length group.members =
      Result.ok (naturalLiteral (sequenceValues group.members).length) := by
  simpa using sequence_length (sequenceValues group.members)

/-- Every in-range member is found with its original raw group and relative position. -/
theorem containing_group_split (before : List RecGroup) (group : RecGroup)
    (after : List RecGroup) (position : Nat)
    (bounded : position < (sequenceValues group.members).length) :
    wasm.type_matching.containing_group (sequenceLiteral (before ++ group :: after))
      (naturalLiteral (typeMemberCount before + position)) =
      Result.ok (.Ok (group, naturalLiteral position)) := by
  induction before with
  | nil =>
      rw [show ([] : List RecGroup) ++ group :: after = group :: after from rfl]
      rw [sequenceLiteral, wasm.type_matching.containing_group]
      have under : ¬(sequenceValues group.members).length ≤ position := by omega
      simp [typeMemberCount, group_length, natural_difference_literal, under,
        ↓uncurry_apply_pair]
  | cons head tail ih =>
      rw [List.cons_append, sequenceLiteral, wasm.type_matching.containing_group]
      simp [group_length, natural_difference_literal, typeMemberCount,
        Nat.add_assoc, ih, ↓uncurry_apply_pair]

/-- Out-of-range flat indices fail explicitly, even through arbitrarily many empty groups. -/
theorem containing_group_missing (groups : List RecGroup) (extra : Nat) :
    wasm.type_matching.containing_group (sequenceLiteral groups)
      (naturalLiteral (typeMemberCount groups + extra)) =
      Result.ok (.Err wasm.choices.GenerationError.InternalInvariant) := by
  induction groups with
  | nil => simp [sequenceLiteral, wasm.type_matching.containing_group]
  | cons head tail ih =>
      rw [sequenceLiteral, wasm.type_matching.containing_group]
      simp [group_length, natural_difference_literal, typeMemberCount,
        Nat.add_assoc, ih, ↓uncurry_apply_pair]

open Lean Elab Command in
run_cmd do
  for declaration in [``same_natural_total, ``completed_lookup, ``comparison_lookup_sound, ``recursive_index_literal,
      ``containing_group_split, ``containing_group_missing] do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"

end RustWasm
