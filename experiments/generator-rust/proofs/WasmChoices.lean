import WasmNatural

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust
open wasm.choices wasm.natural

def tapeCells : Tape → List U64
  | .Empty => []
  | .Cons head tail => head :: tapeCells tail

def tapeFromCells : List U64 → Tape
  | [] => .Empty
  | head :: tail => .Cons head (tapeFromCells tail)

/-- Every finite mathematical word list is an actual replay tape, without a Vec length bound. -/
@[simp] theorem tape_roundtrip (cells : List U64) : tapeCells (tapeFromCells cells) = cells := by
  induction cells <;> simp_all [tapeCells, tapeFromCells]

/-- The unused-tape diagnostic also counts without a machine-sized length or cursor. -/
theorem length_from_total (tape : Tape) (offset : Natural) :
    ∃ total, length_from tape offset = Result.ok total ∧
      naturalValue total = naturalValue offset + (tapeCells tape).length := by
  induction tape generalizing offset with
  | Empty => exact ⟨offset, by rw [length_from], by simp [tapeCells]⟩
  | Cons head tail ih =>
      obtain ⟨next, runOffset, offsetValue⟩ := increment_total offset
      obtain ⟨total, runTail, totalValue⟩ := ih next
      refine ⟨total, ?_, ?_⟩
      · rw [length_from]; simp [runOffset, runTail]
      · simp only [tapeCells, List.length_cons]; omega

theorem tick_success (source : Source) (trace : Tape) (remaining nextRemaining : Natural)
    (budgetStep : wasm.natural.decrement remaining = Result.ok (some nextRemaining)) :
    tick ⟨source, trace, remaining⟩ = Result.ok (.Ok ⟨source, trace, nextRemaining⟩) := by
  simp [tick, budgetStep]

/-- Exact unbounded-tape consumption by the actual translated word reader. -/
theorem word_replay (tail trace : Tape) (offset nextOffset remaining nextRemaining : Natural)
    (cell : U64)
    (offsetStep : wasm.natural.increment offset = Result.ok nextOffset)
    (budgetStep : wasm.natural.decrement remaining = Result.ok (some nextRemaining)) :
    word ⟨.Replay (.Cons cell tail) offset, trace, remaining⟩ =
      Result.ok (.Ok (cell, ⟨.Replay tail nextOffset, .Cons cell trace, nextRemaining⟩)) := by
  simp [word, tick, budgetStep, offsetStep, core.result.Result.Insts.CoreOpsTry.branch]

/-- No cursor, trace-length, or budget-word bound is needed for bounded choices. -/
theorem pick_word_replay (tail trace : Tape) (offset nextOffset remaining nextRemaining : Natural)
    (bound cell : U64) (inRange : cell.val < bound.val)
    (offsetStep : wasm.natural.increment offset = Result.ok nextOffset)
    (budgetStep : wasm.natural.decrement remaining = Result.ok (some nextRemaining)) :
    pick_word bound ⟨.Replay (.Cons cell tail) offset, trace, remaining⟩ =
      Result.ok (.Ok (cell, ⟨.Replay tail nextOffset, .Cons cell trace, nextRemaining⟩)) := by
  have nonzero : bound ≠ 0#u64 := by scalar_tac
  simp [pick_word, nonzero, inRange, tick, budgetStep, offsetStep,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem pick_replay (tail trace : Tape) (offset nextOffset remaining nextRemaining : Natural)
    (bound cell : U64) (selected : Usize) (inRange : cell.val < bound.val)
    (selectedValue : selected.val = cell.val)
    (offsetStep : wasm.natural.increment offset = Result.ok nextOffset)
    (budgetStep : wasm.natural.decrement remaining = Result.ok (some nextRemaining)) :
    pick bound ⟨.Replay (.Cons cell tail) offset, trace, remaining⟩
      ⦃ result => result = .Ok (selected,
        ⟨.Replay tail nextOffset, .Cons cell trace, nextRemaining⟩) ⦄ := by
  have run := pick_word_replay tail trace offset nextOffset remaining nextRemaining
    bound cell inRange offsetStep budgetStep
  simp only [pick, run, core.result.Result.Insts.CoreOpsTry.branch]
  step*
  all_goals simp_all [UScalar.eq_equiv]
  · scalar_tac
  · apply Nat.mod_eq_of_lt
    rw [← selectedValue]
    exact selected.hBounds

/-- Total progress follows from the positive binary budget, with no extra machine bound. -/
theorem word_replay_total (tail trace : Tape) (offset remaining : Natural) (cell : U64)
    (budgetPositive : 0 < naturalValue remaining) :
    ∃ nextOffset nextRemaining,
      word ⟨.Replay (.Cons cell tail) offset, trace, remaining⟩ =
        Result.ok (.Ok (cell, ⟨.Replay tail nextOffset, .Cons cell trace, nextRemaining⟩)) ∧
      naturalValue nextOffset = naturalValue offset + 1 ∧
      naturalValue nextRemaining + 1 = naturalValue remaining := by
  obtain ⟨nextOffset, stepOffset, offsetValue⟩ := increment_total offset
  obtain ⟨nextRemaining, stepBudget, remainingValue⟩ := decrement_total remaining budgetPositive
  exact ⟨nextOffset, nextRemaining,
    word_replay tail trace offset nextOffset remaining nextRemaining cell stepOffset stepBudget,
    offsetValue, remainingValue⟩

end RustWasm
