import WasmChoices
import WasmNaturalEncoding

set_option autoImplicit false

namespace RustWasm
open Aeneas Aeneas.Std generator_rust

/-- A finite mathematical prefix is encoded into the actual recursive Rust input/state. -/
def replayState (input trace : List U64) (offset work : Nat) : wasm.choices.Choices :=
  ⟨.Replay (tapeFromCells input) (naturalLiteral offset),
    tapeFromCells trace, naturalLiteral work⟩

theorem pick_word_state (bound cell : U64) (tail trace : List U64) (offset work : Nat)
    (inRange : cell.val < bound.val) :
    wasm.choices.pick_word bound (replayState (cell :: tail) trace offset (work + 1)) =
      Result.ok (.Ok (cell, replayState tail (cell :: trace) (offset + 1) work)) := by
  unfold replayState
  exact pick_word_replay _ _ _ _ _ _ bound cell inRange
    (increment_literal offset) (decrement_literal work)

theorem pick_state (bound cell : U64) (selected : Usize) (tail trace : List U64)
    (offset work : Nat) (inRange : cell.val < bound.val) (value : selected.val = cell.val) :
    wasm.choices.pick bound (replayState (cell :: tail) trace offset (work + 1)) =
      Result.ok (.Ok (selected, replayState tail (cell :: trace) (offset + 1) work)) := by
  apply wp_eq_ok
  unfold replayState
  exact pick_replay _ _ _ _ _ _ bound cell selected inRange value
    (increment_literal offset) (decrement_literal work)

end RustWasm
