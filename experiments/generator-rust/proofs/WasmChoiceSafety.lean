import WasmChoices

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust

@[step] theorem increment_safe (value : wasm.natural.Natural) :
    wasm.natural.increment value ⦃ _ => True ⦄ := by
  obtain ⟨next, run, _⟩ := increment_total value
  simp [run]

@[step] theorem tick_safe (choices : wasm.choices.Choices) :
    wasm.choices.tick choices ⦃ _ => True ⦄ := by
  rcases choices with ⟨source, trace, remaining⟩
  cases remaining with
  | Zero => simp [wasm.choices.tick, wasm.natural.decrement]
  | Positive remaining =>
      obtain ⟨previous, run, _⟩ := predecessor_total remaining
      simp [wasm.choices.tick, wasm.natural.decrement, run]

@[step] theorem next_random_safe (state : U64) :
    generator.next_random state ⦃ _ => True ⦄ := by
  unfold generator.next_random
  step*

@[step] theorem pick_word_range (bound : U64) (choices : wasm.choices.Choices) :
    wasm.choices.pick_word bound choices ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok (value, _) => value.val < bound.val ⦄ := by
  unfold wasm.choices.pick_word
  step* <;> scalar_tac

end RustWasm
