import WasmChoiceSafety
import WasmMemoryProperties
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.FailIfNoProgress

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust

theorem memory_constructor_spec (choices : wasm.choices.Choices) :
    wasm.memory.memory choices ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok (item, _) => MemoryBounded item ⦄ := by
  unfold wasm.memory.memory
  step*
  all_goals
    rcases val with ⟨width, nextChoices⟩
    by_cases widthZero : width = 0#u64
    all_goals
      simp [widthZero]
      repeat' first
        | casesm _ × _
        | cases_type core.result.Result
        | fail_if_no_progress simp_all [MemoryBounded, memoryPageLimit]
        | fail_if_no_progress step* +splitMatch
      all_goals scalar_tac

/-- Any successful actual memory construction satisfies the original page inequalities. -/
theorem memory_constructor_sound (choices : wasm.choices.Choices)
    (item : wasm.ast.Memory) (finalState : wasm.choices.Choices)
    (success : wasm.memory.memory choices = Result.ok (.Ok (item, finalState))) :
    MemoryBounded item := by
  have correct := memory_constructor_spec choices
  simpa [success] using correct

theorem memory_constructor_valid (context : SpecTec.context) (choices : wasm.choices.Choices)
    (item : wasm.ast.Memory) (finalState : wasm.choices.Choices)
    (success : wasm.memory.memory choices = Result.ok (.Ok (item, finalState))) :
    SpecTec.Memtype_ok context (memory item).MTYPE :=
  memory_bounded_valid context item (memory_constructor_sound choices item finalState success)

end RustWasm
