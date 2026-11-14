import WasmReplayWitness
import WasmChoices

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust

def memoryConfig : wasm.Config := { emptyConfig with max_memories := naturalLiteral 1, work_limit := naturalLiteral 5 }
def memoryCells : List U64 := [0#u64, 1#u64, 0#u64, 0#u64, 0#u64]
def memoryTape : wasm.choices.Tape := tapeFromCells memoryCells
def memoryOutput : wasm.ast.Module :=
  { emptyOutput with memories := .Cons ⟨.I32, 0#u64, none⟩ .Empty }

def memoryState (offset remaining : Nat) : wasm.choices.Choices :=
  ⟨.Replay (tapeFromCells (memoryCells.drop offset)) (naturalLiteral offset),
    tapeFromCells ((memoryCells.take offset).reverse), naturalLiteral remaining⟩

@[local step] theorem memory_pick0 : wasm.choices.pick 1#u64 (memoryState 0 5)
    ⦃ result => result = .Ok (0#usize, memoryState 1 4) ⦄ := by
  unfold memoryState
  apply pick_replay <;> simp [naturalLiteral, positiveLiteral,
    wasm.natural.increment, wasm.natural.decrement, wasm.natural.predecessor]

theorem memory_pick1 : wasm.choices.pick_word 2#u64 (memoryState 1 4)
    = Result.ok (.Ok (1#u64, memoryState 2 3)) := by
  unfold memoryState
  apply pick_word_replay <;> simp [naturalLiteral, positiveLiteral,
    wasm.natural.increment, wasm.natural.increment_positive, wasm.natural.decrement, wasm.natural.predecessor]

theorem memory_pick2 : wasm.choices.pick_word 2#u64 (memoryState 2 3)
    = Result.ok (.Ok (0#u64, memoryState 3 2)) := by
  unfold memoryState
  apply pick_word_replay <;> simp [naturalLiteral, positiveLiteral,
    wasm.natural.increment, wasm.natural.increment_positive, wasm.natural.decrement, wasm.natural.predecessor]

theorem memory_pick3 : wasm.choices.pick_word 65537#u64 (memoryState 3 2) =
    Result.ok (.Ok (0#u64, memoryState 4 1)) := by
  unfold memoryState
  apply pick_word_replay <;> simp [naturalLiteral, positiveLiteral,
    wasm.natural.increment, wasm.natural.increment_positive, wasm.natural.decrement, wasm.natural.predecessor]

theorem memory_pick4 : wasm.choices.pick_word 2#u64 (memoryState 4 1)
    = Result.ok (.Ok (0#u64, memoryState 5 0)) := by
  unfold memoryState
  apply pick_word_replay <;> simp [naturalLiteral, positiveLiteral,
    wasm.natural.increment, wasm.natural.increment_positive, wasm.natural.decrement, wasm.natural.predecessor]

theorem memory_one : wasm.memory.memory (memoryState 2 3) =
    Result.ok (.Ok (⟨.I32, 0#u64, none⟩, memoryState 5 0)) := by
  have h2 := memory_pick2
  have h3 := memory_pick3
  have h4 := memory_pick4
  have add : (65536#u64 + 1#u64) = Result.ok 65537#u64 := by
    apply wp_eq_ok
    step*
  simp [wasm.memory.memory, h2, h3, h4, add,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem memory_generate : wasm.memory.generate (naturalLiteral 1) (memoryState 1 4) =
    Result.ok (.Ok (memoryOutput.memories, memoryState 5 0)) := by
  rw [wasm.memory.generate]
  simp [naturalLiteral, positiveLiteral, wasm.natural.decrement, wasm.natural.predecessor,
    memory_pick1, memory_one, core.result.Result.Insts.CoreOpsTry.branch]
  rw [wasm.memory.generate]
  simp [wasm.natural.decrement, memoryOutput]

theorem memory_types : wasm.types.generate memoryConfig (memoryState 0 5) =
    Result.ok (.Ok (.Empty, .Empty, memoryState 1 4)) := by
  simpa [memoryState, memoryCells, replayState, tapeFromCells] using
    generate_types_zero memoryConfig rfl [1#u64, 0#u64, 0#u64, 0#u64] [] 0 4

theorem memory_replay : wasm.replay memoryConfig memoryTape =
    Result.ok (.Ok (memoryOutput, memoryState 5 0)) := by
  apply replay_from_build memoryConfig memoryTape memoryOutput (memoryState 5 0)
    (naturalLiteral 5) ?_ rfl
  apply build_empty_types memoryConfig _ (memoryState 1 4) (memoryState 1 4) (memoryState 5 0)
    (memoryState 5 0) .Empty memoryOutput.memories .Empty
  · exact memory_types
  · rw [wasm.memory_import.generate]
    simp [memoryConfig, emptyConfig, wasm.natural.decrement]
  · exact memory_generate
  · rw [wasm.data.generate]
    simp [memoryConfig, emptyConfig, wasm.natural.decrement]

/-- The old missing-memory counterexample now has a successful actual replay witness. -/
theorem memory_supported : ReplaySupport memoryConfig memoryOnly := by
  refine ⟨memoryTape, memoryOutput, ⟨memoryState 5 0, memory_replay⟩, ?_⟩
  rfl

theorem memory_generated_valid :
    ReplaySupport memoryConfig memoryOnly ∧ SpecTec.Module_ok memoryOnly :=
  ⟨memory_supported, memoryOnly_ok⟩

end RustWasm
