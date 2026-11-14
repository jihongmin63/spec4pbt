import WasmMemoryCoverage

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

def memoryListConfig (items : List Memory) : wasm.Config :=
  { emptyConfig with
    max_memories := naturalLiteral items.length
    work_limit := naturalLiteral ((memorySectionCells items).length + 1) }

def memoryListOutput (items : List Memory) : wasm.ast.Module :=
  { emptyOutput with memories := memoryList items }

def memoryListFinal (items : List Memory) : wasm.choices.Choices :=
  replayState [] ((memorySectionCells items).reverse ++ [0#u64])
    ((memorySectionCells items).length + 1) 0

theorem memory_list_types (items : List Memory) :
    wasm.types.generate (memoryListConfig items)
      (replayState (0#u64 :: memorySectionCells items) [] 0 ((memorySectionCells items).length + 1)) =
      Result.ok (.Ok (.Empty, .Empty,
        replayState (memorySectionCells items) [0#u64] 1 (memorySectionCells items).length)) :=
  generate_types_zero (memoryListConfig items) rfl (memorySectionCells items) [] 0
    (memorySectionCells items).length

/-- The full translated replay entry point produces every bounded memory list.
There is no bound on the list length; page bounds are the original Wasm limits. -/
theorem memory_list_replay (items : List Memory)
    (bounded : ∀ item ∈ items, MemoryBounded item) :
    wasm.replay (memoryListConfig items) (tapeFromCells (0#u64 :: memorySectionCells items)) =
      Result.ok (.Ok (memoryListOutput items, memoryListFinal items)) := by
  apply replay_from_build (memoryListConfig items) _ _ (memoryListFinal items)
    (naturalLiteral ((memorySectionCells items).length + 1)) ?_ rfl
  let afterTypes := replayState (memorySectionCells items) [0#u64] 1 (memorySectionCells items).length
  apply build_empty_types (memoryListConfig items) _ afterTypes afterTypes (memoryListFinal items)
    (memoryListFinal items) .Empty (memoryList items) .Empty
  · exact memory_list_types items
  · rw [wasm.memory_import.generate]
    simp [memoryListConfig, emptyConfig, wasm.natural.decrement]
  · have generated := memory_section_replay items bounded [] [0#u64] 1 0
    simpa [memoryListConfig, memoryListFinal, afterTypes, Nat.add_comm] using generated
  · rw [wasm.data.generate]
    simp [memoryListConfig, emptyConfig, wasm.natural.decrement]

theorem memory_list_supported (items : List Memory)
    (bounded : ∀ item ∈ items, MemoryBounded item) :
    ReplaySupport (memoryListConfig items) { emptyModule with MEMS := items.map memory } := by
  refine ⟨tapeFromCells (0#u64 :: memorySectionCells items), memoryListOutput items,
    ⟨memoryListFinal items, memory_list_replay items bounded⟩, ?_⟩
  simp [embed, memoryListOutput, emptyOutput, emptyModule, memoryOnly, memories_list,
    sequenceValues, datas]

end RustWasm
