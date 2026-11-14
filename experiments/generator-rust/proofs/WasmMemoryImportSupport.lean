import WasmMemoryImportChoice
import WasmMemoryImportSpecification

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

def memoryImportListConfig (items : List MemoryImport) : wasm.Config :=
  { emptyConfig with
    max_memory_imports := naturalLiteral items.length
    work_limit := naturalLiteral ((memoryImportSectionCells items).length + 1) }

def memoryImportListOutput (items : List MemoryImport) : wasm.ast.Module :=
  { emptyOutput with memory_imports := sequenceLiteral items }

def memoryImportListFinal (items : List MemoryImport) : wasm.choices.Choices :=
  replayState [] ((memoryImportSectionCells items).reverse ++ [0#u64])
    ((memoryImportSectionCells items).length + 1) 0

/-- Full actual replay, including type generation and every later module stage. -/
theorem memory_import_list_replay (items : List MemoryImport)
    (bounded : ∀ item ∈ items, MemoryBounded item.memory) :
    wasm.replay (memoryImportListConfig items)
      (tapeFromCells (0#u64 :: memoryImportSectionCells items)) =
      Result.ok (.Ok (memoryImportListOutput items, memoryImportListFinal items)) := by
  apply replay_from_build (memoryImportListConfig items) _ _ (memoryImportListFinal items)
    (naturalLiteral ((memoryImportSectionCells items).length + 1)) ?_ rfl
  let afterTypes := replayState (memoryImportSectionCells items) [0#u64] 1
    (memoryImportSectionCells items).length
  apply build_empty_types (memoryImportListConfig items) _ afterTypes
    (memoryImportListFinal items) (memoryImportListFinal items) (memoryImportListFinal items)
    (sequenceLiteral items) .Empty .Empty
  · exact generate_types_zero (memoryImportListConfig items) rfl
      (memoryImportSectionCells items) [] 0 (memoryImportSectionCells items).length
  · have generated := memory_import_section_replay items bounded [] [0#u64] 1 0
    simpa [memoryImportListConfig, memoryImportListFinal, afterTypes, Nat.add_comm] using generated
  · rw [wasm.memory.generate]
    simp [memoryImportListConfig, emptyConfig, wasm.natural.decrement]
  · rw [wasm.data.generate]
    simp [memoryImportListConfig, emptyConfig, wasm.natural.decrement]

theorem memory_import_list_supported (items : List MemoryImport)
    (bounded : ∀ item ∈ items, MemoryBounded item.memory) :
    ReplaySupport (memoryImportListConfig items)
      { emptyModule with IMPORTS := items.map memoryImport } := by
  refine ⟨tapeFromCells (0#u64 :: memoryImportSectionCells items), memoryImportListOutput items,
    ⟨memoryImportListFinal items, memory_import_list_replay items bounded⟩, ?_⟩
  simp [embed, memoryImportListOutput, emptyOutput, emptyModule, memoryOnly,
    sequenceValues, sequenceLiteral, memories, datas]

theorem memory_import_list_generated_valid (items : List MemoryImport)
    (bounded : ∀ item ∈ items, MemoryBounded item.memory) :
    ReplaySupport (memoryImportListConfig items)
      { emptyModule with IMPORTS := items.map memoryImport } ∧
      SpecTec.Module_ok { emptyModule with IMPORTS := items.map memoryImport } :=
  ⟨memory_import_list_supported items bounded, memory_import_list_valid items bounded⟩

end RustWasm
