import WasmNameChoice
import WasmMemoryCoverage

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

def memoryImportCells (item : MemoryImport) : List U64 :=
  memoryChoiceCells item.memory ++ nameCells (sequenceValues item.module_name) ++
    nameCells (sequenceValues item.item_name)

def memoryImportSectionCells : List MemoryImport → List U64
  | [] => []
  | head :: tail => 1#u64 :: (memoryImportCells head ++ memoryImportSectionCells tail)

/-- Names, descriptor and exact state are produced by the translated entry constructor. -/
theorem memory_import_entry_replay (item : MemoryImport) (bounded : MemoryBounded item.memory)
    (rest trace : List U64) (offset work : Nat) :
    wasm.memory_import.entry
      (replayState (memoryImportCells item ++ rest) trace offset
        (work + (memoryImportCells item).length)) =
      Result.ok (.Ok (item,
        replayState rest ((memoryImportCells item).reverse ++ trace)
          (offset + (memoryImportCells item).length) work)) := by
  have descriptorRun := memory_replay_cells item.memory bounded
    (nameCells (sequenceValues item.module_name) ++ nameCells (sequenceValues item.item_name) ++ rest)
    trace offset
    (work + (nameCells (sequenceValues item.item_name)).length +
      (nameCells (sequenceValues item.module_name)).length)
  have moduleRun := name_choice_replay (sequenceValues item.module_name)
    (nameCells (sequenceValues item.item_name) ++ rest)
    ((memoryChoiceCells item.memory).reverse ++ trace)
    (offset + (memoryChoiceCells item.memory).length)
    (work + (nameCells (sequenceValues item.item_name)).length)
  have itemRun := name_choice_replay (sequenceValues item.item_name) rest
    ((nameCells (sequenceValues item.module_name)).reverse ++
      (memoryChoiceCells item.memory).reverse ++ trace)
    (offset + (memoryChoiceCells item.memory).length +
      (nameCells (sequenceValues item.module_name)).length) work
  rw [wasm.memory_import.entry]
  simp [memoryImportCells, List.append_assoc, List.reverse_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at descriptorRun moduleRun itemRun ⊢
  rw [descriptorRun]
  simp [core.result.Result.Insts.CoreOpsTry.branch]
  rw [moduleRun]
  simp [core.result.Result.Insts.CoreOpsTry.branch]
  rw [itemRun]
  simp

/-- Arbitrary import-list length is connected to actual execution, without a Vec bound. -/
theorem memory_import_section_replay (items : List MemoryImport)
    (bounded : ∀ item ∈ items, MemoryBounded item.memory)
    (rest trace : List U64) (offset work : Nat) :
    wasm.memory_import.generate (naturalLiteral items.length)
      (replayState (memoryImportSectionCells items ++ rest) trace offset
        (work + (memoryImportSectionCells items).length)) =
      Result.ok (.Ok (sequenceLiteral items,
        replayState rest ((memoryImportSectionCells items).reverse ++ trace)
          (offset + (memoryImportSectionCells items).length) work)) := by
  induction items generalizing rest trace offset work with
  | nil =>
      rw [wasm.memory_import.generate]
      simp [memoryImportSectionCells, sequenceLiteral]
  | cons head tail ih =>
      have headBound := bounded head (by simp)
      have tailBound : ∀ item ∈ tail, MemoryBounded item.memory := by
        intro item present
        exact bounded item (by simp [present])
      have moreRun := pick_word_state 2#u64 1#u64
        (memoryImportCells head ++ (memoryImportSectionCells tail ++ rest)) trace offset
        (work + (memoryImportSectionCells tail).length + (memoryImportCells head).length)
        (by decide)
      have headRun := memory_import_entry_replay head headBound
        (memoryImportSectionCells tail ++ rest) (1#u64 :: trace) (offset + 1)
        (work + (memoryImportSectionCells tail).length)
      have tailRun := ih tailBound rest ((memoryImportCells head).reverse ++ 1#u64 :: trace)
        (offset + 1 + (memoryImportCells head).length) work
      rw [wasm.memory_import.generate]
      simp only [List.length_cons, decrement_literal]
      simp [memoryImportSectionCells, List.append_assoc, List.reverse_append,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at moreRun headRun tailRun ⊢
      rw [moreRun]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      rw [headRun]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      rw [tailRun]
      simp [wasm.sequence.cons, sequenceLiteral]

end RustWasm
