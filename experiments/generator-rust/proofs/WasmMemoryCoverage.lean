import WasmMemoryReplay
import WasmReplayWitness

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

/-- Input encoding only: generation is performed by the actual translated Rust function. -/
def memoryChoiceCells (item : Memory) : List U64 :=
  match item.maximum with
  | none => [memoryWidth item.address, item.minimum, 0#u64]
  | some maximum => [memoryWidth item.address, item.minimum, 1#u64, memoryExtra item.minimum maximum]

def memorySectionCells : List Memory → List U64
  | [] => []
  | head :: tail => 1#u64 :: (memoryChoiceCells head ++ memorySectionCells tail)

theorem memory_replay_cells (item : Memory) (bounded : MemoryBounded item)
    (rest trace : List U64) (offset work : Nat) :
    wasm.memory.memory
      (replayState (memoryChoiceCells item ++ rest) trace offset (work + (memoryChoiceCells item).length)) =
      Result.ok (.Ok (item, replayState rest ((memoryChoiceCells item).reverse ++ trace)
        (offset + (memoryChoiceCells item).length) work)) := by
  rcases item with ⟨address, minimum, maximum⟩
  cases maximum with
  | none =>
      simpa [memoryChoiceCells] using memory_none_replay address minimum bounded.1 rest trace offset work
  | some maximum =>
      have limits := bounded.2 maximum rfl
      simpa [memoryChoiceCells] using memory_some_replay address minimum maximum limits.1 limits.2 rest trace offset work

/-- Every finite valid memory list is produced by the actual recursive constructor.
The maximum and work budget are real Rust binary naturals, with no machine-size premise. -/
theorem memory_section_replay (items : List Memory)
    (bounded : ∀ item ∈ items, MemoryBounded item)
    (rest trace : List U64) (offset work : Nat) :
    wasm.memory.generate (naturalLiteral items.length)
      (replayState (memorySectionCells items ++ rest) trace offset (work + (memorySectionCells items).length)) =
      Result.ok (.Ok (memoryList items,
        replayState rest ((memorySectionCells items).reverse ++ trace)
          (offset + (memorySectionCells items).length) work)) := by
  induction items generalizing rest trace offset work with
  | nil =>
      rw [wasm.memory.generate]
      simp [memorySectionCells, memoryList]
  | cons head tail ih =>
      have headBound := bounded head (by simp)
      have tailBound : ∀ item ∈ tail, MemoryBounded item := by
        intro item present
        exact bounded item (by simp [present])
      have moreRun := pick_word_state 2#u64 1#u64
        (memoryChoiceCells head ++ (memorySectionCells tail ++ rest)) trace offset
        (work + (memorySectionCells tail).length + (memoryChoiceCells head).length) (by decide)
      have headRun := memory_replay_cells head headBound (memorySectionCells tail ++ rest)
        (1#u64 :: trace) (offset + 1) (work + (memorySectionCells tail).length)
      have tailRun := ih tailBound rest ((memoryChoiceCells head).reverse ++ 1#u64 :: trace)
        (offset + 1 + (memoryChoiceCells head).length) work
      rw [wasm.memory.generate]
      simp only [List.length_cons, decrement_literal]
      simp [memorySectionCells, memoryList, List.append_assoc, List.reverse_append,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at moreRun headRun tailRun ⊢
      rw [moreRun]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      rw [headRun]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      rw [tailRun]
      simp

end RustWasm
