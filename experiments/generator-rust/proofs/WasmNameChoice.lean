import WasmNaturalChoice
import WasmSequence

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.natural

def nameCells : List Natural → List U64
  | [] => [0#u64]
  | head :: tail => 1#u64 :: (naturalCells head ++ nameCells tail)

/-- Actual recursive name selection covers every finite list of unbounded naturals. -/
theorem name_choice_replay (values : List Natural)
    (rest trace : List U64) (offset work : Nat) :
    wasm.memory_import.name
      (replayState (nameCells values ++ rest) trace offset (work + (nameCells values).length)) =
      Result.ok (.Ok (sequenceLiteral values,
        replayState rest ((nameCells values).reverse ++ trace)
          (offset + (nameCells values).length) work)) := by
  induction values generalizing trace offset work with
  | nil =>
      have stop := pick_word_state 2#u64 0#u64 rest trace offset work (by decide)
      rw [wasm.memory_import.name]
      simp [nameCells, sequenceLiteral, stop, core.result.Result.Insts.CoreOpsTry.branch]
  | cons head tail ih =>
      have more := pick_word_state 2#u64 1#u64
        (naturalCells head ++ (nameCells tail ++ rest)) trace offset
        (work + (nameCells tail).length + (naturalCells head).length) (by decide)
      have headRun := natural_choice_replay head (nameCells tail ++ rest)
        (1#u64 :: trace) (offset + 1) (work + (nameCells tail).length)
      have tailRun := ih ((naturalCells head).reverse ++ 1#u64 :: trace)
        (offset + 1 + (naturalCells head).length) work
      rw [wasm.memory_import.name]
      simp [nameCells, List.append_assoc, List.reverse_append,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at more headRun tailRun ⊢
      rw [more]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      rw [headRun]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      rw [tailRun]
      simp [wasm.sequence.cons, sequenceLiteral]

def nameLiteral (values : List Nat) : wasm.sequence.Sequence Natural :=
  sequenceLiteral (values.map naturalLiteral)

theorem name_literal_roundtrip (values : List Nat) :
    (sequenceValues (nameLiteral values)).map naturalValue = values := by
  simp [nameLiteral, List.map_map, Function.comp_def]

/-- No character, byte, machine-word, or total-name-length premise is added. -/
theorem name_literal_replay (values : List Nat)
    (rest trace : List U64) (offset work : Nat) :
    wasm.memory_import.name
      (replayState (nameCells (values.map naturalLiteral) ++ rest) trace offset
        (work + (nameCells (values.map naturalLiteral)).length)) =
      Result.ok (.Ok (nameLiteral values,
        replayState rest ((nameCells (values.map naturalLiteral)).reverse ++ trace)
          (offset + (nameCells (values.map naturalLiteral)).length) work)) :=
  name_choice_replay (values.map naturalLiteral) rest trace offset work

end RustWasm
