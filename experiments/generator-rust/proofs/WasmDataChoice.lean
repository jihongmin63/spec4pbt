import WasmReplaySteps
import WasmDataEncoding

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

def textCells : List Char → List U64
  | [] => [0#u64]
  | head :: tail => 1#u64 :: charChoice head :: textCells tail

private theorem char_choice_run (value : Char) :
    (if charChoice value < 55296#u64 then Result.ok (UScalar.cast .U32 (charChoice value))
      else do
        let scalar ← charChoice value + 2048#u64
        Result.ok (UScalar.cast .U32 scalar)) = Result.ok (charScalar value) := by
  have decoded := char_choice_decode value
  have bounded := value.ordinal.isLt
  simp only [Char.numCodePoints] at bounded
  apply wp_eq_ok
  unfold charChoice charScalar
  step* <;> scalar_tac

/-- The actual Rust text chooser produces every finite sequence of Unicode scalars. -/
theorem text_choice_replay (values : List Char) (rest trace : List U64) (offset work : Nat) :
    wasm.data.text
      (replayState (textCells values ++ rest) trace offset (work + (textCells values).length)) =
      Result.ok (.Ok (textLiteral values,
        replayState rest ((textCells values).reverse ++ trace)
          (offset + (textCells values).length) work)) := by
  induction values generalizing trace offset with
  | nil =>
      have stop := pick_word_state 2#u64 0#u64 rest trace offset work (by decide)
      rw [wasm.data.text]
      simp [textCells, textLiteral, stop, core.result.Result.Insts.CoreOpsTry.branch]
  | cons head tail ih =>
      have more := pick_word_state 2#u64 1#u64 (charChoice head :: (textCells tail ++ rest))
        trace offset (work + (textCells tail).length + 1) (by decide)
      have bound : (charChoice head).val < (1112064#u64).val := by
        rw [charChoice_val]
        change head.ordinal.val < 1112064
        exact head.ordinal.isLt
      have scalar := pick_word_state 1112064#u64 (charChoice head) (textCells tail ++ rest)
        (1#u64 :: trace) (offset + 1) (work + (textCells tail).length) bound
      rw [wasm.data.text]
      simp only [textCells, textLiteral, List.cons_append, List.length_cons, Nat.add_assoc] at more scalar ⊢
      rw [more]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      erw [scalar]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      erw [char_choice_run]
      simp
      erw [ih]
      simp [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def dataLiteral : List String → Datas
  | [] => .Empty
  | head :: tail => .Cons (textLiteral head.toList) (dataLiteral tail)

def dataCells : List String → List U64
  | [] => []
  | head :: tail => 1#u64 :: (textCells head.toList ++ dataCells tail)

/-- The section budget is an arbitrary Natural, not a machine-sized list count. -/
theorem data_section_replay (payloads : List String)
    (rest trace : List U64) (offset work : Nat) :
    wasm.data.generate (naturalLiteral payloads.length)
      (replayState (dataCells payloads ++ rest) trace offset (work + (dataCells payloads).length)) =
      Result.ok (.Ok (dataLiteral payloads,
        replayState rest ((dataCells payloads).reverse ++ trace)
          (offset + (dataCells payloads).length) work)) := by
  induction payloads generalizing rest trace offset work with
  | nil =>
      rw [wasm.data.generate]
      simp [dataCells, dataLiteral]
  | cons head tail ih =>
      have more := pick_word_state 2#u64 1#u64
        (textCells head.toList ++ (dataCells tail ++ rest)) trace offset
        (work + (dataCells tail).length + (textCells head.toList).length) (by decide)
      have textRun := text_choice_replay head.toList (dataCells tail ++ rest)
        (1#u64 :: trace) (offset + 1) (work + (dataCells tail).length)
      have tailRun := ih rest ((textCells head.toList).reverse ++ 1#u64 :: trace)
        (offset + 1 + (textCells head.toList).length) work
      rw [wasm.data.generate]
      simp only [List.length_cons, decrement_literal]
      simp [dataCells, dataLiteral, List.append_assoc, List.reverse_append,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at more textRun tailRun ⊢
      rw [more]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      rw [textRun]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      rw [tailRun]
      simp

end RustWasm
