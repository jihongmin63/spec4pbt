import WasmReplaySteps

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.natural

def positiveCells : Positive → List U64
  | .One => [0#u64]
  | .Bit0 tail => 1#u64 :: positiveCells tail
  | .Bit1 tail => 2#u64 :: positiveCells tail

def naturalCells : Natural → List U64
  | .Zero => [0#u64]
  | .Positive value => 4294967296#u64 :: positiveCells value

/-- The recursive Rust chooser executes every finite binary numeral exactly. -/
theorem positive_choice_replay (value : Positive) (rest trace : List U64) (offset work : Nat) :
    wasm.choices.positive
      (replayState (positiveCells value ++ rest) trace offset (work + (positiveCells value).length)) =
      Result.ok (.Ok (value, replayState rest ((positiveCells value).reverse ++ trace)
        (offset + (positiveCells value).length) work)) := by
  induction value generalizing trace offset with
  | One =>
      have picked := pick_word_state 3#u64 0#u64 rest trace offset work (by decide)
      rw [wasm.choices.positive]
      simp [positiveCells, picked, core.result.Result.Insts.CoreOpsTry.branch]
  | Bit0 value ih =>
      have picked := pick_word_state 3#u64 1#u64 (positiveCells value ++ rest) trace offset
        (work + (positiveCells value).length) (by decide)
      rw [wasm.choices.positive]
      simp only [positiveCells, List.cons_append, List.length_cons, Nat.add_assoc] at picked ⊢
      rw [picked]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | Bit1 value ih =>
      have picked := pick_word_state 3#u64 2#u64 (positiveCells value ++ rest) trace offset
        (work + (positiveCells value).length) (by decide)
      rw [wasm.choices.positive]
      simp only [positiveCells, List.cons_append, List.length_cons, Nat.add_assoc] at picked ⊢
      rw [picked]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem natural_choice_replay (value : Natural) (rest trace : List U64) (offset work : Nat) :
    wasm.choices.natural
      (replayState (naturalCells value ++ rest) trace offset (work + (naturalCells value).length)) =
      Result.ok (.Ok (value, replayState rest ((naturalCells value).reverse ++ trace)
        (offset + (naturalCells value).length) work)) := by
  have shift : 1#u64 <<< 32#i32 = Result.ok 4294967296#u64 := by
    apply wp_eq_ok
    step* <;> scalar_tac
  have add : 4294967296#u64 + 1#u64 = Result.ok 4294967297#u64 := by
    apply wp_eq_ok
    step* <;> scalar_tac
  cases value with
  | Zero =>
      have picked := pick_word_state 4294967297#u64 0#u64 rest trace offset work (by decide)
      simp [wasm.choices.natural, naturalCells, shift, add, picked,
        core.result.Result.Insts.CoreOpsTry.branch, wasm.natural.from_u64]
  | Positive value =>
      have picked := pick_word_state 4294967297#u64 4294967296#u64
        (positiveCells value ++ rest) trace offset (work + (positiveCells value).length) (by decide)
      simp only [wasm.choices.natural, naturalCells, List.cons_append, List.length_cons,
        Nat.add_assoc] at picked ⊢
      simp only [shift, bind_tc_ok, add]
      simp [add, picked, core.result.Result.Insts.CoreOpsTry.branch]
      rw [positive_choice_replay]
      simp [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The constant payload domain is the original Nat, without a machine-integer premise. -/
theorem natural_literal_choice (n : Nat) (rest trace : List U64) (offset work : Nat) :
    wasm.choices.natural
      (replayState (naturalCells (naturalLiteral n) ++ rest) trace offset
        (work + (naturalCells (naturalLiteral n)).length)) =
      Result.ok (.Ok (naturalLiteral n,
        replayState rest ((naturalCells (naturalLiteral n)).reverse ++ trace)
          (offset + (naturalCells (naturalLiteral n)).length) work)) :=
  natural_choice_replay (naturalLiteral n) rest trace offset work

end RustWasm
