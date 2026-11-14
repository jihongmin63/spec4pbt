import WasmReplaySteps
import WasmMemoryProperties

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

def memoryWidth : AddressType → U64
  | .I32 => 0#u64
  | .I64 => 1#u64

def memoryLimit : AddressType → U64
  | .I32 => 65536#u64
  | .I64 => 281474976710656#u64

def memoryLimitSucc : AddressType → U64
  | .I32 => 65537#u64
  | .I64 => 281474976710657#u64

def memoryExtra (minimum maximum : U64) : U64 :=
  UScalar.ofNatCore (maximum.val - minimum.val) (lt_of_le_of_lt (Nat.sub_le _ _) maximum.hBounds)

def memorySlack (address : AddressType) (minimum : U64) : U64 :=
  UScalar.ofNatCore (memoryPageLimit address - minimum.val) (by
    have bounded := Nat.sub_le (memoryPageLimit address) minimum.val
    cases address <;> simp only [memoryPageLimit] at bounded ⊢ <;> scalar_tac)

def memorySlackSucc (address : AddressType) (minimum : U64) : U64 :=
  UScalar.ofNatCore (memoryPageLimit address - minimum.val + 1) (by
    have bounded := Nat.sub_le (memoryPageLimit address) minimum.val
    cases address <;> simp only [memoryPageLimit] at bounded ⊢ <;> scalar_tac)

theorem add_u64_exact (left right result : U64) (value : result.val = left.val + right.val) :
    left + right = Result.ok result := by
  apply wp_eq_ok
  step* <;> scalar_tac

theorem sub_u64_exact (left right result : U64) (ordered : right.val ≤ left.val)
    (value : result.val = left.val - right.val) : left - right = Result.ok result := by
  apply wp_eq_ok
  step* <;> scalar_tac

theorem memory_limit_add (address : AddressType) :
    memoryLimit address + 1#u64 = Result.ok (memoryLimitSucc address) := by
  apply add_u64_exact
  cases address <;> rfl

theorem memory_none_replay (address : AddressType) (minimum : U64)
    (bounded : minimum.val ≤ memoryPageLimit address)
    (rest trace : List U64) (offset work : Nat) :
    wasm.memory.memory
      (replayState (memoryWidth address :: minimum :: 0#u64 :: rest) trace offset (work + 3)) =
      Result.ok (.Ok (⟨address, minimum, none⟩,
        replayState rest (0#u64 :: minimum :: memoryWidth address :: trace) (offset + 3) work)) := by
  have widthRun := pick_word_state 2#u64 (memoryWidth address) (minimum :: 0#u64 :: rest)
    trace offset (work + 2) (by cases address <;> decide)
  have minRange : minimum.val < (memoryLimitSucc address).val := by
    cases address <;> simp only [memoryPageLimit, memoryLimitSucc] at bounded ⊢ <;> scalar_tac
  have minRun := pick_word_state (memoryLimitSucc address) minimum (0#u64 :: rest)
    (memoryWidth address :: trace) (offset + 1) (work + 1) minRange
  have flagRun := pick_word_state 2#u64 0#u64 rest
    (minimum :: memoryWidth address :: trace) (offset + 2) work (by decide)
  have add := memory_limit_add address
  cases address <;>
    simp [wasm.memory.memory, memoryWidth, memoryLimit, memoryLimitSucc,
      core.result.Result.Insts.CoreOpsTry.branch, Nat.add_assoc] at widthRun minRun flagRun add ⊢
  all_goals
    rw [widthRun]
    simp
    rw [add]
    simp
    rw [minRun]
    simp
    rw [flagRun]
    simp

theorem memory_some_replay (address : AddressType) (minimum maximum : U64)
    (ordered : minimum.val ≤ maximum.val) (bounded : maximum.val ≤ memoryPageLimit address)
    (rest trace : List U64) (offset work : Nat) :
    wasm.memory.memory
      (replayState (memoryWidth address :: minimum :: 1#u64 :: memoryExtra minimum maximum :: rest)
        trace offset (work + 4)) =
      Result.ok (.Ok (⟨address, minimum, some maximum⟩,
        replayState rest (memoryExtra minimum maximum :: 1#u64 :: minimum :: memoryWidth address :: trace)
          (offset + 4) work)) := by
  have minBound : minimum.val ≤ memoryPageLimit address := Nat.le_trans ordered bounded
  have widthRun := pick_word_state 2#u64 (memoryWidth address)
    (minimum :: 1#u64 :: memoryExtra minimum maximum :: rest) trace offset (work + 3)
    (by cases address <;> decide)
  have minRange : minimum.val < (memoryLimitSucc address).val := by
    cases address <;> simp only [memoryPageLimit, memoryLimitSucc] at minBound ⊢ <;> scalar_tac
  have minRun := pick_word_state (memoryLimitSucc address) minimum
    (1#u64 :: memoryExtra minimum maximum :: rest) (memoryWidth address :: trace)
    (offset + 1) (work + 2) minRange
  have flagRun := pick_word_state 2#u64 1#u64 (memoryExtra minimum maximum :: rest)
    (minimum :: memoryWidth address :: trace) (offset + 2) (work + 1) (by decide)
  have extraRange : (memoryExtra minimum maximum).val < (memorySlackSucc address minimum).val := by
    simp only [memoryExtra, memorySlackSucc, UScalar.ofNatCore_val_eq]
    omega
  have extraRun := pick_word_state (memorySlackSucc address minimum) (memoryExtra minimum maximum) rest
    (1#u64 :: minimum :: memoryWidth address :: trace) (offset + 3) work extraRange
  have add := memory_limit_add address
  have sub : memoryLimit address - minimum = Result.ok (memorySlack address minimum) := by
    apply sub_u64_exact
    · cases address <;> exact minBound
    · cases address <;> rfl
  have slackAdd : memorySlack address minimum + 1#u64 = Result.ok (memorySlackSucc address minimum) := by
    apply add_u64_exact
    rfl
  have resultAdd : minimum + memoryExtra minimum maximum = Result.ok maximum := by
    apply add_u64_exact
    simp only [memoryExtra, UScalar.ofNatCore_val_eq]
    omega
  cases address <;>
    simp [wasm.memory.memory, memoryWidth, memoryLimit, memoryLimitSucc,
      core.result.Result.Insts.CoreOpsTry.branch, Nat.add_assoc] at widthRun minRun flagRun extraRun add sub ⊢
  all_goals
    rw [widthRun]
    simp
    rw [add]
    simp
    rw [minRun]
    simp
    rw [flagRun]
    simp
  all_goals
    rw [sub]
    simp
    rw [slackAdd]
    simp
    rw [extraRun]
    simp [resultAdd]

end RustWasm
