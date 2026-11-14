import WasmSpecificationWitnesses

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas.Std generator_rust wasm.ast SpecTecExecution

def memoryPageLimit : AddressType → Nat
  | .I32 => 65536
  | .I64 => 281474976710656

def MemoryBounded (item : Memory) : Prop :=
  item.minimum.val ≤ memoryPageLimit item.address ∧
    ∀ maximum ∈ item.maximum,
      item.minimum.val ≤ maximum.val ∧ maximum.val ≤ memoryPageLimit item.address

/-- Successful original ordered limits validation, with unchanged fresh supply. -/
theorem memory_limits_valid (context : SpecTec.context) (limit minimum : Nat)
    (maximum : Option Nat) (supply : Nat)
    (bounded : minimum ≤ limit ∧ ∀ value ∈ maximum, minimum ≤ value ∧ value ≤ limit) :
    Eval SpecTec.Body (.call ⟨Unit, SpecTec.Call.Limits_ok context limit ⟨minimum, maximum⟩⟩)
      supply (.success (.of ())) supply := by
  apply Eval.call
  cases maximum with
  | none =>
    apply Eval.orElse_success
    apply Eval.bind_success
    · exact Eval.guard_true rfl
    · apply Eval.bind_success
      · exact Eval.guard_true bounded.1
      · exact Eval.pure ()
  | some value =>
    apply Eval.orElse_unmatch
    · apply Eval.bind_unmatch
      apply Eval.guard_false
      change ¬ false = true
      decide
    · apply Eval.orElse_success
      apply Eval.bind_success
      · exact Eval.guard_true rfl
      · apply Eval.bind_success
        · exact Eval.guard_true ⟨⟨bounded.1, (bounded.2 value rfl).2⟩, (bounded.2 value rfl).1⟩
        · exact Eval.pure ()

theorem memory_bounded_execute (context : SpecTec.context) (item : Memory)
    (bounded : MemoryBounded item) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨Unit, SpecTec.Call.Memtype_ok context (memory item).MTYPE⟩)
      supply (.success (.of ())) supply := by
  rcases item with ⟨address, minimum, maximum⟩
  have limits : ∀ supply, Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Limits_ok context (memoryPageLimit address)
        ⟨minimum.val, maximum.map (fun value => value.val)⟩⟩)
      supply (.success (.of ())) supply := by
    intro supply
    apply memory_limits_valid
    refine ⟨bounded.1, ?_⟩
    intro value present
    cases maximum with
    | none => simp at present
    | some original =>
      simp at present
      subst value
      exact bounded.2 original rfl
  apply Eval.call
  cases address with
  | I32 =>
    apply Eval.orElse_success
    apply Eval.bind_success
    · exact Eval.guard_true rfl
    · apply Eval.bind_success
      · exact limits supply
      · exact Eval.pure ()
  | I64 =>
    apply Eval.orElse_unmatch
    · apply Eval.bind_unmatch
      apply Eval.guard_false
      change ¬ false = true
      decide
    · apply Eval.orElse_success
      apply Eval.bind_success
      · exact Eval.guard_true rfl
      · apply Eval.bind_success
        · exact limits supply
        · exact Eval.pure ()

theorem memory_bounded_valid (context : SpecTec.context) (item : Memory)
    (bounded : MemoryBounded item) : SpecTec.Memtype_ok context (memory item).MTYPE :=
  ⟨0, memory_bounded_execute context item bounded 0⟩

def memoryList : List Memory → Memories
  | [] => .Empty
  | head :: tail => .Cons head (memoryList tail)

/-- Recursive Rust section values represent every finite memory list, without a Vec cap.
This is a representation lemma, not a replay-support claim. -/
theorem memories_list (items : List Memory) :
    memories (memoryList items) = items.map memory := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp [memoryList, memories, ih]

/-- The original ordered section rules accept every pointwise bounded list. -/
theorem memories_bounded_execute (context : SpecTec.context) (items : List Memory)
    (bounded : ∀ item ∈ items, MemoryBounded item) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨SpecTec.context, SpecTec.Call.Mems_ok context (items.map memory)⟩)
      supply (.success (.of { context with
        MEMS := context.MEMS ++ items.map (fun item => (memory item).MTYPE) })) supply := by
  induction items generalizing context with
  | nil =>
      simp only [List.map_nil, List.append_nil]
      apply Eval.call
      apply Eval.orElse_unmatch
      · apply Eval.bind_unmatch
        exact Eval.guard_false (by decide)
      · apply Eval.orElse_success
        apply Eval.bind_success
        · exact Eval.guard_true rfl
        · exact Eval.pure context
  | cons head tail ih =>
      have headBound := bounded head (by simp)
      have tailBound : ∀ item ∈ tail, MemoryBounded item := by
        intro item present
        exact bounded item (by simp [present])
      apply Eval.call
      apply Eval.orElse_success
      apply Eval.bind_success
      · apply Eval.guard_true
        simp
      · apply Eval.bind_success
        · apply Eval.call
          apply Eval.orElse_success
          apply Eval.bind_success
          · exact memory_bounded_execute context head headBound supply
          · exact Eval.pure _
        · apply Eval.bind_success
          · exact ih { context with MEMS := context.MEMS ++ [(memory head).MTYPE] } tailBound
          · simp only [List.map_cons, List.append_assoc, List.singleton_append]
            exact Eval.pure _

end RustWasm
