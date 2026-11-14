import WasmMemorySupport

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

namespace RustWasm
open SpecTecExecution generator_rust.wasm.ast

def memoryFree : SpecTec.free :=
  ⟨.«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» [],
    .«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» []⟩

theorem memory_free_execute (item : Memory) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨SpecTec.free, SpecTec.Call.«$free_mem» (memory item)⟩)
      supply (.success (.of memoryFree)) supply := by
  spec_run

theorem memories_free_execute (items : List Memory) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨SpecTec.free,
      SpecTec.Call.«$free_list» SpecTec.memory SpecTec.Call.«$free_mem» (items.map memory)⟩)
      supply (.success (.of memoryFree)) supply := by
  induction items with
  | nil => spec_run
  | cons head tail ih =>
      apply Eval.call
      apply Eval.orElse_unmatch
      · apply Eval.bind_unmatch
        apply Eval.guard_false
        simp
      · apply Eval.orElse_success
        apply Eval.bind_success
        · apply Eval.guard_true
          simp
        · apply Eval.bind_success
          · exact memory_free_execute head supply
          · apply Eval.bind_success
            · exact ih
            · spec_run

/- Extend the concrete ordered-rule tactic with the two list induction lemmas. -/
syntax "memory_spec_run" : tactic
macro_rules
| `(tactic| memory_spec_run) => `(tactic|
  first
  | exact memories_free_execute _ _
  | (apply memories_bounded_execute; assumption)
  | exact Eval.pure _
  | exact Eval.unmatch
  | (apply Eval.guard_true; first | rfl | decide)
  | (apply Eval.guard_false; change ¬ false = true; decide)
  | (apply Eval.call; memory_spec_run)
  | (apply Eval.bind_success; memory_spec_run; memory_spec_run)
  | (apply Eval.bind_unmatch; memory_spec_run)
  | (apply Eval.orElse_success; memory_spec_run)
  | (apply Eval.orElse_unmatch; memory_spec_run; memory_spec_run))

theorem memory_list_valid (items : List Memory)
    (bounded : ∀ item ∈ items, MemoryBounded item) :
    SpecTec.Module_ok { emptyModule with MEMS := items.map memory } := by
  refine ⟨0, ?_⟩
  memory_spec_run

/-- Arbitrary finite memory lists have both actual replay witnesses and original validity. -/
theorem memory_list_generated_valid (items : List Memory)
    (bounded : ∀ item ∈ items, MemoryBounded item) :
    (∃ config, ReplaySupport config { emptyModule with MEMS := items.map memory }) ∧
      SpecTec.Module_ok { emptyModule with MEMS := items.map memory } :=
  ⟨⟨memoryListConfig items, memory_list_supported items bounded⟩, memory_list_valid items bounded⟩

end RustWasm
