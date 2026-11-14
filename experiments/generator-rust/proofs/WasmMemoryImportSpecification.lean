import WasmMemoryRepresentation

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

namespace RustWasm
open SpecTecExecution generator_rust.wasm.ast

/-- A memory descriptor and its two names contribute no free indices. -/
theorem memory_import_free_execute (entry : MemoryImport) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨SpecTec.free, SpecTec.Call.«$free_import» (memoryImport entry)⟩)
      supply (.success (.of memoryFree)) supply := by
  memory_spec_run

theorem memory_imports_free_execute (items : List MemoryImport) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨SpecTec.free,
      SpecTec.Call.«$free_list» SpecTec.«import» SpecTec.Call.«$free_import»
        (items.map memoryImport)⟩)
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
          · exact memory_import_free_execute head supply
          · apply Eval.bind_success
            · exact ih
            · spec_run

/-- A memory import changes only the memory context; names are unconstrained. -/
theorem memory_import_execute (context : SpecTec.context) (entry : MemoryImport)
    (bounded : MemoryBounded entry.memory) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨SpecTec.context,
      SpecTec.Call.Import_ok context (memoryImport entry)⟩)
      supply (.success (.of { context with
        MEMS := context.MEMS ++ [(memory entry.memory).MTYPE] })) supply := by
  apply Eval.call
  apply Eval.orElse_unmatch
  · apply Eval.bind_unmatch
    exact Eval.guard_false (by change ¬ false = true; decide)
  · apply Eval.orElse_unmatch
    · apply Eval.bind_unmatch
      exact Eval.guard_false (by change ¬ false = true; decide)
    · apply Eval.orElse_unmatch
      · apply Eval.bind_unmatch
        exact Eval.guard_false (by change ¬ false = true; decide)
      · apply Eval.orElse_success
        apply Eval.bind_success
        · exact Eval.guard_true rfl
        · apply Eval.bind_success
          · exact memory_bounded_execute context entry.memory bounded supply
          · exact Eval.pure _

/-- Import order and duplicates are preserved in the original memory index space. -/
theorem memory_imports_execute (context : SpecTec.context) (items : List MemoryImport)
    (bounded : ∀ item ∈ items, MemoryBounded item.memory) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨SpecTec.context,
      SpecTec.Call.Imports_ok context (items.map memoryImport)⟩)
      supply (.success (.of { context with
        MEMS := context.MEMS ++ items.map (fun item : MemoryImport => (memory item.memory).MTYPE) })) supply := by
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
      have tailBound : ∀ item ∈ tail, MemoryBounded item.memory := by
        intro item present
        exact bounded item (by simp [present])
      apply Eval.call
      apply Eval.orElse_success
      apply Eval.bind_success
      · apply Eval.guard_true
        simp
      · apply Eval.bind_success
        · exact memory_import_execute context head headBound supply
        · apply Eval.bind_success
          · exact ih { context with MEMS := context.MEMS ++ [(memory head.memory).MTYPE] } tailBound
          · simp only [List.map_cons, List.append_assoc, List.singleton_append]
            exact Eval.pure _

syntax "memory_import_spec_run" : tactic
macro_rules
| `(tactic| memory_import_spec_run) => `(tactic|
  first
  | exact memory_imports_free_execute _ _
  | (apply memory_imports_execute; assumption)
  | exact Eval.pure _
  | exact Eval.unmatch
  | (apply Eval.guard_true; first | rfl | decide)
  | (apply Eval.guard_false; change ¬ false = true; decide)
  | (apply Eval.call; memory_import_spec_run)
  | (apply Eval.bind_success; memory_import_spec_run; memory_import_spec_run)
  | (apply Eval.bind_unmatch; memory_import_spec_run)
  | (apply Eval.orElse_success; memory_import_spec_run)
  | (apply Eval.orElse_unmatch; memory_import_spec_run; memory_import_spec_run))

theorem memory_import_list_valid (items : List MemoryImport)
    (bounded : ∀ item ∈ items, MemoryBounded item.memory) :
    SpecTec.Module_ok { emptyModule with IMPORTS := items.map memoryImport } := by
  refine ⟨0, ?_⟩
  memory_import_spec_run

end RustWasm
