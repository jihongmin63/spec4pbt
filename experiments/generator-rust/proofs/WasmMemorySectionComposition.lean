import WasmMemoryImportRepresentation
import WasmDataSupport
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast SpecTecExecution

def memorySectionsCells (imports : List MemoryImport) (items : List Memory)
    (payloads : List String) : List U64 :=
  memoryImportSectionCells imports ++ memorySectionCells items ++ dataCells payloads

def memorySectionsConfig (imports : List MemoryImport) (items : List Memory)
    (payloads : List String) : wasm.Config :=
  { emptyConfig with
    max_memory_imports := naturalLiteral imports.length
    max_memories := naturalLiteral items.length
    max_datas := naturalLiteral payloads.length
    work_limit := naturalLiteral ((memorySectionsCells imports items payloads).length + 1) }

def memorySectionsOutput (imports : List MemoryImport) (items : List Memory)
    (payloads : List String) : wasm.ast.Module :=
  { emptyOutput with memory_imports := sequenceLiteral imports
                     memories := memoryList items
                     datas := dataLiteral payloads }

def memorySectionsFinal (imports : List MemoryImport) (items : List Memory)
    (payloads : List String) : wasm.choices.Choices :=
  replayState [] ((memorySectionsCells imports items payloads).reverse ++ [0#u64])
    ((memorySectionsCells imports items payloads).length + 1) 0

def memorySectionsModule (imports : List SpecTec.«import») (items : List SpecTec.memory)
    (payloads : List String) : SpecTec.module :=
  { emptyModule with IMPORTS := imports, MEMS := items, DATAS := payloads.map passiveDatum }

/-- The three arbitrary-length sections compose in the actual full Rust execution. -/
theorem memory_sections_replay (imports : List MemoryImport) (items : List Memory)
    (payloads : List String)
    (importBounds : ∀ item ∈ imports, MemoryBounded item.memory)
    (memoryBounds : ∀ item ∈ items, MemoryBounded item) :
    wasm.replay (memorySectionsConfig imports items payloads)
      (tapeFromCells (0#u64 :: memorySectionsCells imports items payloads)) =
      Result.ok (.Ok (memorySectionsOutput imports items payloads,
        memorySectionsFinal imports items payloads)) := by
  apply replay_from_build (memorySectionsConfig imports items payloads) _ _
    (memorySectionsFinal imports items payloads)
    (naturalLiteral ((memorySectionsCells imports items payloads).length + 1)) ?_ rfl
  let afterTypes := replayState (memorySectionsCells imports items payloads) [0#u64] 1
    (memorySectionsCells imports items payloads).length
  let afterImports := replayState (memorySectionCells items ++ dataCells payloads)
    ((memoryImportSectionCells imports).reverse ++ [0#u64])
    (1 + (memoryImportSectionCells imports).length)
    ((memorySectionCells items).length + (dataCells payloads).length)
  let afterMemories := replayState (dataCells payloads)
    ((memorySectionCells items).reverse ++ (memoryImportSectionCells imports).reverse ++ [0#u64])
    (1 + (memoryImportSectionCells imports).length + (memorySectionCells items).length)
    (dataCells payloads).length
  apply build_empty_types (memorySectionsConfig imports items payloads) _ afterTypes
    afterImports afterMemories (memorySectionsFinal imports items payloads)
    (sequenceLiteral imports) (memoryList items) (dataLiteral payloads)
  · exact generate_types_zero (memorySectionsConfig imports items payloads) rfl
      (memorySectionsCells imports items payloads) [] 0
      (memorySectionsCells imports items payloads).length
  · have generated := memory_import_section_replay imports importBounds
      (memorySectionCells items ++ dataCells payloads) [0#u64] 1
      ((memorySectionCells items).length + (dataCells payloads).length)
    simpa [memorySectionsConfig, memorySectionsCells, afterTypes, afterImports,
      List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using generated
  · have generated := memory_section_replay items memoryBounds (dataCells payloads)
      ((memoryImportSectionCells imports).reverse ++ [0#u64])
      (1 + (memoryImportSectionCells imports).length) (dataCells payloads).length
    simpa [memorySectionsConfig, afterImports, afterMemories, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using generated
  · have generated := data_section_replay payloads []
      ((memorySectionCells items).reverse ++ (memoryImportSectionCells imports).reverse ++ [0#u64])
      (1 + (memoryImportSectionCells imports).length + (memorySectionCells items).length) 0
    simpa [memorySectionsConfig, memorySectionsCells, memorySectionsFinal, afterMemories,
      List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using generated

theorem memory_sections_supported (imports : List MemoryImport) (items : List Memory)
    (payloads : List String)
    (importBounds : ∀ item ∈ imports, MemoryBounded item.memory)
    (memoryBounds : ∀ item ∈ items, MemoryBounded item) :
    ReplaySupport (memorySectionsConfig imports items payloads)
      (memorySectionsModule (imports.map memoryImport) (items.map memory) payloads) := by
  refine ⟨tapeFromCells (0#u64 :: memorySectionsCells imports items payloads),
    memorySectionsOutput imports items payloads,
    ⟨memorySectionsFinal imports items payloads,
      memory_sections_replay imports items payloads importBounds memoryBounds⟩, ?_⟩
  simp [embed, memorySectionsOutput, memorySectionsModule, emptyOutput, emptyModule,
    memoryOnly, memories_list, data_literal_embed, sequenceValues, sequenceLiteral]

syntax "memory_sections_spec_run" : tactic
macro_rules
| `(tactic| memory_sections_spec_run) => `(tactic|
  first
  | exact memory_imports_free_execute _ _
  | exact memories_free_execute _ _
  | exact passive_free_list_execute _ _
  | (apply memory_imports_execute; assumption)
  | (apply memories_bounded_execute; assumption)
  | exact passive_datas_execute _ _ _
  | exact Eval.pure _
  | exact Eval.unmatch
  | (apply Eval.guard_true; first | rfl | decide)
  | (apply Eval.guard_false; first | decide | exact of_decide_eq_true rfl)
  | (apply Eval.call; memory_sections_spec_run)
  | (apply Eval.bind_success; memory_sections_spec_run; memory_sections_spec_run)
  | (apply Eval.bind_unmatch; memory_sections_spec_run)
  | (apply Eval.orElse_success; memory_sections_spec_run)
  | (apply Eval.orElse_unmatch; memory_sections_spec_run; memory_sections_spec_run))

theorem memory_sections_valid (imports : List MemoryImport) (items : List Memory)
    (payloads : List String)
    (importBounds : ∀ item ∈ imports, MemoryBounded item.memory)
    (memoryBounds : ∀ item ∈ items, MemoryBounded item) :
    SpecTec.Module_ok
      (memorySectionsModule (imports.map memoryImport) (items.map memory) payloads) := by
  refine ⟨0, ?_⟩
  memory_sections_spec_run

/-- Composition preserves the original names, memory types and arbitrary String payloads. -/
theorem original_memory_sections_generated_valid (context : SpecTec.context)
    (imports : List SpecTec.«import») (items : List SpecTec.memory) (payloads : List String)
    (importTypes : ∀ item ∈ imports, MemoryImportValid context item)
    (memoryTypes : ∀ item ∈ items, SpecTec.Memtype_ok context item.MTYPE) :
    (∃ config, ReplaySupport config (memorySectionsModule imports items payloads)) ∧
      SpecTec.Module_ok (memorySectionsModule imports items payloads) := by
  obtain ⟨representedImports, importBounds, importsEqual⟩ :=
    original_memory_imports_representable context imports importTypes
  obtain ⟨representedMemories, memoryBounds, memoriesEqual⟩ :=
    original_memories_representable context items memoryTypes
  rw [←importsEqual, ←memoriesEqual]
  exact ⟨⟨memorySectionsConfig representedImports representedMemories payloads,
    memory_sections_supported representedImports representedMemories payloads importBounds memoryBounds⟩,
    memory_sections_valid representedImports representedMemories payloads importBounds memoryBounds⟩

open Lean Elab Command in
run_cmd do
  for declaration in [``memory_sections_replay, ``memory_sections_supported,
      ``memory_sections_valid, ``original_memory_sections_generated_valid] do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"

end RustWasm
