import WasmMemoryImportSupport
import WasmImportInversion
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace RustWasm
open Aeneas.Std generator_rust.wasm.ast

/-- An original-domain premise for the memory-import family, independent of Rust support. -/
def MemoryImportValid (context : SpecTec.context) (entry : SpecTec.«import») : Prop :=
  match entry.IDESC with
  | .MemImport type => SpecTec.Memtype_ok context type
  | _ => False

theorem memory_import_representable (context : SpecTec.context) (entry : SpecTec.«import»)
    (valid : MemoryImportValid context entry) :
    ∃ represented : MemoryImport,
      MemoryBounded represented.memory ∧ memoryImport represented = entry := by
  cases entry with
  | mk moduleName itemName descriptor =>
      cases descriptor with
      | MemImport type =>
          obtain ⟨item, bounded, exactType⟩ := (memtype_representable_iff context type).mp valid
          refine ⟨⟨nameLiteral moduleName, nameLiteral itemName, item⟩, bounded, ?_⟩
          simp [memoryImport, name_literal_roundtrip, exactType]
      | FuncImport _ => cases valid
      | GlobalImport _ => cases valid
      | TableImport _ => cases valid
      | TagImport _ => cases valid

theorem original_memory_imports_representable (context : SpecTec.context)
    (items : List SpecTec.«import»)
    (valid : ∀ item ∈ items, MemoryImportValid context item) :
    ∃ represented : List MemoryImport,
      (∀ item ∈ represented, MemoryBounded item.memory) ∧
      represented.map memoryImport = items := by
  induction items with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons head tail ih =>
      obtain ⟨first, firstBound, firstEqual⟩ := memory_import_representable context head
        (valid head (by simp))
      obtain ⟨rest, restBound, restEqual⟩ := ih (by
        intro item present
        exact valid item (by simp [present]))
      refine ⟨first :: rest, ?_, ?_⟩
      · intro item present
        rcases List.mem_cons.mp present with rfl | present
        · exact firstBound
        · exact restBound item present
      · simp [firstEqual, restEqual]

/-- Original arbitrary names/types are connected to the actual full replay and Module_ok. -/
theorem original_memory_imports_generated_valid (context : SpecTec.context)
    (items : List SpecTec.«import»)
    (valid : ∀ item ∈ items, MemoryImportValid context item) :
    (∃ config, ReplaySupport config { emptyModule with IMPORTS := items }) ∧
      SpecTec.Module_ok { emptyModule with IMPORTS := items } := by
  obtain ⟨represented, bounded, exactItems⟩ :=
    original_memory_imports_representable context items valid
  rw [←exactItems]
  exact ⟨⟨memoryImportListConfig represented, memory_import_list_supported represented bounded⟩,
    memory_import_list_valid represented bounded⟩

/-- Completeness of the import-only family starts from the unchanged original Module_ok. -/
theorem memory_imports_module_complete (items : List SpecTec.«import»)
    (descriptors : ∀ entry ∈ items, ∃ type, entry.IDESC = .MemImport type)
    (valid : SpecTec.Module_ok { emptyModule with IMPORTS := items }) :
    ∃ config, ReplaySupport config { emptyModule with IMPORTS := items } := by
  obtain ⟨source, output, start, finish, run⟩ := module_imports_execution _ valid
  have typed := imports_memory_types_valid source source output items start finish run
  apply (original_memory_imports_generated_valid source items ?_).1
  intro entry present
  obtain ⟨type, descriptor⟩ := descriptors entry present
  simpa [MemoryImportValid, descriptor] using typed entry present type descriptor

/-- The former missing-import counterexample receives an exact full replay witness. -/
theorem importsOnly_supported : ∃ config, ReplaySupport config importsOnly := by
  let item : MemoryImport := ⟨.Empty, .Empty, ⟨.I32, 0#u64, none⟩⟩
  have bounded : ∀ entry ∈ [item], MemoryBounded entry.memory := by
    simp [item, MemoryBounded, memoryPageLimit]
  refine ⟨memoryImportListConfig [item], ?_⟩
  simpa [importsOnly, memoryImport, item, memory, sequenceValues] using
    memory_import_list_supported [item] bounded

open Lean Elab Command in
run_cmd do
  for declaration in [``name_choice_replay, ``name_literal_roundtrip, ``name_literal_replay,
      ``memory_import_entry_replay, ``memory_import_section_replay,
      ``memory_import_free_execute, ``memory_imports_free_execute,
      ``memory_import_execute, ``memory_imports_execute, ``memory_import_list_valid,
      ``memory_import_list_replay, ``memory_import_list_supported, ``memory_import_list_generated_valid,
      ``memory_import_representable, ``original_memory_imports_representable,
      ``original_memory_imports_generated_valid, ``importsOnly_supported,
      ``memtype_valid_of_execution, ``import_memory_type_valid, ``imports_memory_types_valid,
      ``module_imports_execution, ``memory_imports_module_complete] do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"

end RustWasm
