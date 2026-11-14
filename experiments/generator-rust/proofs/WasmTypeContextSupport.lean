import WasmTypeContextReplay
import WasmTypeContextSpecification
import WasmContract
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace RustWasm
open Aeneas.Std

theorem recursive_parent_embed : embed recursiveParentOutput = recursiveParentModule := by
  simp [recursiveParentOutput, contextOutput, contextRef, contextVoidGroup, contextVoid,
    recursiveParentModule, typeContextEmptyModule, typeContextIndexedRef, typeContextVoidType,
    embed, recursiveGroup, subtype, sequenceValues, sequenceLiteral, valueType,
    function, instructionSequence, instruction, exportEntry, memories, datas] <;> rfl

theorem recursive_parent_supported : ReplaySupport recursiveParentConfig recursiveParentModule := by
  exact ⟨tapeFromCells recursiveParentCells, recursiveParentOutput,
    ⟨contextFinal recursiveParentCells, recursive_parent_replay⟩, recursive_parent_embed⟩

theorem recursive_parent_generated_valid :
    ReplaySupport recursiveParentConfig recursiveParentModule ∧ SpecTec.Module_ok recursiveParentModule :=
  ⟨recursive_parent_supported, recursive_parent_module_ok⟩

theorem mutual_group_embed : embed mutualGroupOutput = mutualGroupModule := by
  simp [mutualGroupOutput, contextOutput, contextRef, contextVoidGroup, contextVoid,
    mutualGroupModule, typeContextEmptyModule, typeContextIndexedRef, typeContextVoidType,
    embed, recursiveGroup, subtype, sequenceValues, sequenceLiteral, valueType,
    function, instructionSequence, instruction, exportEntry, memories, datas] <;> rfl

theorem mutual_group_supported : ReplaySupport mutualGroupConfig mutualGroupModule := by
  exact ⟨tapeFromCells mutualGroupCells, mutualGroupOutput,
    ⟨contextFinal mutualGroupCells, mutual_group_replay⟩, mutual_group_embed⟩

theorem mutual_group_generated_valid :
    ReplaySupport mutualGroupConfig mutualGroupModule ∧ SpecTec.Module_ok mutualGroupModule :=
  ⟨mutual_group_supported, mutual_group_module_ok⟩

theorem raw_alias_embed : embed rawAliasOutput = rawAliasModule := by
  simp [rawAliasOutput, contextOutput, contextRef, contextVoidGroup, contextVoid,
    rawAliasModule, typeContextEmptyModule, typeContextIndexedRef, typeContextVoidType,
    embed, recursiveGroup, subtype, sequenceValues, sequenceLiteral, valueType,
    function, instructionSequence, instruction, exportEntry, memories, datas] <;> rfl

theorem raw_alias_supported : ReplaySupport rawAliasConfig rawAliasModule := by
  exact ⟨tapeFromCells rawAliasCells, rawAliasOutput,
    ⟨contextFinal rawAliasCells, raw_alias_replay⟩, raw_alias_embed⟩

theorem raw_alias_generated_valid :
    ReplaySupport rawAliasConfig rawAliasModule ∧ SpecTec.Module_ok rawAliasModule :=
  ⟨raw_alias_supported, raw_alias_module_ok⟩

theorem exported_ref_embed : embed exportedRefOutput = exportedRefModule := by
  simp [exportedRefOutput, contextOutput, contextRef, contextVoidGroup, contextVoid,
    exportedRefModule, typeContextEmptyModule, typeContextIndexedRef, typeContextVoidType,
    embed, recursiveGroup, subtype, sequenceValues, sequenceLiteral, valueType,
    function, instructionSequence, instruction, exportEntry, memories, datas] <;> rfl

theorem exported_ref_supported : ReplaySupport exportedRefConfig exportedRefModule := by
  exact ⟨tapeFromCells exportedRefCells, exportedRefOutput,
    ⟨contextFinal exportedRefCells, exported_ref_replay⟩, exported_ref_embed⟩

theorem exported_ref_generated_valid :
    ReplaySupport exportedRefConfig exportedRefModule ∧ SpecTec.Module_ok exportedRefModule :=
  ⟨exported_ref_supported, exported_ref_module_ok⟩

end RustWasm

open Lean Elab Command

run_cmd do
  let declarations := [
    ``RustWasm.recursive_parent_replay,
    ``RustWasm.recursive_parent_embed,
    ``RustWasm.recursive_parent_module_ok,
    ``RustWasm.recursive_parent_supported,
    ``RustWasm.recursive_parent_generated_valid,
    ``RustWasm.mutual_group_replay,
    ``RustWasm.mutual_group_embed,
    ``RustWasm.mutual_group_module_ok,
    ``RustWasm.mutual_group_supported,
    ``RustWasm.mutual_group_generated_valid,
    ``RustWasm.raw_alias_replay,
    ``RustWasm.raw_alias_embed,
    ``RustWasm.raw_alias_module_ok,
    ``RustWasm.raw_alias_supported,
    ``RustWasm.raw_alias_generated_valid,
    ``RustWasm.exported_ref_replay,
    ``RustWasm.exported_ref_embed,
    ``RustWasm.exported_ref_module_ok,
    ``RustWasm.exported_ref_supported,
    ``RustWasm.exported_ref_generated_valid,
    ``RustWasm.closed_shared_aliases_match,
    ``RustWasm.closed_dangling_reference_rejected,
    ``RustWasm.closed_later_dangling_reference_rejected]
  for declaration in declarations do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"
