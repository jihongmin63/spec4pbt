import WasmControlReplay
import WasmControlSpecification
import WasmContract
import WasmNaturalEncoding
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace RustWasm
open Aeneas.Std

theorem unreachable_add_embed : embed unreachableAddOutput = unreachableAddModule := by
  simp [unreachableAddOutput, controlOutput, unreachableAddModule, controlModule, embed,
    sequenceValues, sequenceLiteral, recursiveGroup, subtype, valueType, function, instructionSequence,
    instruction, blockType, binaryOp, memories, datas] <;> rfl


theorem unreachable_add_supported : ReplaySupport unreachableAddConfig unreachableAddModule := by
  exact ⟨tapeFromCells unreachableAddCells, unreachableAddOutput,
    ⟨controlFinal unreachableAddCells, unreachable_add_replay⟩, unreachable_add_embed⟩

theorem unreachable_add_generated_valid :
    ReplaySupport unreachableAddConfig unreachableAddModule ∧ SpecTec.Module_ok unreachableAddModule :=
  ⟨unreachable_add_supported, unreachable_add_module_ok⟩

theorem unreachable_operand_embed : embed unreachableOperandOutput = unreachableOperandModule := by
  simp [unreachableOperandOutput, controlOutput, unreachableOperandModule, controlModule, embed,
    sequenceValues, sequenceLiteral, recursiveGroup, subtype, valueType, function, instructionSequence,
    instruction, blockType, binaryOp, memories, datas] <;> rfl


theorem unreachable_operand_supported : ReplaySupport unreachableOperandConfig unreachableOperandModule := by
  exact ⟨tapeFromCells unreachableOperandCells, unreachableOperandOutput,
    ⟨controlFinal unreachableOperandCells, unreachable_operand_replay⟩, unreachable_operand_embed⟩

theorem unreachable_operand_generated_valid :
    ReplaySupport unreachableOperandConfig unreachableOperandModule ∧ SpecTec.Module_ok unreachableOperandModule :=
  ⟨unreachable_operand_supported, unreachable_operand_module_ok⟩

theorem unreachable_predecessor_embed : embed unreachablePredecessorOutput = unreachablePredecessorModule := by
  simp [unreachablePredecessorOutput, controlOutput, unreachablePredecessorModule, controlModule, embed,
    sequenceValues, sequenceLiteral, recursiveGroup, subtype, valueType, function, instructionSequence,
    instruction, blockType, binaryOp, memories, datas] <;> rfl


theorem unreachable_predecessor_supported : ReplaySupport unreachablePredecessorConfig unreachablePredecessorModule := by
  exact ⟨tapeFromCells unreachablePredecessorCells, unreachablePredecessorOutput,
    ⟨controlFinal unreachablePredecessorCells, unreachable_predecessor_replay⟩, unreachable_predecessor_embed⟩

theorem unreachable_predecessor_generated_valid :
    ReplaySupport unreachablePredecessorConfig unreachablePredecessorModule ∧ SpecTec.Module_ok unreachablePredecessorModule :=
  ⟨unreachable_predecessor_supported, unreachable_predecessor_module_ok⟩

theorem loop_label_embed : embed loopLabelOutput = loopLabelModule := by
  simp [loopLabelOutput, controlOutput, loopLabelModule, controlModule, embed,
    sequenceValues, sequenceLiteral, recursiveGroup, subtype, valueType, function, instructionSequence,
    instruction, blockType, binaryOp, memories, datas] <;> rfl


theorem loop_label_supported : ReplaySupport loopLabelConfig loopLabelModule := by
  exact ⟨tapeFromCells loopLabelCells, loopLabelOutput,
    ⟨controlFinal loopLabelCells, loop_label_replay⟩, loop_label_embed⟩

theorem loop_label_generated_valid :
    ReplaySupport loopLabelConfig loopLabelModule ∧ SpecTec.Module_ok loopLabelModule :=
  ⟨loop_label_supported, loop_label_module_ok⟩

theorem outer_label_embed : embed outerLabelOutput = outerLabelModule := by
  simp [outerLabelOutput, controlOutput, outerLabelModule, controlModule, embed,
    sequenceValues, sequenceLiteral, recursiveGroup, subtype, valueType, function, instructionSequence,
    instruction, blockType, binaryOp, memories, datas] <;> rfl


theorem outer_label_supported : ReplaySupport outerLabelConfig outerLabelModule := by
  exact ⟨tapeFromCells outerLabelCells, outerLabelOutput,
    ⟨controlFinal outerLabelCells, outer_label_replay⟩, outer_label_embed⟩

theorem outer_label_generated_valid :
    ReplaySupport outerLabelConfig outerLabelModule ∧ SpecTec.Module_ok outerLabelModule :=
  ⟨outer_label_supported, outer_label_module_ok⟩

theorem branch_if_embed : embed branchIfOutput = branchIfModule := by
  simp [branchIfOutput, controlOutput, branchIfModule, controlModule, embed,
    sequenceValues, sequenceLiteral, recursiveGroup, subtype, valueType, function, instructionSequence,
    instruction, blockType, binaryOp, memories, datas] <;> rfl


theorem branch_if_supported : ReplaySupport branchIfConfig branchIfModule := by
  exact ⟨tapeFromCells branchIfCells, branchIfOutput,
    ⟨controlFinal branchIfCells, branch_if_replay⟩, branch_if_embed⟩

theorem branch_if_generated_valid :
    ReplaySupport branchIfConfig branchIfModule ∧ SpecTec.Module_ok branchIfModule :=
  ⟨branch_if_supported, branch_if_module_ok⟩

end RustWasm

open Lean Elab Command

run_cmd do
  let declarations := [
    ``RustWasm.unreachable_add_replay,
    ``RustWasm.unreachable_add_embed,
    ``RustWasm.unreachable_add_module_ok,
    ``RustWasm.unreachable_add_supported,
    ``RustWasm.unreachable_add_generated_valid,
    ``RustWasm.unreachable_operand_replay,
    ``RustWasm.unreachable_operand_embed,
    ``RustWasm.unreachable_operand_module_ok,
    ``RustWasm.unreachable_operand_supported,
    ``RustWasm.unreachable_operand_generated_valid,
    ``RustWasm.unreachable_predecessor_replay,
    ``RustWasm.unreachable_predecessor_embed,
    ``RustWasm.unreachable_predecessor_module_ok,
    ``RustWasm.unreachable_predecessor_supported,
    ``RustWasm.unreachable_predecessor_generated_valid,
    ``RustWasm.loop_label_replay,
    ``RustWasm.loop_label_embed,
    ``RustWasm.loop_label_module_ok,
    ``RustWasm.loop_label_supported,
    ``RustWasm.loop_label_generated_valid,
    ``RustWasm.outer_label_replay,
    ``RustWasm.outer_label_embed,
    ``RustWasm.outer_label_module_ok,
    ``RustWasm.outer_label_supported,
    ``RustWasm.outer_label_generated_valid,
    ``RustWasm.branch_if_replay,
    ``RustWasm.branch_if_embed,
    ``RustWasm.branch_if_module_ok,
    ``RustWasm.branch_if_supported,
    ``RustWasm.branch_if_generated_valid]
  for declaration in declarations do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"
