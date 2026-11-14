import WasmConstantReplay
import WasmConstantSpecification
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace RustWasm
open Aeneas.Std generator_rust

/-- Exact structural embedding; the requested instruction is neither normalized nor extended. -/
theorem constant_embed (n : Nat) :
    embed (constantOutput (naturalLiteral n)) = constantModule n := by
  simp [embed, constantOutput, constantSignature, constantGroup, integerConstantOutput,
    integerConstantSignature, integerConstantGroup, integerConstantInstruction, integerValue, sequenceValues, sequenceLiteral,
    recursiveGroup, subtype, valueType, function, instructionSequence, instruction,
    memories, datas, constantModule, emptyModule, memoryOnly] <;> rfl


/-- Full Rust replay support for every original-spec natural i32 constant. -/
theorem constant_supported (n : Nat) :
    ReplaySupport (constantConfig (naturalLiteral n)) (constantModule n) := by
  refine ⟨tapeFromCells (constantCells (naturalLiteral n)), constantOutput (naturalLiteral n),
    ⟨constantFinal (naturalLiteral n), constant_replay (naturalLiteral n)⟩, constant_embed n⟩

/-- A universal family of actual executions and original Module_ok proofs, not full completeness. -/
theorem constant_generated_valid (n : Nat) :
    ReplaySupport (constantConfig (naturalLiteral n)) (constantModule n) ∧
      SpecTec.Module_ok (constantModule n) :=
  ⟨constant_supported n, constant_module_ok n⟩

/-- The i64 instruction carries exactly the requested natural, without truncation. -/
theorem constant64_embed (n : Nat) :
    embed (integerConstantOutput .I64 (naturalLiteral n)) = constant64Module n := by
  simp [embed, integerConstantOutput, integerConstantSignature, integerConstantGroup,
    integerConstantInstruction, integerValue, sequenceValues, sequenceLiteral,
    recursiveGroup, subtype, valueType, function, instructionSequence, instruction,
    memories, datas, constant64Module, emptyModule, memoryOnly] <;> rfl

theorem constant64_supported (n : Nat) :
    ReplaySupport (constantConfig (naturalLiteral n)) (constant64Module n) := by
  refine ⟨tapeFromCells (integerConstantCells .I64 (naturalLiteral n)),
    integerConstantOutput .I64 (naturalLiteral n),
    ⟨integerConstantFinal .I64 (naturalLiteral n), constant64_replay (naturalLiteral n)⟩,
    constant64_embed n⟩

theorem constant64_generated_valid (n : Nat) :
    ReplaySupport (constantConfig (naturalLiteral n)) (constant64Module n) ∧
      SpecTec.Module_ok (constant64Module n) :=
  ⟨constant64_supported n, constant64_module_ok n⟩

end RustWasm

open Lean Elab Command
run_cmd do
  for declaration in [``RustWasm.positive_choice_replay, ``RustWasm.natural_choice_replay,
      ``RustWasm.natural_literal_choice, ``RustWasm.constant_replay, ``RustWasm.constant_embed,
      ``RustWasm.constant_supported, ``RustWasm.constant_module_ok,
      ``RustWasm.constant_generated_valid, ``RustWasm.integer_constant_replay,
      ``RustWasm.constant64_replay, ``RustWasm.constant64_embed,
      ``RustWasm.constant64_supported, ``RustWasm.constant64_module_ok,
      ``RustWasm.constant64_generated_valid] do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"
