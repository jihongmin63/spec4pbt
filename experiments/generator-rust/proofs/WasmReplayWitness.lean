import WasmSpecificationWitnesses
import WasmModulePrimitives

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust

def emptyConfig : wasm.Config :=
  ⟨.Zero, .Zero, .Zero, .Zero, .Zero, .Zero, .Zero, .Zero, .Zero, .Zero, naturalLiteral 1⟩
def emptyTape : wasm.choices.Tape := .Cons 0#u64 .Empty
def emptyOutput : wasm.ast.Module :=
  ⟨.Empty, .Empty, .Empty, none, .Empty, .Empty, .Empty⟩
def emptyFinal : wasm.choices.Choices :=
  ⟨.Replay .Empty (naturalLiteral 1), emptyTape, .Zero⟩

theorem generate_types_empty : wasm.types.generate emptyConfig
    ⟨.Replay emptyTape .Zero, .Empty, naturalLiteral 1⟩ =
      Result.ok (.Ok (.Empty, .Empty, emptyFinal)) := by
  simpa [replayState, emptyConfig, emptyTape, emptyFinal, tapeFromCells, naturalLiteral] using
    generate_types_zero emptyConfig rfl [] [] 0 0

theorem empty_replay : wasm.replay emptyConfig emptyTape =
    Result.ok (.Ok (emptyOutput, emptyFinal)) := by
  apply replay_from_build emptyConfig emptyTape emptyOutput emptyFinal (naturalLiteral 1) ?_ rfl
  apply build_empty_types emptyConfig _ emptyFinal emptyFinal emptyFinal emptyFinal .Empty .Empty .Empty
  · exact generate_types_empty
  · rw [wasm.memory_import.generate]
    simp [emptyConfig, wasm.natural.decrement]
  · rw [wasm.memory.generate]
    simp [emptyConfig, wasm.natural.decrement]
  · rw [wasm.data.generate]
    simp [emptyConfig, wasm.natural.decrement]

/-- A kernel-checked successful execution of the translated entry point. -/
theorem empty_supported : ReplaySupport emptyConfig emptyModule := by
  refine ⟨emptyTape, emptyOutput, ⟨emptyFinal, empty_replay⟩, ?_⟩
  rfl

/-- One real execution/embedding/specification chain, not universal soundness. -/
theorem empty_generated_valid :
    ReplaySupport emptyConfig emptyModule ∧ SpecTec.Module_ok emptyModule :=
  ⟨empty_supported, emptyModule_ok⟩

end RustWasm
