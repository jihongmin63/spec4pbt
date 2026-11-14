import WasmMemorySoundness
import WasmMemoryImportSpecification
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace RustWasm
open Aeneas.Std generator_rust wasm.ast

private theorem result_bind_success {α β : Type} (first : Result α) (next : α → Result β)
    (output : β) (success : Aeneas.Std.bind first next = Result.ok output) :
    ∃ intermediate, first = Result.ok intermediate ∧ next intermediate = Result.ok output := by
  cases first with
  | ret intermediate => exact ⟨intermediate, rfl, by simpa using success⟩
  | vis effect continuation => simp at success
  | div => simp at success

/-- Invert a successful Rust result bind whose error arm preserves the error. -/
private theorem generation_bind_success {α β : Type}
    (first : Result (core.result.Result α wasm.choices.GenerationError))
    (next : core.result.Result α wasm.choices.GenerationError →
      Result (core.result.Result β wasm.choices.GenerationError)) (output : β)
    (success : Aeneas.Std.bind first next = Result.ok (.Ok output))
    (errorRun : ∀ error, next (.Err error) = Result.ok (.Err error)) :
    ∃ value, first = Result.ok (.Ok value) ∧ next (.Ok value) = Result.ok (.Ok output) := by
  obtain ⟨result, firstRun, tail⟩ := result_bind_success first next (.Ok output) success
  cases result with
  | Ok value => exact ⟨value, firstRun, tail⟩
  | Err error =>
      rw [errorRun error] at tail
      simp at tail

/-- Every successful entry, from any choice source, has an originally valid memory descriptor. -/
theorem memory_import_constructor_sound (choices : wasm.choices.Choices)
    (output : MemoryImport) (finalState : wasm.choices.Choices)
    (success : wasm.memory_import.entry choices = Result.ok (.Ok (output, finalState))) :
    MemoryBounded output.memory := by
  rw [wasm.memory_import.entry] at success
  obtain ⟨⟨item, afterMemory⟩, memoryRun, tail⟩ :=
    generation_bind_success (wasm.memory.memory choices) _ (output, finalState) success (by
        intro error
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, core.convert.FromSame.from])
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
    ↓uncurry_apply_pair] at tail
  have bounded := memory_constructor_sound choices item afterMemory memoryRun
  obtain ⟨⟨moduleName, afterModuleName⟩, _, tail⟩ :=
    generation_bind_success (wasm.memory_import.name afterMemory) _ (output, finalState) tail (by
        intro error
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, core.convert.FromSame.from])
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
    ↓uncurry_apply_pair] at tail
  obtain ⟨⟨itemName, afterItemName⟩, _, tail⟩ :=
    generation_bind_success (wasm.memory_import.name afterModuleName) _ (output, finalState) tail (by
        intro error
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, core.convert.FromSame.from])
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
    ↓uncurry_apply_pair] at tail
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at tail
  rcases tail with ⟨rfl, rfl⟩
  exact bounded

private theorem import_section_literal_sound (maximum : Nat)
    (choices : wasm.choices.Choices) (output : wasm.sequence.Sequence MemoryImport)
    (finalState : wasm.choices.Choices)
    (success : wasm.memory_import.generate (naturalLiteral maximum) choices =
      Result.ok (.Ok (output, finalState))) :
    ∀ item ∈ sequenceValues output, MemoryBounded item.memory := by
  induction maximum generalizing choices output finalState with
  | zero =>
      rw [wasm.memory_import.generate] at success
      simp only [decrement_zero, bind_ok, Result.ok.injEq,
        core.result.Result.Ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      simp [sequenceValues]
  | succ maximum ih =>
      rw [wasm.memory_import.generate] at success
      simp only [decrement_literal, bind_ok] at success
      obtain ⟨⟨more, afterMore⟩, _, tail⟩ :=
        generation_bind_success (wasm.choices.pick_word 2#u64 choices) _ (output, finalState) success (by
        intro error
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, core.convert.FromSame.from])
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
        ↓uncurry_apply_pair] at tail
      by_cases stop : more = 0#u64
      · simp [stop] at tail
        rcases tail with ⟨rfl, rfl⟩
        simp [sequenceValues]
      · simp only [stop, ↓reduceIte] at tail
        obtain ⟨⟨head, afterHead⟩, headRun, tail⟩ :=
          generation_bind_success (wasm.memory_import.entry afterMore) _ (output, finalState) tail (by
        intro error
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, core.convert.FromSame.from])
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
          ↓uncurry_apply_pair] at tail
        obtain ⟨⟨rest, afterRest⟩, restRun, tail⟩ :=
          generation_bind_success (wasm.memory_import.generate (naturalLiteral maximum) afterHead)
            _ (output, finalState) tail (by
        intro error
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, core.convert.FromSame.from])
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
          ↓uncurry_apply_pair] at tail
        have headBound := memory_import_constructor_sound afterMore head afterHead headRun
        have restBound := ih afterHead rest afterRest restRun
        simp [wasm.sequence.cons] at tail
        rcases tail with ⟨rfl, rfl⟩
        intro item present
        simp only [sequenceValues, List.mem_cons] at present
        rcases present with rfl | present
        · exact headBound
        · exact restBound item present

/-- Arbitrary successful section executions preserve original descriptor validity. -/
theorem memory_import_section_sound (maximum : wasm.natural.Natural)
    (choices : wasm.choices.Choices) (output : wasm.sequence.Sequence MemoryImport)
    (finalState : wasm.choices.Choices)
    (success : wasm.memory_import.generate maximum choices = Result.ok (.Ok (output, finalState))) :
    ∀ item ∈ sequenceValues output, MemoryBounded item.memory := by
  have canonical : maximum = naturalLiteral (naturalValue maximum) := by
    apply naturalValue_injective
    simp
  rw [canonical] at success
  exact import_section_literal_sound (naturalValue maximum) choices output finalState success

theorem memory_import_section_valid (maximum : wasm.natural.Natural)
    (choices : wasm.choices.Choices) (output : wasm.sequence.Sequence MemoryImport)
    (finalState : wasm.choices.Choices)
    (success : wasm.memory_import.generate maximum choices = Result.ok (.Ok (output, finalState))) :
    SpecTec.Module_ok { emptyModule with IMPORTS := (sequenceValues output).map memoryImport } :=
  memory_import_list_valid (sequenceValues output)
    (memory_import_section_sound maximum choices output finalState success)

open Lean Elab Command in
run_cmd do
  for declaration in [``memory_import_constructor_sound, ``memory_import_section_sound,
      ``memory_import_section_valid] do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"

end RustWasm
