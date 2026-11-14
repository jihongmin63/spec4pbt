import WasmNaturalWord
import WasmReplaySteps
import WasmSequence
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast wasm.sequence

def integerValue : IntegerType → ValueType
  | .I32 => .I32
  | .I64 => .I64

def valueTypeCell : IntegerType → U64
  | .I32 => 0#u64
  | .I64 => 1#u64

/-- Word-sized bounds keep the same one-cell tape encoding in the unbounded core. -/
theorem pick_natural_word_state (bound cell : U64) (rest trace : List U64)
    (offset work : Nat) (inRange : cell.val < bound.val) :
    wasm.choices.pick_natural (naturalLiteral bound.val)
      (replayState (cell :: rest) trace offset (work + 1)) =
      Result.ok (.Ok (naturalLiteral cell.val,
        replayState rest (cell :: trace) (offset + 1) work)) := by
  have bounded : bound.val < 18446744073709551616 := by scalar_tac
  rw [wasm.choices.pick_natural, literal_to_word]
  simp only [wordEncoding, dif_pos bounded, bind_ok, bind_tc_ok]
  have restored : (UScalar.ofNatCore bound.val bounded : U64) = bound := by
    apply UScalar.val_eq_imp
    simp only [UScalar.ofNatCore_val_eq]
  rw [restored, pick_word_state bound cell rest trace offset work inRange]
  simp [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, natural_from_word]

@[simp] theorem copy_value_eq (value : ValueType) :
    wasm.ast.copy_value value = Result.ok value := by
  cases value <;> simp [wasm.ast.copy_value]

@[simp] theorem copy_types_literal (values : List ValueType) :
    wasm.ast.copy_types (sequenceLiteral values) = Result.ok (sequenceLiteral values) := by
  induction values with
  | nil => rw [sequenceLiteral, wasm.ast.copy_types]
  | cons head tail ih =>
      rw [sequenceLiteral, wasm.ast.copy_types]
      simp [ih, wasm.sequence.cons, ↓uncurry_apply_pair]

theorem join_types_literal (left right : List ValueType) :
    wasm.ast.join_types (sequenceLiteral left) (sequenceLiteral right) =
      Result.ok (sequenceLiteral (left ++ right)) := by
  simp [wasm.ast.join_types, sequence_append]

theorem types_zero (config : wasm.Config) (groups : Sequence RecGroup) (flat : Sequence FuncType)
    (eligible : Sequence wasm.natural.Natural) (choices : wasm.choices.Choices) :
    wasm.types.groups .Zero config groups flat eligible choices = Result.ok (.Ok (groups, flat, choices)) := by
  rw [wasm.types.groups]
  simp [wasm.natural.decrement]

theorem functions_nil (config : wasm.Config) (choices : wasm.choices.Choices) :
    wasm.functions_loop .Empty config .Empty .Empty .Empty .Empty .Empty choices =
      Result.ok (.Ok (.Empty, choices)) := by
  rw [wasm.functions_loop]

theorem generate_types_zero (config : wasm.Config) (zero : config.max_types = naturalLiteral 0)
    (rest trace : List U64) (offset work : Nat) :
    wasm.types.generate config (replayState (0#u64 :: rest) trace offset (work + 1)) =
      Result.ok (.Ok (.Empty, .Empty, replayState rest (0#u64 :: trace) (offset + 1) work)) := by
  have picked := pick_natural_word_state 1#u64 0#u64 rest trace offset work (by decide)
  simp only [UScalar.ofNatCore_val_eq] at picked
  rw [wasm.types.generate]
  simp only [copy_natural_eq, zero, increment_literal, bind_ok, bind_tc_ok, picked,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  exact types_zero config .Empty .Empty .Empty (replayState rest (0#u64 :: trace) (offset + 1) work)

@[simp] theorem sequence_empty_length {α : Type} :
    wasm.sequence.length (Sequence.Empty : Sequence α) = Result.ok wasm.natural.Natural.Zero := by
  rw [wasm.sequence.length]

/-- Empty type generation skips numeric declarations and composes the actual sections. -/
theorem build_empty_types (config : wasm.Config)
    (initial afterTypes afterImports afterMemories finalState : wasm.choices.Choices)
    (imports : Sequence MemoryImport) (memories : Memories) (datas : Datas)
    (typesRun : wasm.types.generate config initial = Result.ok (.Ok (.Empty, .Empty, afterTypes)))
    (importRun : wasm.memory_import.generate config.max_memory_imports afterTypes =
      Result.ok (.Ok (imports, afterImports)))
    (memoryRun : wasm.memory.generate config.max_memories afterImports =
      Result.ok (.Ok (memories, afterMemories)))
    (dataRun : wasm.data.generate config.max_datas afterMemories =
      Result.ok (.Ok (datas, finalState))) :
    wasm.build config initial =
      Result.ok (.Ok (⟨.Empty, .Empty, .Empty, none, memories, datas, imports⟩, finalState)) := by
  simp [wasm.build, typesRun, copy_natural_eq, importRun, sequence_empty_length, wasm.function_indices,
    functions_nil, wasm.declared_refs, wasm.generate_exports, wasm.generate_start, memoryRun, dataRun,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]

theorem replay_from_build (config : wasm.Config) (tape : wasm.choices.Tape)
    (output : wasm.ast.Module) (finalState : wasm.choices.Choices) (offset : wasm.natural.Natural)
    (buildRun : wasm.build config ⟨.Replay tape .Zero, .Empty, config.work_limit⟩ =
      Result.ok (.Ok (output, finalState)))
    (finished : finalState.source = .Replay .Empty offset) :
    wasm.replay config tape = Result.ok (.Ok (output, finalState)) := by
  simp [wasm.replay, buildRun, finished, core.result.Result.Insts.CoreOpsTry.branch,
    ↓uncurry_apply_pair]

open Lean Elab Command in
run_cmd do
  for declaration in [``pick_natural_word_state, ``copy_value_eq, ``copy_types_literal, ``join_types_literal,
      ``types_zero, ``functions_nil, ``generate_types_zero, ``sequence_empty_length,
      ``build_empty_types, ``replay_from_build] do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"

end RustWasm
