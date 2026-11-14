import WasmReplayWitness
import WasmNaturalIndex
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

def valueTypeCells (values : List IntegerType) : List U64 := values.map valueTypeCell

/-- The actual list loop has no bound on count, accumulator, or tape cursor. -/
theorem value_types_loop_replay (values : List IntegerType) (initial : List ValueType)
    (rest trace : List U64) (offset work : Nat) :
    wasm.value_types_loop (naturalLiteral values.length) (sequenceLiteral initial)
      (replayState (valueTypeCells values ++ rest) trace offset (work + values.length)) =
      Result.ok (.Ok (sequenceLiteral (initial ++ values.map integerValue),
        replayState rest ((valueTypeCells values).reverse ++ trace) (offset + values.length) work)) := by
  induction values generalizing initial trace offset with
  | nil =>
      rw [wasm.value_types_loop]
      simp [valueTypeCells, integerValue]
  | cons head tail ih =>
      have picked := pick_word_state 2#u64 (valueTypeCell head)
        (valueTypeCells tail ++ rest) trace offset (work + tail.length) (by cases head <;> decide)
      rw [wasm.value_types_loop]
      simp only [List.length_cons, decrement_literal, bind_ok, bind_tc_ok,
        valueTypeCells, List.map_cons, List.cons_append, Nat.add_assoc] at picked ⊢
      rw [picked]
      have appended (value : ValueType) : (initial ++ [value]) ++ tail.map integerValue = initial ++ value :: tail.map integerValue := by
        rw [List.append_assoc]
        rfl
      cases head with
      | I32 =>
          simp [valueTypeCell, integerValue, core.result.Result.Insts.CoreOpsTry.branch,
            ↓uncurry_apply_pair, sequence_snoc]
          have recurse := ih (initial ++ [.I32]) (0#u64 :: trace) (offset + 1)
          rw [appended] at recurse
          simpa [valueTypeCells, integerValue, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using recurse
      | I64 =>
          simp [valueTypeCell, integerValue, core.result.Result.Insts.CoreOpsTry.branch,
            ↓uncurry_apply_pair, sequence_snoc]
          have recurse := ih (initial ++ [.I64]) (1#u64 :: trace) (offset + 1)
          rw [appended] at recurse
          simpa [valueTypeCells, integerValue, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using recurse

/-- Every finite numeric signature is generated under every sufficiently large natural bound. -/
theorem value_types_replay (values : List IntegerType) (maximum : Nat)
    (bounded : values.length ≤ maximum) :
    ∃ cells : List U64, ∀ (rest trace : List U64) (offset work : Nat),
      wasm.value_types (naturalLiteral maximum)
        (replayState (cells ++ rest) trace offset (work + cells.length)) =
        Result.ok (.Ok (sequenceLiteral (values.map integerValue),
          replayState rest (cells.reverse ++ trace) (offset + cells.length) work)) := by
  obtain ⟨countCells, countRun⟩ := natural_index_replay (maximum + 1) values.length (by omega)
  refine ⟨countCells ++ valueTypeCells values, ?_⟩
  intro rest trace offset work
  have selectCount : wasm.choices.pick_natural (naturalLiteral (maximum + 1))
      (replayState ((countCells ++ valueTypeCells values) ++ rest) trace offset
        (work + (countCells ++ valueTypeCells values).length)) =
      Result.ok (.Ok (naturalLiteral values.length,
        replayState (valueTypeCells values ++ rest) (countCells.reverse ++ trace)
          (offset + countCells.length) (work + values.length))) := by
    simpa [valueTypeCells, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      countRun (valueTypeCells values ++ rest) trace offset (work + values.length)
  rw [wasm.value_types]
  simp only [copy_natural_eq, bind_ok, bind_tc_ok, increment_literal, selectCount,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  simpa [sequenceLiteral, valueTypeCells, List.append_assoc, List.reverse_append, Nat.add_assoc] using
    value_types_loop_replay values [] rest
      (countCells.reverse ++ trace) (offset + countCells.length) work

/-- The actual generic selector reaches every element of an unbounded sequence. -/
theorem choose_replay {α : Type} (values : List α) (index : Nat) (bounded : index < values.length) :
    ∃ cells : List U64, ∀ (rest trace : List U64) (offset work : Nat),
      wasm.choose (sequenceLiteral values)
        (replayState (cells ++ rest) trace offset (work + cells.length)) =
        Result.ok (.Ok (values[index]'bounded,
          replayState rest (cells.reverse ++ trace) (offset + cells.length) work)) := by
  obtain ⟨cells, indexRun⟩ := natural_index_replay values.length index bounded
  refine ⟨cells, ?_⟩
  intro rest trace offset work
  simp [wasm.choose, sequence_length, indexRun, sequence_select,
    List.getElem?_eq_getElem bounded, core.result.Result.Insts.CoreOpsTry.branch,
    ↓uncurry_apply_pair]

/-- All seven numeric bounds may be arbitrary naturals even in a complete module replay. -/
def unboundedEmptyConfig (types functions parameters results locals exports fuel work : Nat) : wasm.Config :=
  ⟨naturalLiteral types, naturalLiteral functions, naturalLiteral parameters,
    naturalLiteral results, naturalLiteral locals, naturalLiteral exports, naturalLiteral fuel,
    .Zero, .Zero, .Zero, naturalLiteral work⟩

theorem unbounded_empty_supported (types functions parameters results locals exports fuel : Nat) :
    ∃ work : Nat, ReplaySupport
      (unboundedEmptyConfig types functions parameters results locals exports fuel work) emptyModule := by
  obtain ⟨cells, countRun⟩ := natural_index_replay (types + 1) 0 (by omega)
  let config := unboundedEmptyConfig types functions parameters results locals exports fuel cells.length
  let finalState := replayState [] cells.reverse cells.length 0
  have selectZero := countRun [] [] 0 0
  simp only [List.append_nil, List.nil_append, Nat.zero_add] at selectZero
  have typesRun : wasm.types.generate config
      (replayState cells [] 0 cells.length) = Result.ok (.Ok (.Empty, .Empty, finalState)) := by
    rw [wasm.types.generate]
    simp only [config, unboundedEmptyConfig, copy_natural_eq, increment_literal,
      bind_ok, bind_tc_ok, selectZero, core.result.Result.Insts.CoreOpsTry.branch,
      ↓uncurry_apply_pair]
    exact types_zero config .Empty .Empty .Empty finalState
  have built : wasm.build config (replayState cells [] 0 cells.length) =
      Result.ok (.Ok (emptyOutput, finalState)) := by
    apply build_empty_types config _ finalState finalState finalState finalState .Empty .Empty .Empty typesRun
    · rw [wasm.memory_import.generate]
      simp [config, unboundedEmptyConfig, wasm.natural.decrement]
    · rw [wasm.memory.generate]
      simp [config, unboundedEmptyConfig, wasm.natural.decrement]
    · rw [wasm.data.generate]
      simp [config, unboundedEmptyConfig, wasm.natural.decrement]
  refine ⟨cells.length, tapeFromCells cells, emptyOutput,
    ⟨finalState, replay_from_build config _ _ finalState (naturalLiteral cells.length) built rfl⟩, rfl⟩

open Lean Elab Command in
run_cmd do
  for declaration in [``value_types_loop_replay, ``value_types_replay,
      ``choose_replay, ``unbounded_empty_supported] do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"

end RustWasm
