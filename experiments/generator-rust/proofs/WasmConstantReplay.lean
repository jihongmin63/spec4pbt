import WasmNaturalChoice
import WasmModulePrimitives

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast wasm.sequence

private abbrev oneSequence {α : Type} (value : α) : Sequence α := sequenceLiteral [value]

private theorem one_sequence_length {α : Type} (value : α) :
    wasm.sequence.length (oneSequence value) = Result.ok (naturalLiteral 1) :=
  sequence_length [value]

def integerConstantInstruction (width : IntegerType)
    (value : wasm.natural.Natural) : Instruction :=
  match width with
  | .I32 => .Const32 value
  | .I64 => .Const64 value

def integerConstantSignature (width : IntegerType) : FuncType := ⟨.Empty, oneSequence (integerValue width)⟩
def integerConstantGroup (width : IntegerType) : RecGroup := ⟨oneSequence ⟨.Final, none, integerConstantSignature width⟩⟩
def integerConstantOutput (width : IntegerType) (value : wasm.natural.Natural) : wasm.ast.Module :=
  ⟨oneSequence (integerConstantGroup width), oneSequence ⟨.Zero, .Empty, oneSequence (integerConstantInstruction width value)⟩,
    .Empty, none, .Empty, .Empty, .Empty⟩
def constantConfig (value : wasm.natural.Natural) : wasm.Config :=
  ⟨naturalLiteral 1, naturalLiteral 1, .Zero, naturalLiteral 1, .Zero, .Zero, .Zero, .Zero, .Zero, .Zero,
    naturalLiteral ((naturalCells value).length + 14)⟩
def integerConstantCells (width : IntegerType) (value : wasm.natural.Natural) : List U64 :=
  [1#u64, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, valueTypeCell width, 1#u64, 0#u64, 0#u64, 0#u64, 0#u64] ++
    naturalCells value ++ [0#u64]
def integerConstantFinal (width : IntegerType) (value : wasm.natural.Natural) : wasm.choices.Choices :=
  replayState [] (integerConstantCells width value).reverse ((naturalCells value).length + 13) 0

private theorem tick_state (input trace : List U64) (offset work : Nat) :
    wasm.choices.tick (replayState input trace offset (work + 1)) =
      Result.ok (.Ok (replayState input trace offset work)) := by
  simp [wasm.choices.tick, replayState, decrement_literal]

private theorem pick10 (rest trace : List U64) (offset work : Nat) :
    wasm.choices.pick_natural (naturalLiteral 1) (replayState (0#u64 :: rest) trace offset (work + 1)) =
      Result.ok (.Ok (naturalLiteral 0, replayState rest (0#u64 :: trace) (offset + 1) work)) :=
  pick_natural_word_state 1#u64 0#u64 rest trace offset work (by decide)
private theorem pick21 (rest trace : List U64) (offset work : Nat) :
    wasm.choices.pick_natural (naturalLiteral 2) (replayState (1#u64 :: rest) trace offset (work + 1)) =
      Result.ok (.Ok (naturalLiteral 1, replayState rest (1#u64 :: trace) (offset + 1) work)) :=
  pick_natural_word_state 2#u64 1#u64 rest trace offset work (by decide)
private theorem word20 (rest trace : List U64) (offset work : Nat) :
    wasm.choices.pick_word 2#u64 (replayState (0#u64 :: rest) trace offset (work + 1)) =
      Result.ok (.Ok (0#u64, replayState rest (0#u64 :: trace) (offset + 1) work)) :=
  pick_word_state 2#u64 0#u64 rest trace offset work (by decide)

private theorem increment_zero : wasm.natural.increment .Zero = Result.ok (naturalLiteral 1) := by
  simpa [naturalLiteral] using increment_literal 0
private theorem decrement_one : wasm.natural.decrement (naturalLiteral 1) = Result.ok (some .Zero) := by
  simpa [naturalLiteral] using decrement_literal 0
private theorem increment_one : wasm.natural.increment (naturalLiteral 1) = Result.ok (naturalLiteral 2) := by
  simpa using increment_literal 1
private theorem decrement_empty : wasm.natural.decrement .Zero = Result.ok none := rfl
private theorem natural_zero : naturalLiteral 0 = wasm.natural.Natural.Zero := rfl
attribute [local simp] increment_zero increment_one decrement_one decrement_empty natural_zero

private theorem constant_payload (width : IntegerType) (value : wasm.natural.Natural)
    (rest trace : List U64) (offset work : Nat) :
    wasm.body.constant (integerValue width)
      (replayState (naturalCells value ++ rest) trace offset (work + (naturalCells value).length)) =
      Result.ok (.Ok (integerConstantInstruction width value,
        replayState rest ((naturalCells value).reverse ++ trace)
          (offset + (naturalCells value).length) work)) := by
  cases width <;> simp [integerValue, integerConstantInstruction, wasm.body.constant, natural_choice_replay, core.result.Result.Insts.CoreOpsTry.branch]

private theorem leaf_constant (width : IntegerType) (value : wasm.natural.Natural)
    (rest trace : List U64) (offset work : Nat) :
    wasm.body.leaf (integerValue width) .Empty (oneSequence (integerConstantGroup width)) .Empty (oneSequence .Zero)
      (replayState (0#u64 :: (naturalCells value ++ rest)) trace offset
        ((work + (naturalCells value).length) + 1)) =
      Result.ok (.Ok (integerConstantInstruction width value,
        replayState rest ((naturalCells value).reverse ++ 0#u64 :: trace)
          ((offset + 1) + (naturalCells value).length) work)) := by
  have payload := constant_payload width
  cases width <;> simp only [integerValue, integerConstantInstruction] at payload ⊢ <;>
    simp [wasm.body.leaf, wasm.body.matching_locals, wasm.body.leaf_reads, wasm.body.reference_rules,
    wasm.ast.copy_value, wasm.choose, wasm.sequence.cons, wasm.sequence.length, wasm.sequence.select, wasm.natural.decrement,
    pick10, payload, core.result.Result.Insts.CoreOpsTry.branch,
    ↓uncurry_apply_pair]

private theorem base_single (width : IntegerType) (value : wasm.natural.Natural)
    (initial final : wasm.choices.Choices)
    (runLeaf : wasm.body.leaf (integerValue width) .Empty (oneSequence (integerConstantGroup width)) .Empty (oneSequence .Zero) initial = Result.ok (.Ok (integerConstantInstruction width value, final))) :
    wasm.body.base .Empty (oneSequence (integerValue width)) .Empty (oneSequence (integerConstantGroup width)) .Empty (oneSequence .Zero) initial =
      Result.ok (.Ok (oneSequence (integerConstantInstruction width value), final)) := by
  simp only [oneSequence, sequenceLiteral] at runLeaf
  rw [wasm.body.base]
  simp [wasm.body.drops, oneSequence, sequenceLiteral,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.body.leaves.eq_def]
  simp [runLeaf, wasm.sequence.snoc, wasm.sequence.append, wasm.sequence.cons,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.body.leaves.eq_def]

private theorem generate_single (width : IntegerType) (value : wasm.natural.Natural)
    (initial afterTick final : wasm.choices.Choices)
    (types : Sequence FuncType)
    (tickRun : wasm.choices.tick initial = Result.ok (.Ok afterTick))
    (baseRun : wasm.body.base .Empty (oneSequence (integerValue width)) .Empty (oneSequence (integerConstantGroup width)) .Empty (oneSequence .Zero) afterTick =
      Result.ok (.Ok (oneSequence (integerConstantInstruction width value), final))) :
    wasm.body.generate .Empty (oneSequence (integerValue width)) .Zero .Empty types (oneSequence .Zero) (oneSequence (integerConstantGroup width)) .Empty initial =
      Result.ok (.Ok (oneSequence (integerConstantInstruction width value), final)) := by
  have copyRun := copy_types_literal [integerValue width]
  change wasm.ast.copy_types (oneSequence (integerValue width)) = Result.ok (oneSequence (integerValue width)) at copyRun
  simp [wasm.body.generate, wasm.body.push, copyRun]
  rw [wasm.body.execute.eq_def]
  simp [tickRun, wasm.body.step, baseRun, wasm.body.push,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.body.execute.eq_def]
  simp [wasm.body.pop_body, core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]

private theorem locals_zero (rest trace : List U64) (offset work : Nat) :
    wasm.types.locals .Zero (naturalLiteral 1) (replayState (0#u64 :: rest) trace offset (work + 1)) =
      Result.ok (.Ok (.Empty, replayState rest (0#u64 :: trace) (offset + 1) work)) := by
  simp [wasm.types.locals, pick10, core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.types.locals_loop.eq_def]
  simp [naturalLiteral]

private theorem type_word (width : IntegerType)
    (rest trace : List U64) (offset work : Nat) :
    wasm.choices.pick_word 3#u64
      (replayState (valueTypeCell width :: rest) trace offset (work + 1)) =
      Result.ok (.Ok (valueTypeCell width,
        replayState rest (valueTypeCell width :: trace) (offset + 1) work)) :=
  pick_word_state 3#u64 (valueTypeCell width) rest trace offset work (by cases width <;> decide)

private theorem constant_types (width : IntegerType) (value : wasm.natural.Natural)
    (rest trace : List U64) (offset work : Nat) :
    wasm.types.generate (constantConfig value)
      (replayState ([1#u64, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, valueTypeCell width] ++ rest) trace offset (work + 7)) =
      Result.ok (.Ok (oneSequence (integerConstantGroup width), oneSequence (integerConstantSignature width),
        replayState rest ([valueTypeCell width, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, 1#u64] ++ trace) (offset + 7) work)) := by
  rw [wasm.types.generate]
  simp [constantConfig, pick21, core.result.Result.Insts.CoreOpsTry.branch,
    ↓uncurry_apply_pair]
  rw [wasm.types.groups.eq_def]
  simp [pick21, core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.types.headers.eq_def]
  simp [word20, wasm.types.parent, pick10, wasm.sequence.snoc,
    wasm.sequence.append, wasm.sequence.cons,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.types.headers.eq_def]
  simp [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.types.members.eq_def]
  simp [wasm.types.signature, wasm.types.values, pick10, pick21,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.types.values_loop.eq_def]
  simp [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, pick21]
  rw [wasm.types.values_loop.eq_def]
  have valueRun (input history : List U64) (cursor budget : Nat) :
      wasm.types.value (naturalLiteral 1)
        (replayState (valueTypeCell width :: input) history cursor (budget + 1)) =
        Result.ok (.Ok (integerValue width,
          replayState input (valueTypeCell width :: history) (cursor + 1) budget)) := by
    have picked := type_word width input history cursor budget
    cases width <;> simp only [valueTypeCell] at picked ⊢ <;>
      simp [wasm.types.value, naturalLiteral, positiveLiteral, picked,
        integerValue, valueTypeCell, core.result.Result.Insts.CoreOpsTry.branch,
        ↓uncurry_apply_pair] <;> rfl
  simp [valueRun, wasm.sequence.snoc, wasm.sequence.append, wasm.sequence.cons,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.types.values_loop.eq_def]
  simp [wasm.ast.copy_signature, wasm.ast.copy_types, wasm.sequence.snoc,
    wasm.sequence.append, wasm.sequence.cons,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.types.members.eq_def]
  simp [wasm.sequence.snoc, wasm.sequence.append, wasm.sequence.cons,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.types.groups.eq_def]
  simp [integerConstantGroup, integerConstantSignature, oneSequence, sequenceLiteral, Nat.add_assoc]

private theorem constant_indices (rest trace : List U64) (offset work : Nat) :
    wasm.function_indices (naturalLiteral 1) (naturalLiteral 1)
      (replayState (1#u64 :: 0#u64 :: rest) trace offset (work + 2)) =
      Result.ok (.Ok (oneSequence wasm.natural.Natural.Zero,
        replayState rest (0#u64 :: 1#u64 :: trace) (offset + 2) work)) := by
  have pickOne := pick10
  have pickTwo := pick21
  have inc := increment_one
  have dec := decrement_one
  simp [naturalLiteral, positiveLiteral] at pickOne pickTwo inc dec
  rw [wasm.function_indices.eq_def]
  simp [inc, pickTwo, core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair,
    naturalLiteral, positiveLiteral]
  rw [wasm.indices_loop.eq_def]
  simp [dec, pickOne, wasm.sequence.snoc, wasm.sequence.append, wasm.sequence.cons,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.indices_loop.eq_def]
  simp [oneSequence, sequenceLiteral, Nat.add_assoc]

private theorem signature_lookup (width : IntegerType) : wasm.lookup (oneSequence (integerConstantSignature width)) .Zero =
    Result.ok (.Ok (integerConstantSignature width)) := by
  have got : wasm.sequence.get (oneSequence (integerConstantSignature width)) .Zero =
      Result.ok (some (integerConstantSignature width)) := by
    simpa [oneSequence, naturalLiteral] using sequence_get [integerConstantSignature width] 0
  simp [wasm.lookup, got]

private theorem functions_single (width : IntegerType) (value : wasm.natural.Natural)
    (initial afterLocals final : wasm.choices.Choices)
    (localsRun : wasm.types.locals .Zero (naturalLiteral 1) initial = Result.ok (.Ok (.Empty, afterLocals)))
    (bodyRun : wasm.body.generate .Empty (oneSequence (integerValue width)) .Zero .Empty
      (oneSequence (integerConstantSignature width)) (oneSequence .Zero) (oneSequence (integerConstantGroup width)) .Empty afterLocals =
      Result.ok (.Ok (oneSequence (integerConstantInstruction width value), final))) :
    wasm.functions_loop (oneSequence .Zero) (constantConfig value) (oneSequence (integerConstantSignature width))
      (oneSequence .Zero) (oneSequence (integerConstantGroup width)) .Empty .Empty initial =
      Result.ok (.Ok ((integerConstantOutput width value).functions, final)) := by
  have copied := copy_types_literal [integerValue width]
  have joined := join_types_literal [] []
  have looked := signature_lookup width
  simp only [oneSequence, sequenceLiteral, integerConstantSignature] at copied joined looked bodyRun
  rw [wasm.functions_loop.eq_def]
  simp [oneSequence, sequenceLiteral, constantConfig, localsRun, looked,
    copied, joined, integerConstantSignature, one_sequence_length, wasm.sequence.length, core.result.Result.Insts.CoreOpsTry.branch,
    ↓uncurry_apply_pair]
  erw [bodyRun]
  simp [wasm.sequence.snoc, wasm.sequence.append, wasm.sequence.cons,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  rw [wasm.functions_loop.eq_def]
  simp [integerConstantOutput, oneSequence, sequenceLiteral]

private theorem exports_zero (rest trace : List U64) (offset work : Nat) :
    wasm.generate_exports .Zero (naturalLiteral 1)
      (replayState (0#u64 :: rest) trace offset (work + 1)) =
      Result.ok (.Ok (.Empty, replayState rest (0#u64 :: trace) (offset + 1) work)) := by
  have picked := pick10
  simp [naturalLiteral, positiveLiteral] at picked
  rw [wasm.generate_exports.eq_def]
  simp [picked, wasm.sequence.cons, core.result.Result.Insts.CoreOpsTry.branch,
    ↓uncurry_apply_pair, naturalLiteral, positiveLiteral]
  rw [wasm.exports_loop.eq_def]
  simp

private theorem start_none (width : IntegerType) (rest trace : List U64) (offset work : Nat) :
    wasm.generate_start (oneSequence (integerConstantSignature width)) (oneSequence .Zero)
      (replayState (0#u64 :: rest) trace offset (work + 1)) =
      Result.ok (.Ok (none, replayState rest (0#u64 :: trace) (offset + 1) work)) := by
  have looked := signature_lookup width
  simp only [oneSequence, sequenceLiteral, integerConstantSignature] at looked
  have noStarts : wasm.start_indices (oneSequence (integerConstantSignature width)) (oneSequence .Zero)
      .Zero .Empty = Result.ok (.Ok .Empty) := by
    rw [wasm.start_indices.eq_def]
    simp [oneSequence, sequenceLiteral, looked, integerConstantSignature,
      core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
    rw [wasm.start_indices.eq_def]
  simp only [oneSequence, sequenceLiteral] at noStarts
  rw [wasm.generate_start.eq_def]
  simp [noStarts, sequence_empty_length, pick10,
    core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, oneSequence, sequenceLiteral]

/-- Every Natural payload is produced by the full translated Rust entry point. -/
theorem integer_constant_replay (width : IntegerType) (value : wasm.natural.Natural) :
    wasm.replay (constantConfig value) (tapeFromCells (integerConstantCells width value)) =
      Result.ok (.Ok (integerConstantOutput width value, integerConstantFinal width value)) := by
  let cells := naturalCells value
  let before : List U64 := [0#u64, 0#u64, 0#u64, 1#u64, valueTypeCell width, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, 1#u64]
  let after : List U64 := cells.reverse ++ 0#u64 :: before
  have typesRun := constant_types width value
    ([1#u64, 0#u64, 0#u64, 0#u64, 0#u64] ++ cells ++ [0#u64]) [] 0 (cells.length + 7)
  have indicesRun := constant_indices
    ([0#u64, 0#u64, 0#u64] ++ cells ++ [0#u64]) [valueTypeCell width, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, 1#u64] 7 (cells.length + 5)
  have exportsRun := exports_zero
    ([0#u64, 0#u64] ++ cells ++ [0#u64]) [0#u64, 1#u64, valueTypeCell width, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, 1#u64] 9 (cells.length + 4)
  have localsRun := locals_zero (0#u64 :: (cells ++ [0#u64]))
    [0#u64, 0#u64, 1#u64, valueTypeCell width, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, 1#u64] 10 (cells.length + 3)
  have leafRun := leaf_constant width value [0#u64] before 11 1
  have baseRun := base_single width value _ _ leafRun
  have workEq : 1 + (naturalCells value).length + 1 = cells.length + 2 := by dsimp [cells]; omega
  rw [workEq] at baseRun
  have tickRun := tick_state (0#u64 :: (cells ++ [0#u64])) before 11 (cells.length + 2)
  have bodyRun := generate_single width value _ _ _ (oneSequence (integerConstantSignature width))
    tickRun baseRun
  have functionsRun := functions_single width value _ _ _ localsRun bodyRun
  have startRun := start_none width [] after (12 + cells.length) 0
  have startOffset : 12 + cells.length + 1 = cells.length + 13 := by omega
  rw [startOffset] at startRun
  have noImports (choices : wasm.choices.Choices) :
      wasm.memory_import.generate .Zero choices = Result.ok (.Ok (.Empty, choices)) := by
    rw [wasm.memory_import.generate]
    simp [wasm.natural.decrement]
  have noMemories (choices : wasm.choices.Choices) :
      wasm.memory.generate .Zero choices = Result.ok (.Ok (.Empty, choices)) := by
    rw [wasm.memory.generate]
    simp [wasm.natural.decrement]
  have noDatas (choices : wasm.choices.Choices) :
      wasm.data.generate .Zero choices = Result.ok (.Ok (.Empty, choices)) := by
    rw [wasm.data.generate]
    simp [wasm.natural.decrement]
  have built : wasm.build (constantConfig value)
      (replayState (integerConstantCells width value) [] 0 (cells.length + 14)) =
      Result.ok (.Ok (integerConstantOutput width value, integerConstantFinal width value)) := by
    simp [wasm.build, core.result.Result.Insts.CoreOpsTry.branch]
    simp only [integerConstantCells, List.append_assoc, List.cons_append, List.nil_append] at typesRun ⊢
    erw [typesRun]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair,
      bind_ok, bind_tc_ok, constantConfig, copy_natural_eq, noImports]
    simp [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, one_sequence_length, constantConfig]
    erw [indicesRun]
    simp [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, one_sequence_length, constantConfig]
    erw [exportsRun]
    simp [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, one_sequence_length, constantConfig, wasm.declared_refs]
    erw [functionsRun]
    simp [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, one_sequence_length, constantConfig]
    erw [startRun]
    simp [constantConfig, copy_natural_eq, noMemories, noDatas, integerConstantOutput, integerConstantFinal,
      integerConstantCells, cells, before, after, List.reverse_append,
      List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      core.result.Result.Insts.CoreOpsTry.branch]
  simp [wasm.replay, copy_natural_eq]
  change (do
    let output ← wasm.build (constantConfig value)
      (replayState (integerConstantCells width value) [] 0 (cells.length + 14))
    let cf ← core.result.Result.Insts.CoreOpsTry.branch output
    _) = _
  rw [built]
  simp [integerConstantFinal, replayState, tapeFromCells,
    core.result.Result.Insts.CoreOpsTry.branch]


def constantSignature : FuncType := integerConstantSignature .I32
def constantGroup : RecGroup := integerConstantGroup .I32
def constantOutput (value : wasm.natural.Natural) : wasm.ast.Module :=
  integerConstantOutput .I32 value
def constantCells (value : wasm.natural.Natural) : List U64 := integerConstantCells .I32 value
def constantFinal (value : wasm.natural.Natural) : wasm.choices.Choices :=
  integerConstantFinal .I32 value

/-- Preserve the original exact full replay theorem for every natural i32 payload. -/
theorem constant_replay (value : wasm.natural.Natural) :
    wasm.replay (constantConfig value) (tapeFromCells (constantCells value)) =
      Result.ok (.Ok (constantOutput value, constantFinal value)) :=
  integer_constant_replay .I32 value

/-- The same actual Rust construction covers every natural i64 payload. -/
theorem constant64_replay (value : wasm.natural.Natural) :
    wasm.replay (constantConfig value) (tapeFromCells (integerConstantCells .I64 value)) =
      Result.ok (.Ok (integerConstantOutput .I64 value, integerConstantFinal .I64 value)) :=
  integer_constant_replay .I64 value

end RustWasm
