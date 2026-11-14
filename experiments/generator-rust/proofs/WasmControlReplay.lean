import WasmReplayEvaluation

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

def controlConfig (results fuel work : Nat) : wasm.Config :=
  ⟨naturalLiteral 1, naturalLiteral 1, .Zero, naturalLiteral results, .Zero, .Zero,
    naturalLiteral fuel, .Zero, .Zero, .Zero, naturalLiteral work⟩

def controlOutput (results : wasm.sequence.Sequence ValueType)
    (body : wasm.sequence.Sequence Instruction) : wasm.ast.Module :=
  ⟨sequenceLiteral [⟨sequenceLiteral [⟨.Final, none, ⟨.Empty, results⟩⟩]⟩],
    sequenceLiteral [⟨.Zero, .Empty, body⟩], .Empty, none, .Empty, .Empty, .Empty⟩

def controlFinal (cells : List U64) : wasm.choices.Choices :=
  ⟨.Replay .Empty (naturalLiteral cells.length), tapeFromCells cells.reverse, .Zero⟩

def unreachableAddConfig : wasm.Config := controlConfig 1 2 20
def unreachableAddCells : List U64 := [1#u64, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, 0#u64, 1#u64, 0#u64, 0#u64, 0#u64, 5#u64, 18#u64, 0#u64, 0#u64]
def unreachableAddOutput : wasm.ast.Module :=
  controlOutput (sequenceLiteral [.I32])
    (sequenceLiteral [.Unreachable, .Binary .I32 .Add])

theorem unreachable_add_replay :
    wasm.replay unreachableAddConfig (tapeFromCells unreachableAddCells) =
      Result.ok (.Ok (unreachableAddOutput, controlFinal unreachableAddCells)) := by
  unfold unreachableAddConfig unreachableAddCells unreachableAddOutput
  unfold controlConfig controlOutput controlFinal
  wasm_replay_run

def unreachableOperandConfig : wasm.Config := controlConfig 1 3 24
def unreachableOperandCells : List U64 := [1#u64, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, 0#u64, 1#u64, 0#u64, 0#u64, 0#u64, 5#u64, 4#u64, 7#u64, 18#u64, 0#u64, 0#u64]
def unreachableOperandOutput : wasm.ast.Module :=
  controlOutput (sequenceLiteral [.I32])
    (sequenceLiteral [.Unreachable, .Const32 (naturalLiteral 7), .Binary .I32 .Add])

theorem unreachable_operand_replay :
    wasm.replay unreachableOperandConfig (tapeFromCells unreachableOperandCells) =
      Result.ok (.Ok (unreachableOperandOutput, controlFinal unreachableOperandCells)) := by
  unfold unreachableOperandConfig unreachableOperandCells unreachableOperandOutput
  unfold controlConfig controlOutput controlFinal
  wasm_replay_run

def unreachablePredecessorConfig : wasm.Config := controlConfig 0 1 19
def unreachablePredecessorCells : List U64 := [1#u64, 1#u64, 0#u64, 0#u64, 0#u64, 0#u64, 1#u64, 0#u64, 0#u64, 0#u64, 11#u64, 1#u64, 1#u64, 0#u64, 7#u64, 0#u64]
def unreachablePredecessorOutput : wasm.ast.Module :=
  controlOutput (sequenceLiteral [])
    (sequenceLiteral [.Const64 (naturalLiteral 7), .Unreachable])

theorem unreachable_predecessor_replay :
    wasm.replay unreachablePredecessorConfig (tapeFromCells unreachablePredecessorCells) =
      Result.ok (.Ok (unreachablePredecessorOutput, controlFinal unreachablePredecessorCells)) := by
  unfold unreachablePredecessorConfig unreachablePredecessorCells unreachablePredecessorOutput
  unfold controlConfig controlOutput controlFinal
  wasm_replay_run

def loopLabelConfig : wasm.Config := controlConfig 1 2 22
def loopLabelCells : List U64 := [1#u64, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, 0#u64, 1#u64, 0#u64, 0#u64, 0#u64, 13#u64, 0#u64, 19#u64, 0#u64, 0#u64]
def loopLabelOutput : wasm.ast.Module :=
  controlOutput (sequenceLiteral [.I32])
    (sequenceLiteral [.Loop (.Value .I32) (sequenceLiteral [.Branch .Zero])])

theorem loop_label_replay :
    wasm.replay loopLabelConfig (tapeFromCells loopLabelCells) =
      Result.ok (.Ok (loopLabelOutput, controlFinal loopLabelCells)) := by
  unfold loopLabelConfig loopLabelCells loopLabelOutput
  unfold controlConfig controlOutput controlFinal
  wasm_replay_run

def outerLabelConfig : wasm.Config := controlConfig 1 3 29
def outerLabelCells : List U64 := [1#u64, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, 0#u64, 1#u64, 0#u64, 0#u64, 0#u64, 12#u64, 0#u64, 12#u64, 0#u64, 21#u64, 0#u64, 0#u64, 7#u64, 0#u64]
def outerLabelOutput : wasm.ast.Module :=
  controlOutput (sequenceLiteral [.I32])
    (sequenceLiteral [.Block (.Value .I32) (sequenceLiteral [.Block (.Value .I32) (sequenceLiteral [.Const32 (naturalLiteral 7), .Branch (naturalLiteral 1)])])])

theorem outer_label_replay :
    wasm.replay outerLabelConfig (tapeFromCells outerLabelCells) =
      Result.ok (.Ok (outerLabelOutput, controlFinal outerLabelCells)) := by
  unfold outerLabelConfig outerLabelCells outerLabelOutput
  unfold controlConfig controlOutput controlFinal
  wasm_replay_run

def branchIfConfig : wasm.Config := controlConfig 1 1 20
def branchIfCells : List U64 := [1#u64, 1#u64, 0#u64, 0#u64, 0#u64, 1#u64, 0#u64, 1#u64, 0#u64, 0#u64, 0#u64, 20#u64, 0#u64, 7#u64, 0#u64, 0#u64, 0#u64]
def branchIfOutput : wasm.ast.Module :=
  controlOutput (sequenceLiteral [.I32])
    (sequenceLiteral [.Const32 (naturalLiteral 7), .Const32 (naturalLiteral 0), .BranchIf .Zero])

theorem branch_if_replay :
    wasm.replay branchIfConfig (tapeFromCells branchIfCells) =
      Result.ok (.Ok (branchIfOutput, controlFinal branchIfCells)) := by
  unfold branchIfConfig branchIfCells branchIfOutput
  unfold controlConfig controlOutput controlFinal
  wasm_replay_run

end RustWasm
