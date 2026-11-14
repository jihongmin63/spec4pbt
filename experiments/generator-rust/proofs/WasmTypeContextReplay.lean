import WasmReplayEvaluation

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

def contextRef (index : Nat) : ValueType := .Ref .Nullable (naturalLiteral index)
def contextVoid : FuncType := ⟨.Empty, .Empty⟩
def contextVoidGroup : RecGroup := ⟨sequenceLiteral [⟨.Final, none, contextVoid⟩]⟩

def contextOutput (types : List RecGroup) (functions : List Function) (exports : List Export) : wasm.ast.Module :=
  ⟨sequenceLiteral types, sequenceLiteral functions, sequenceLiteral exports, none, .Empty, .Empty, .Empty⟩

def contextFinal (cells : List U64) : wasm.choices.Choices :=
  ⟨.Replay .Empty (naturalLiteral cells.length), tapeFromCells cells.reverse, .Zero⟩

def recursiveParentConfig : wasm.Config :=
  ⟨naturalLiteral 2, .Zero, naturalLiteral 1, .Zero, .Zero, .Zero, .Zero, .Zero, .Zero, .Zero, naturalLiteral 12⟩
def recursiveParentCells : List U64 :=
  [1#u64, 2#u64, 1#u64, 0#u64, 0#u64, 1#u64, 1#u64, 2#u64, 0#u64, 0#u64, 0#u64, 0#u64]
def recursiveParentOutput : wasm.ast.Module := contextOutput
  [⟨sequenceLiteral [
    ⟨.NoFinal, none, ⟨sequenceLiteral [contextRef 0], .Empty⟩⟩,
    ⟨.Final, some .Zero, ⟨sequenceLiteral [contextRef 0], .Empty⟩⟩]⟩] [] []

theorem recursive_parent_replay :
    wasm.replay recursiveParentConfig (tapeFromCells recursiveParentCells) =
      Result.ok (.Ok (recursiveParentOutput, contextFinal recursiveParentCells)) := by
  unfold recursiveParentConfig recursiveParentCells recursiveParentOutput contextOutput contextFinal contextRef
  wasm_replay_run

def mutualGroupConfig : wasm.Config :=
  ⟨naturalLiteral 2, .Zero, naturalLiteral 1, .Zero, .Zero, .Zero, .Zero, .Zero, .Zero, .Zero, naturalLiteral 17⟩
def mutualGroupCells : List U64 :=
  [1#u64, 2#u64, 0#u64, 0#u64, 0#u64, 0#u64, 1#u64, 2#u64, 0#u64, 1#u64, 0#u64,
   1#u64, 2#u64, 0#u64, 0#u64, 0#u64, 0#u64]
def mutualGroupOutput : wasm.ast.Module := contextOutput
  [⟨sequenceLiteral [
    ⟨.Final, none, ⟨sequenceLiteral [contextRef 1], .Empty⟩⟩,
    ⟨.Final, none, ⟨sequenceLiteral [contextRef 0], .Empty⟩⟩]⟩] [] []

theorem mutual_group_replay :
    wasm.replay mutualGroupConfig (tapeFromCells mutualGroupCells) =
      Result.ok (.Ok (mutualGroupOutput, contextFinal mutualGroupCells)) := by
  unfold mutualGroupConfig mutualGroupCells mutualGroupOutput contextOutput contextFinal contextRef
  wasm_replay_run

def rawAliasConfig : wasm.Config :=
  ⟨naturalLiteral 3, naturalLiteral 1, naturalLiteral 1, naturalLiteral 1,
    .Zero, .Zero, .Zero, .Zero, .Zero, .Zero, naturalLiteral 29⟩
def rawAliasCells : List U64 :=
  [3#u64, 1#u64, 0#u64, 0#u64, 0#u64, 0#u64, 1#u64, 0#u64, 0#u64, 0#u64, 0#u64,
   1#u64, 0#u64, 0#u64, 1#u64, 2#u64, 0#u64, 0#u64, 1#u64, 2#u64, 0#u64, 1#u64,
   1#u64, 2#u64, 0#u64, 0#u64, 1#u64, 0#u64]
def rawAliasOutput : wasm.ast.Module := contextOutput
  [contextVoidGroup, contextVoidGroup,
   ⟨sequenceLiteral [⟨.Final, none, ⟨sequenceLiteral [contextRef 0], sequenceLiteral [contextRef 1]⟩⟩]⟩]
  [⟨naturalLiteral 2, .Empty, sequenceLiteral [.LocalGet .Zero]⟩] []

theorem raw_alias_replay :
    wasm.replay rawAliasConfig (tapeFromCells rawAliasCells) =
      Result.ok (.Ok (rawAliasOutput, contextFinal rawAliasCells)) := by
  unfold rawAliasConfig rawAliasCells rawAliasOutput contextOutput contextFinal contextRef contextVoidGroup contextVoid
  wasm_replay_run

def exportedRefConfig : wasm.Config :=
  ⟨naturalLiteral 1, naturalLiteral 1, .Zero, .Zero, .Zero, naturalLiteral 1,
    naturalLiteral 1, .Zero, .Zero, .Zero, naturalLiteral 17⟩
def exportedRefCells : List U64 :=
  [1#u64, 1#u64, 0#u64, 0#u64, 0#u64, 0#u64, 1#u64, 0#u64, 1#u64, 0#u64,
   0#u64, 15#u64, 0#u64, 0#u64]
def exportedRefOutput : wasm.ast.Module := contextOutput [contextVoidGroup]
  [⟨.Zero, .Empty, sequenceLiteral [.RefFunc .Zero, .Drop]⟩]
  [⟨sequenceLiteral [101#u8, 48#u8], .Zero⟩]

theorem exported_ref_replay :
    wasm.replay exportedRefConfig (tapeFromCells exportedRefCells) =
      Result.ok (.Ok (exportedRefOutput, contextFinal exportedRefCells)) := by
  unfold exportedRefConfig exportedRefCells exportedRefOutput contextOutput contextFinal contextVoidGroup contextVoid
  wasm_replay_run


/-- Distinct raw indices retain closed equality through repeated shared dependencies. -/
theorem closed_shared_aliases_match :
    wasm.type_matching.same_definition (sequenceLiteral [contextVoidGroup, contextVoidGroup,
      ⟨sequenceLiteral [⟨.Final, none, ⟨sequenceLiteral [contextRef 0, contextRef 0], .Empty⟩⟩]⟩,
      ⟨sequenceLiteral [⟨.Final, none, ⟨sequenceLiteral [contextRef 1, contextRef 1], .Empty⟩⟩]⟩])
      (naturalLiteral 2) (naturalLiteral 3) = Result.ok (.Ok true) := by
  unfold contextVoidGroup contextVoid contextRef
  wasm_replay_run

/-- Reflexive comparison still resolves references and rejects a dangling target. -/
theorem closed_dangling_reference_rejected :
    wasm.type_matching.same_definition (sequenceLiteral [
      ⟨sequenceLiteral [⟨.Final, none, ⟨sequenceLiteral [contextRef 1], .Empty⟩⟩]⟩])
      .Zero .Zero = Result.ok (.Err wasm.choices.GenerationError.InternalInvariant) := by
  unfold contextRef
  wasm_replay_run

/-- Reusing a completed pair cannot hide an invalid reference later in the group. -/
theorem closed_later_dangling_reference_rejected :
    wasm.type_matching.same_definition (sequenceLiteral [contextVoidGroup,
      ⟨sequenceLiteral [⟨.Final, none,
        ⟨sequenceLiteral [contextRef 0, contextRef 0, contextRef 2], .Empty⟩⟩]⟩])
      (naturalLiteral 1) (naturalLiteral 1) = Result.ok (.Err wasm.choices.GenerationError.InternalInvariant) := by
  unfold contextVoidGroup contextVoid contextRef
  wasm_replay_run

end RustWasm
