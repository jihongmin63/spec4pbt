import WasmDataChoice
import WasmDataSpecification
import WasmReplayWitness
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

def dataListConfig (payloads : List String) : wasm.Config :=
  { emptyConfig with
    max_datas := naturalLiteral payloads.length
    work_limit := naturalLiteral ((dataCells payloads).length + 1) }

def dataListOutput (payloads : List String) : wasm.ast.Module :=
  { emptyOutput with datas := dataLiteral payloads }

def dataListFinal (payloads : List String) : wasm.choices.Choices :=
  replayState [] ((dataCells payloads).reverse ++ [0#u64])
    ((dataCells payloads).length + 1) 0

theorem data_literal_embed (payloads : List String) :
    datas (dataLiteral payloads) = payloads.map passiveDatum := by
  induction payloads with
  | nil => rfl
  | cons head tail ih => simp [datas, dataLiteral, passiveDatum, text_roundtrip, ih]

private theorem data_list_types (payloads : List String) :
    wasm.types.generate (dataListConfig payloads)
      (replayState (0#u64 :: dataCells payloads) [] 0 ((dataCells payloads).length + 1)) =
      Result.ok (.Ok (.Empty, .Empty,
        replayState (dataCells payloads) [0#u64] 1 (dataCells payloads).length)) :=
  generate_types_zero (dataListConfig payloads) rfl (dataCells payloads) [] 0 (dataCells payloads).length

/-- Every original list of string payloads has a full successful Rust replay. -/
theorem data_list_replay (payloads : List String) :
    wasm.replay (dataListConfig payloads) (tapeFromCells (0#u64 :: dataCells payloads)) =
      Result.ok (.Ok (dataListOutput payloads, dataListFinal payloads)) := by
  apply replay_from_build (dataListConfig payloads) _ _ (dataListFinal payloads)
    (naturalLiteral ((dataCells payloads).length + 1)) ?_ rfl
  let afterTypes := replayState (dataCells payloads) [0#u64] 1 (dataCells payloads).length
  apply build_empty_types (dataListConfig payloads) _ afterTypes afterTypes afterTypes
    (dataListFinal payloads) .Empty .Empty (dataLiteral payloads)
  · exact data_list_types payloads
  · rw [wasm.memory_import.generate]
    simp [dataListConfig, emptyConfig, wasm.natural.decrement]
  · rw [wasm.memory.generate]
    simp [dataListConfig, emptyConfig, wasm.natural.decrement]
  · have generated := data_section_replay payloads [] [0#u64] 1 0
    simpa [dataListConfig, dataListFinal, afterTypes, Nat.add_comm] using generated

theorem data_list_supported (payloads : List String) :
    ReplaySupport (dataListConfig payloads) (passiveModule payloads) := by
  refine ⟨tapeFromCells (0#u64 :: dataCells payloads), dataListOutput payloads,
    ⟨dataListFinal payloads, data_list_replay payloads⟩, ?_⟩
  simp [embed, dataListOutput, emptyOutput, passiveModule, emptyModule, memoryOnly,
    data_literal_embed, memories, sequenceValues]

theorem data_list_generated_valid (payloads : List String) :
    ReplaySupport (dataListConfig payloads) (passiveModule payloads) ∧
      SpecTec.Module_ok (passiveModule payloads) :=
  ⟨data_list_supported payloads, passive_module_ok payloads⟩

/-- The former missing-DATAS counterexample now has an actual execution witness. -/
theorem dataOnly_supported : ReplaySupport (dataListConfig [""]) dataOnly :=
  data_list_supported [""]

end RustWasm

open Lean Elab Command
run_cmd do
  for declaration in [``RustWasm.text_literal_valid, ``RustWasm.text_roundtrip,
      ``RustWasm.char_choice_decode,
      ``RustWasm.text_choice_replay, ``RustWasm.data_section_replay,
      ``RustWasm.data_literal_embed, ``RustWasm.passive_module_ok,
      ``RustWasm.data_list_replay, ``RustWasm.data_list_supported,
      ``RustWasm.data_list_generated_valid, ``RustWasm.dataOnly_supported] do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"
