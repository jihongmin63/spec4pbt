import WasmMemoryWitness
import WasmMemoryProperties
import WasmMemorySpecification
import WasmMemorySoundness
import WasmDomainWitnesses
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Check dependencies of statements as well as proved theorems. -/
run_cmd do
  let declarations := [
    ``RustWasm.embed, ``RustWasm.ReplayReturns, ``RustWasm.SampleReturns,
    ``RustWasm.Soundness, ``RustWasm.SamplingSoundness,
    ``RustWasm.Completeness, ``RustWasm.SamplingCompleteness, ``RustWasm.CompleteFor,
    ``RustWasm.memoryOnly_ok, ``RustWasm.dataOnly_ok, ``RustWasm.importsOnly_ok,
    ``RustWasm.globalsOnly_ok, ``RustWasm.globalsOnly_not_generated, ``RustWasm.not_complete,
    ``RustWasm.memory_import_names_ok, ``RustWasm.passive_data_payload_ok,
    ``RustWasm.emptyModule_ok, ``RustWasm.empty_replay,
    ``RustWasm.empty_supported, ``RustWasm.empty_generated_valid,
    ``RustWasm.copy_natural_eq, ``RustWasm.increment_total,
    ``RustWasm.decrement_total, ``RustWasm.natural_representable,
    ``RustWasm.tape_roundtrip, ``RustWasm.length_from_total, ``RustWasm.word_replay, ``RustWasm.word_replay_total,
    ``RustWasm.pick_word_replay, ``RustWasm.pick_replay, ``RustWasm.memory_limits_valid,
    ``RustWasm.memory_bounded_valid, ``RustWasm.memories_list,
    ``RustWasm.memory_replay, ``RustWasm.memory_supported,
    ``RustWasm.memory_generated_valid,
    ``RustWasm.naturalLiteral_value, ``RustWasm.increment_literal, ``RustWasm.decrement_literal,
    ``RustWasm.pick_word_state, ``RustWasm.pick_state,
    ``RustWasm.memory_none_replay, ``RustWasm.memory_some_replay,
    ``RustWasm.memory_section_replay, ``RustWasm.memory_list_replay,
    ``RustWasm.memory_list_supported, ``RustWasm.memories_bounded_execute,
    ``RustWasm.memory_list_valid, ``RustWasm.memory_list_generated_valid,
    ``RustWasm.memory_constructor_sound, ``RustWasm.memory_constructor_valid]
  for declaration in declarations do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"
