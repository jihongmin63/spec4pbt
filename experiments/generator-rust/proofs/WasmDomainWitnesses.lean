import WasmSpecificationWitnesses

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

namespace RustWasm
open SpecTecExecution

/- Reduce guards before deciding: module names and payloads can remain symbolic. -/
syntax "domain_run" : tactic
macro_rules
| `(tactic| domain_run) => `(tactic|
  first
  | exact Eval.pure _
  | exact Eval.unmatch
  | (apply Eval.guard_true; first | rfl | decide)
  | (apply Eval.guard_false; change ¬ false = true; decide)
  | (apply Eval.call; domain_run)
  | (apply Eval.bind_success; domain_run; domain_run)
  | (apply Eval.bind_unmatch; domain_run)
  | (apply Eval.orElse_success; domain_run)
  | (apply Eval.orElse_unmatch; domain_run; domain_run))

def memoryImportModule (moduleName itemName : List Nat) : SpecTec.module :=
  { emptyModule with IMPORTS := [⟨moduleName, itemName, .MemImport (.MemoryT .I32AT ⟨0, none⟩)⟩] }

/-- The exact target accepts arbitrary natural-number names, without byte or length bounds. -/
theorem memory_import_names_ok (moduleName itemName : List Nat) :
    SpecTec.Module_ok (memoryImportModule moduleName itemName) := by
  refine ⟨0, ?_⟩
  domain_run

def passiveDataModule (payload : String) : SpecTec.module :=
  { emptyModule with DATAS := [⟨payload, .Passive⟩] }

/-- Original validation imposes no restriction on a passive segment's string payload. -/
theorem passive_data_payload_ok (payload : String) :
    SpecTec.Module_ok (passiveDataModule payload) := by
  refine ⟨0, ?_⟩
  domain_run

end RustWasm
