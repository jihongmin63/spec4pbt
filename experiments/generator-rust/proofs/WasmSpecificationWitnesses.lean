import WasmContract
import Lean

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

namespace RustWasm
open SpecTecExecution

/- Construct concrete ordered execution derivations; the kernel checks the result. -/
syntax "spec_run" : tactic
macro_rules
| `(tactic| spec_run) => `(tactic|
  first
  | exact Eval.pure _
  | exact Eval.unmatch
  | (apply Eval.guard_true; decide)
  | (apply Eval.guard_false; decide)
  | (apply Eval.call; spec_run)
  | (apply Eval.bind_success; spec_run; spec_run)
  | (apply Eval.bind_unmatch; spec_run)
  | (apply Eval.orElse_success; spec_run)
  | (apply Eval.orElse_unmatch; spec_run; spec_run))

def memoryOnly : SpecTec.module where
  TYPES := []
  GLOBALS := []
  TABLES := []
  MEMS := [⟨.MemoryT .I32AT ⟨0, none⟩⟩]
  TAGS := []
  FUNCS := []
  START := none
  ELEMS := []
  DATAS := []
  IMPORTS := []
  EXPORTS := []

theorem memoryOnly_ok : SpecTec.Module_ok memoryOnly := by
  refine ⟨0, ?_⟩
  spec_run

/-- The positive specification witness used by the concrete replay proof. -/
def emptyModule : SpecTec.module := { memoryOnly with MEMS := [] }

theorem emptyModule_ok : SpecTec.Module_ok emptyModule := by
  refine ⟨0, ?_⟩
  spec_run

/-- The original passive-data witness, also used by the data extension. -/
def dataOnly : SpecTec.module := { emptyModule with DATAS := [⟨"", .Passive⟩] }

theorem dataOnly_ok : SpecTec.Module_ok dataOnly := by
  refine ⟨0, ?_⟩
  spec_run

/-- The original memory-import witness, used by the import extension. -/
def importsOnly : SpecTec.module :=
  { emptyModule with IMPORTS := [⟨[], [], .MemImport (.MemoryT .I32AT ⟨0, none⟩)⟩] }

theorem importsOnly_ok : SpecTec.Module_ok importsOnly := by
  refine ⟨0, ?_⟩
  spec_run

/-- Globals remain outside the current Rust construction core. -/
def globalsOnly : SpecTec.module :=
  { emptyModule with GLOBALS := [⟨.GlobalT .Cons (.NumT .I32T), [.CONST (.I32 0)]⟩] }

theorem globalsOnly_ok : SpecTec.Module_ok globalsOnly := by
  refine ⟨0, ?_⟩
  spec_run

theorem globalsOnly_not_generated (config : generator_rust.wasm.Config) :
    ¬ ReplaySupport config globalsOnly := by
  rintro ⟨_, output, _, equal⟩
  have impossible := congrArg SpecTec.module.GLOBALS equal
  simp [embed, globalsOnly] at impossible

theorem not_complete : ¬ Completeness := by
  intro complete
  obtain ⟨config, generated⟩ := complete globalsOnly globalsOnly_ok
  exact globalsOnly_not_generated config generated

end RustWasm
