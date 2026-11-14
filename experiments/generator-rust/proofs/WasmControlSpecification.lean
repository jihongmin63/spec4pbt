import WasmGroundEvaluation

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace RustWasm
open GroundEvaluation

/-- Preserve the exact control instruction sequence in the original AST. -/
def controlModule (results : List SpecTec.valtype) (body : List SpecTec.instr) : SpecTec.module :=
  { TYPES := [.RecT [.SubT .Final [] (.DefFuncT (.FuncT [] results))]]
    FUNCS := [⟨0, [], body⟩]
    GLOBALS := []
    TABLES := []
    MEMS := []
    TAGS := []
    START := none
    ELEMS := []
    DATAS := []
    IMPORTS := []
    EXPORTS := [] }

def unreachableAddModule : SpecTec.module :=
  controlModule [.NumT .I32T] [.UNREACHABLE, .BINOP (.I32 .IAdd)]

def unreachableOperandModule : SpecTec.module :=
  controlModule [.NumT .I32T] [.UNREACHABLE, .CONST (.I32 7), .BINOP (.I32 .IAdd)]

def unreachablePredecessorModule : SpecTec.module :=
  controlModule [] [.CONST (.I64 7), .UNREACHABLE]

def loopLabelModule : SpecTec.module :=
  controlModule [.NumT .I32T] [.LOOP (.ValBlockType (some (.NumT .I32T))) [.BR 0]]

def outerLabelModule : SpecTec.module :=
  controlModule [.NumT .I32T] [.BLOCK (.ValBlockType (some (.NumT .I32T)))
    [.BLOCK (.ValBlockType (some (.NumT .I32T))) [.CONST (.I32 7), .BR 1]]]

def branchIfModule : SpecTec.module :=
  controlModule [.NumT .I32T] [.CONST (.I32 7), .CONST (.I32 0), .BR_IF 0]

theorem unreachable_add_module_ok : SpecTec.Module_ok unreachableAddModule := by
  refine ⟨0, ?_⟩
  ground_spec_run

theorem unreachable_operand_module_ok : SpecTec.Module_ok unreachableOperandModule := by
  refine ⟨0, ?_⟩
  ground_spec_run

theorem unreachable_predecessor_module_ok : SpecTec.Module_ok unreachablePredecessorModule := by
  refine ⟨0, ?_⟩
  ground_spec_run

theorem loop_label_module_ok : SpecTec.Module_ok loopLabelModule := by
  refine ⟨0, ?_⟩
  ground_spec_run

theorem outer_label_module_ok : SpecTec.Module_ok outerLabelModule := by
  refine ⟨0, ?_⟩
  ground_spec_run

theorem branch_if_module_ok : SpecTec.Module_ok branchIfModule := by
  refine ⟨0, ?_⟩
  ground_spec_run

end RustWasm
