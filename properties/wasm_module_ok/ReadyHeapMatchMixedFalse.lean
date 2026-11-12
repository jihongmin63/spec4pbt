import properties.wasm_module_ok.ReadyHeapMatchIndexed
import properties.wasm_module_ok.ReadyHeapMatchSimpleBase
import properties.wasm_module_ok.MatchReadyDefFixed

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyHeapMatchMixedFalse

/-- The translated definition matcher returns false for these eight base
targets regardless of the ready definition's expanded structural shape. -/
def nonstructuralTarget (target : SpecTec.heaptype) : Bool :=
  decide (target ∈ MatchReadyDefFixed.nonstructuralBaseTargets)

theorem nonstructuralTarget_true_iff (target : SpecTec.heaptype) :
    nonstructuralTarget target = true ↔
      target ∈ MatchReadyDefFixed.nonstructuralBaseTargets := by
  simp [nonstructuralTarget]

theorem ready_def_nonstructural_result
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (htarget : nonstructuralTarget target = true) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        c.TYPES (.DefHT dt) target⟩)
      n (.success (.of false)) n := by
  exact MatchReadyDefFixed.ready_def_nonstructural_base_false
    c p n dt target hready hlookup
    ((nonstructuralTarget_true_iff target).mp htarget)

theorem ready_statx_nonstructural_result
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (htarget : nonstructuralTarget target = true) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        c.TYPES (.VarHT (.StatX p)) target⟩)
      n (.success (.of false)) n := by
  apply MatchHeaptypeBasic.match_heaptype_statx_total_of_def
    c.TYPES p dt target false n hlookup
  exact ready_def_nonstructural_result
    c p n dt target hready hlookup htarget

end properties.wasm_module_ok.ReadyHeapMatchMixedFalse
