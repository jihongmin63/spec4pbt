import properties.wasm_module_ok.ReadyHeapMatchMixedFalse

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyHeapMatchDefBase

/-- Exact finite result for a ready indexed definition against a base target. -/
def readyDefBaseMatch (dt : SpecTec.deftype) : SpecTec.heaptype → Bool
  | .AnyHT => MatchReadyDefFixed.anyBaseMatch dt
  | .EqHT => MatchReadyDefFixed.eqBaseMatch dt
  | .StructHT => MatchReadyDefFixed.structBaseMatch dt
  | .ArrayHT => MatchReadyDefFixed.arrayBaseMatch dt
  | .FuncHT => MatchReadyDefFixed.funcBaseMatch dt
  | _ => false

theorem ready_def_base_result
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : target ∈ HeaptypeValidation.baseHeaptypes) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) target⟩)
      n (.success (.of (readyDefBaseMatch dt target))) n := by
  simp [HeaptypeValidation.baseHeaptypes] at hbase
  rcases hbase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact MatchReadyDefFixed.ready_def_any_result c p n dt hready hlookup
  · exact ReadyHeapMatchMixedFalse.ready_def_nonstructural_result
      c p n dt .NoneHT hready hlookup (by
        simp [ReadyHeapMatchMixedFalse.nonstructuralTarget,
          MatchReadyDefFixed.nonstructuralBaseTargets])
  · exact MatchReadyDefFixed.ready_def_eq_result c p n dt hready hlookup
  · exact ReadyHeapMatchMixedFalse.ready_def_nonstructural_result
      c p n dt .I31HT hready hlookup (by
        simp [ReadyHeapMatchMixedFalse.nonstructuralTarget,
          MatchReadyDefFixed.nonstructuralBaseTargets])
  · exact MatchReadyDefFixed.ready_def_struct_result c p n dt hready hlookup
  · exact MatchReadyDefFixed.ready_def_array_result c p n dt hready hlookup
  · exact MatchReadyDefFixed.ready_def_func_result c p n dt hready hlookup
  · exact ReadyHeapMatchMixedFalse.ready_def_nonstructural_result
      c p n dt .NoFuncHT hready hlookup (by
        simp [ReadyHeapMatchMixedFalse.nonstructuralTarget,
          MatchReadyDefFixed.nonstructuralBaseTargets])
  · exact ReadyHeapMatchMixedFalse.ready_def_nonstructural_result
      c p n dt .ExnHT hready hlookup (by
        simp [ReadyHeapMatchMixedFalse.nonstructuralTarget,
          MatchReadyDefFixed.nonstructuralBaseTargets])
  · exact ReadyHeapMatchMixedFalse.ready_def_nonstructural_result
      c p n dt .NoExnHT hready hlookup (by
        simp [ReadyHeapMatchMixedFalse.nonstructuralTarget,
          MatchReadyDefFixed.nonstructuralBaseTargets])
  · exact ReadyHeapMatchMixedFalse.ready_def_nonstructural_result
      c p n dt .ExternHT hready hlookup (by
        simp [ReadyHeapMatchMixedFalse.nonstructuralTarget,
          MatchReadyDefFixed.nonstructuralBaseTargets])
  · exact ReadyHeapMatchMixedFalse.ready_def_nonstructural_result
      c p n dt .NoExternHT hready hlookup (by
        simp [ReadyHeapMatchMixedFalse.nonstructuralTarget,
          MatchReadyDefFixed.nonstructuralBaseTargets])
  · exact ReadyHeapMatchMixedFalse.ready_def_nonstructural_result
      c p n dt .BotHT hready hlookup (by
        simp [ReadyHeapMatchMixedFalse.nonstructuralTarget,
          MatchReadyDefFixed.nonstructuralBaseTargets])

theorem ready_statx_base_result
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : target ∈ HeaptypeValidation.baseHeaptypes) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.VarHT (.StatX p)) target⟩)
      n (.success (.of (readyDefBaseMatch dt target))) n := by
  apply MatchHeaptypeBasic.match_heaptype_statx_total_of_def
    c.TYPES p dt target (readyDefBaseMatch dt target) n hlookup
  exact ready_def_base_result c p n dt target hready hlookup hbase

end properties.wasm_module_ok.ReadyHeapMatchDefBase
