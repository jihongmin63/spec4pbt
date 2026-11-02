import properties.wasm_module_ok.ReadyHeapMatchDefBase

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyHeapMatchSpecialIndexed

def specialBaseSources : List SpecTec.heaptype :=
  [.NoneHT, .NoFuncHT, .NoExnHT, .NoExternHT, .BotHT]

def specialBaseMatch (dt : SpecTec.deftype) :
    SpecTec.heaptype → Bool
  | .NoneHT => ReadyHeapMatchDefBase.readyDefBaseMatch dt .AnyHT
  | .NoFuncHT => ReadyHeapMatchDefBase.readyDefBaseMatch dt .FuncHT
  | .NoExnHT => ReadyHeapMatchDefBase.readyDefBaseMatch dt .ExnHT
  | .NoExternHT => ReadyHeapMatchDefBase.readyDefBaseMatch dt .ExternHT
  | .BotHT => true
  | _ => false

theorem special_base_def_result
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (source : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (hsource : source ∈ specialBaseSources) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES source (.DefHT dt)⟩)
      n (.success (.of (specialBaseMatch dt source))) n := by
  simp [specialBaseSources] at hsource
  rcases hsource with rfl | rfl | rfl | rfl | rfl
  · exact MatchHeaptypeBasic.match_heaptype_none_total_of_any
      c.TYPES (.DefHT dt)
      (ReadyHeapMatchDefBase.readyDefBaseMatch dt .AnyHT) n
      (ReadyHeapMatchDefBase.ready_def_base_result
        c p n dt .AnyHT hready hlookup
        (by simp [HeaptypeValidation.baseHeaptypes]))
  · exact MatchHeaptypeBasic.match_heaptype_nofunc_total_of_func
      c.TYPES (.DefHT dt)
      (ReadyHeapMatchDefBase.readyDefBaseMatch dt .FuncHT) n
      (ReadyHeapMatchDefBase.ready_def_base_result
        c p n dt .FuncHT hready hlookup
        (by simp [HeaptypeValidation.baseHeaptypes]))
  · exact MatchHeaptypeBasic.match_heaptype_noexn_total_of_exn
      c.TYPES (.DefHT dt)
      (ReadyHeapMatchDefBase.readyDefBaseMatch dt .ExnHT) n
      (ReadyHeapMatchDefBase.ready_def_base_result
        c p n dt .ExnHT hready hlookup
        (by simp [HeaptypeValidation.baseHeaptypes]))
  · exact MatchHeaptypeBasic.match_heaptype_noextern_total_of_extern
      c.TYPES (.DefHT dt)
      (ReadyHeapMatchDefBase.readyDefBaseMatch dt .ExternHT) n
      (ReadyHeapMatchDefBase.ready_def_base_result
        c p n dt .ExternHT hready hlookup
        (by simp [HeaptypeValidation.baseHeaptypes]))
  · exact MatchHeaptypeBasic.match_heaptype_bot_total
      c.TYPES (.DefHT dt) n

theorem special_base_statx_result
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (source : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (hsource : source ∈ specialBaseSources) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES source (.VarHT (.StatX p))⟩)
      n (.success (.of (specialBaseMatch dt source))) n := by
  simp [specialBaseSources] at hsource
  rcases hsource with rfl | rfl | rfl | rfl | rfl
  · exact MatchHeaptypeBasic.match_heaptype_none_total_of_any
      c.TYPES (.VarHT (.StatX p))
      (ReadyHeapMatchDefBase.readyDefBaseMatch dt .AnyHT) n
      (ReadyHeapMatchDefBase.ready_statx_base_result
        c p n dt .AnyHT hready hlookup
        (by simp [HeaptypeValidation.baseHeaptypes]))
  · exact MatchHeaptypeBasic.match_heaptype_nofunc_total_of_func
      c.TYPES (.VarHT (.StatX p))
      (ReadyHeapMatchDefBase.readyDefBaseMatch dt .FuncHT) n
      (ReadyHeapMatchDefBase.ready_statx_base_result
        c p n dt .FuncHT hready hlookup
        (by simp [HeaptypeValidation.baseHeaptypes]))
  · exact MatchHeaptypeBasic.match_heaptype_noexn_total_of_exn
      c.TYPES (.VarHT (.StatX p))
      (ReadyHeapMatchDefBase.readyDefBaseMatch dt .ExnHT) n
      (ReadyHeapMatchDefBase.ready_statx_base_result
        c p n dt .ExnHT hready hlookup
        (by simp [HeaptypeValidation.baseHeaptypes]))
  · exact MatchHeaptypeBasic.match_heaptype_noextern_total_of_extern
      c.TYPES (.VarHT (.StatX p))
      (ReadyHeapMatchDefBase.readyDefBaseMatch dt .ExternHT) n
      (ReadyHeapMatchDefBase.ready_statx_base_result
        c p n dt .ExternHT hready hlookup
        (by simp [HeaptypeValidation.baseHeaptypes]))
  · exact MatchHeaptypeBasic.match_heaptype_bot_total
      c.TYPES (.VarHT (.StatX p)) n

end properties.wasm_module_ok.ReadyHeapMatchSpecialIndexed
