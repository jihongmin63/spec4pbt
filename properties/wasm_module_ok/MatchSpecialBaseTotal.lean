import properties.wasm_module_ok.MatchBaseDefTotal
import properties.wasm_module_ok.HeaptypeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchSpecialBaseTotal

open properties.wasm_module_ok.HeaptypeValidation

def fixedBaseTargets : List SpecTec.heaptype :=
  [.AnyHT, .FuncHT, .ExnHT, .ExternHT]

theorem fixed_target_simple
    (t : SpecTec.heaptype) (h : t ∈ fixedBaseTargets) :
    t ∈ MatchBaseDefTotal.simpleBaseHeaptypes := by
  simp [fixedBaseTargets] at h
  rcases h with rfl | rfl | rfl | rfl
  all_goals simp [MatchBaseDefTotal.simpleBaseHeaptypes]

theorem none_fixed_target_total
    (dts : List SpecTec.deftype) (t : SpecTec.heaptype) (n : Nat)
    (ht : t ∈ fixedBaseTargets) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          dts .NoneHT t⟩)
        n (.success (.of r)) n := by
  obtain ⟨r, hresult⟩ := MatchBaseDefTotal.match_simple_base_total
    dts t .AnyHT n (fixed_target_simple t ht)
  exact ⟨r, MatchHeaptypeBasic.match_heaptype_none_total_of_any
    dts t r n hresult⟩

theorem nofunc_fixed_target_total
    (dts : List SpecTec.deftype) (t : SpecTec.heaptype) (n : Nat)
    (ht : t ∈ fixedBaseTargets) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          dts .NoFuncHT t⟩)
        n (.success (.of r)) n := by
  obtain ⟨r, hresult⟩ := MatchBaseDefTotal.match_simple_base_total
    dts t .FuncHT n (fixed_target_simple t ht)
  exact ⟨r, MatchHeaptypeBasic.match_heaptype_nofunc_total_of_func
    dts t r n hresult⟩

theorem noexn_fixed_target_total
    (dts : List SpecTec.deftype) (t : SpecTec.heaptype) (n : Nat)
    (ht : t ∈ fixedBaseTargets) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          dts .NoExnHT t⟩)
        n (.success (.of r)) n := by
  obtain ⟨r, hresult⟩ := MatchBaseDefTotal.match_simple_base_total
    dts t .ExnHT n (fixed_target_simple t ht)
  exact ⟨r, MatchHeaptypeBasic.match_heaptype_noexn_total_of_exn
    dts t r n hresult⟩

theorem noextern_fixed_target_total
    (dts : List SpecTec.deftype) (t : SpecTec.heaptype) (n : Nat)
    (ht : t ∈ fixedBaseTargets) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          dts .NoExternHT t⟩)
        n (.success (.of r)) n := by
  obtain ⟨r, hresult⟩ := MatchBaseDefTotal.match_simple_base_total
    dts t .ExternHT n (fixed_target_simple t ht)
  exact ⟨r, MatchHeaptypeBasic.match_heaptype_noextern_total_of_extern
    dts t r n hresult⟩

theorem fixed_target_all_base_sources
    (dts : List SpecTec.deftype) (ht target : SpecTec.heaptype)
    (n : Nat)
    (hbase : ht ∈ baseHeaptypes)
    (htarget : target ∈ fixedBaseTargets) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          dts ht target⟩)
        n (.success (.of r)) n := by
  simp [baseHeaptypes] at hbase
  rcases hbase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact MatchBaseDefTotal.match_simple_base_total dts .AnyHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact none_fixed_target_total dts target n htarget
  · exact MatchBaseDefTotal.match_simple_base_total dts .EqHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total dts .I31HT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total dts .StructHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total dts .ArrayHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total dts .FuncHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact nofunc_fixed_target_total dts target n htarget
  · exact MatchBaseDefTotal.match_simple_base_total dts .ExnHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact noexn_fixed_target_total dts target n htarget
  · exact MatchBaseDefTotal.match_simple_base_total dts .ExternHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact noextern_fixed_target_total dts target n htarget
  · exact ⟨true, MatchHeaptypeBasic.match_heaptype_bot_total dts target n⟩

theorem match_base_base_total
    (dts : List SpecTec.deftype) (ht target : SpecTec.heaptype)
    (n : Nat)
    (hsource : ht ∈ baseHeaptypes)
    (htarget : target ∈ baseHeaptypes) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          dts ht target⟩)
        n (.success (.of r)) n := by
  simp [baseHeaptypes] at hsource
  rcases hsource with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact MatchBaseDefTotal.match_simple_base_total dts .AnyHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hfixed⟩ := fixed_target_all_base_sources
      dts target .AnyHT n htarget (by simp [fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_none_total_of_any
      dts target r n hfixed⟩
  · exact MatchBaseDefTotal.match_simple_base_total dts .EqHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total dts .I31HT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total dts .StructHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total dts .ArrayHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total dts .FuncHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hfixed⟩ := fixed_target_all_base_sources
      dts target .FuncHT n htarget (by simp [fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_nofunc_total_of_func
      dts target r n hfixed⟩
  · exact MatchBaseDefTotal.match_simple_base_total dts .ExnHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hfixed⟩ := fixed_target_all_base_sources
      dts target .ExnHT n htarget (by simp [fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_noexn_total_of_exn
      dts target r n hfixed⟩
  · exact MatchBaseDefTotal.match_simple_base_total dts .ExternHT target n
      (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hfixed⟩ := fixed_target_all_base_sources
      dts target .ExternHT n htarget (by simp [fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_noextern_total_of_extern
      dts target r n hfixed⟩
  · exact ⟨true, MatchHeaptypeBasic.match_heaptype_bot_total dts target n⟩

end properties.wasm_module_ok.MatchSpecialBaseTotal
