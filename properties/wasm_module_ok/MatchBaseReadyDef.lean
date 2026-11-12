import properties.wasm_module_ok.MatchReadyDefFixed

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchBaseReadyDef

theorem match_base_def_total
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (ht : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt)
    (hbase : ht ∈ HeaptypeValidation.baseHeaptypes) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
          c.TYPES ht (.DefHT dt)⟩)
        n (.success (.of r)) n := by
  simp [HeaptypeValidation.baseHeaptypes] at hbase
  rcases hbase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .AnyHT
      (.DefHT dt) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hinner⟩ := MatchReadyDefFixed.ready_def_fixed_match_total
      c q n dt .AnyHT hready hlookup
      (by simp [MatchSpecialBaseTotal.fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_none_total_of_any
      c.TYPES (.DefHT dt) r n hinner⟩
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .EqHT
      (.DefHT dt) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .I31HT
      (.DefHT dt) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .StructHT
      (.DefHT dt) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .ArrayHT
      (.DefHT dt) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .FuncHT
      (.DefHT dt) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hinner⟩ := MatchReadyDefFixed.ready_def_fixed_match_total
      c q n dt .FuncHT hready hlookup
      (by simp [MatchSpecialBaseTotal.fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_nofunc_total_of_func
      c.TYPES (.DefHT dt) r n hinner⟩
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .ExnHT
      (.DefHT dt) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hinner⟩ := MatchReadyDefFixed.ready_def_fixed_match_total
      c q n dt .ExnHT hready hlookup
      (by simp [MatchSpecialBaseTotal.fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_noexn_total_of_exn
      c.TYPES (.DefHT dt) r n hinner⟩
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .ExternHT
      (.DefHT dt) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hinner⟩ := MatchReadyDefFixed.ready_def_fixed_match_total
      c q n dt .ExternHT hready hlookup
      (by simp [MatchSpecialBaseTotal.fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_noextern_total_of_extern
      c.TYPES (.DefHT dt) r n hinner⟩
  · exact ⟨true, MatchHeaptypeBasic.match_heaptype_bot_total
      c.TYPES (.DefHT dt) n⟩

theorem match_statx_fixed_total
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (htarget : target ∈ MatchSpecialBaseTotal.fixedBaseTargets) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
          c.TYPES (.VarHT (.StatX p)) target⟩)
        n (.success (.of r)) n := by
  obtain ⟨r, hinner⟩ := MatchReadyDefFixed.ready_def_fixed_match_total
    c p n dt target hready hlookup htarget
  exact ⟨r, MatchHeaptypeBasic.match_heaptype_statx_total_of_def
    c.TYPES p dt target r n hlookup hinner⟩

theorem match_statx_base_total
    (c : SpecTec.context) (p n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[p]? = some dt)
    (hbase : target ∈ HeaptypeValidation.baseHeaptypes) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
          c.TYPES (.VarHT (.StatX p)) target⟩)
        n (.success (.of r)) n := by
  obtain ⟨r, hinner⟩ := MatchReadyDefFixed.ready_def_all_base_total
    c p n dt target hready hlookup hbase
  exact ⟨r, MatchHeaptypeBasic.match_heaptype_statx_total_of_def
    c.TYPES p dt target r n hlookup hinner⟩

theorem match_base_statx_total
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (ht : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt)
    (hbase : ht ∈ HeaptypeValidation.baseHeaptypes) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
          c.TYPES ht (.VarHT (.StatX q))⟩)
        n (.success (.of r)) n := by
  simp [HeaptypeValidation.baseHeaptypes] at hbase
  rcases hbase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .AnyHT
      (.VarHT (.StatX q)) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hinner⟩ := match_statx_fixed_total
      c q n dt .AnyHT hready hlookup
      (by simp [MatchSpecialBaseTotal.fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_none_total_of_any
      c.TYPES (.VarHT (.StatX q)) r n hinner⟩
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .EqHT
      (.VarHT (.StatX q)) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .I31HT
      (.VarHT (.StatX q)) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .StructHT
      (.VarHT (.StatX q)) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .ArrayHT
      (.VarHT (.StatX q)) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .FuncHT
      (.VarHT (.StatX q)) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hinner⟩ := match_statx_fixed_total
      c q n dt .FuncHT hready hlookup
      (by simp [MatchSpecialBaseTotal.fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_nofunc_total_of_func
      c.TYPES (.VarHT (.StatX q)) r n hinner⟩
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .ExnHT
      (.VarHT (.StatX q)) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hinner⟩ := match_statx_fixed_total
      c q n dt .ExnHT hready hlookup
      (by simp [MatchSpecialBaseTotal.fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_noexn_total_of_exn
      c.TYPES (.VarHT (.StatX q)) r n hinner⟩
  · exact MatchBaseDefTotal.match_simple_base_total c.TYPES .ExternHT
      (.VarHT (.StatX q)) n (by simp [MatchBaseDefTotal.simpleBaseHeaptypes])
  · obtain ⟨r, hinner⟩ := match_statx_fixed_total
      c q n dt .ExternHT hready hlookup
      (by simp [MatchSpecialBaseTotal.fixedBaseTargets])
    exact ⟨r, MatchHeaptypeBasic.match_heaptype_noextern_total_of_extern
      c.TYPES (.VarHT (.StatX q)) r n hinner⟩
  · exact ⟨true, MatchHeaptypeBasic.match_heaptype_bot_total
      c.TYPES (.VarHT (.StatX q)) n⟩


end properties.wasm_module_ok.MatchBaseReadyDef
