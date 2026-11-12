import properties.wasm_module_ok.CandidateValMatch
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateValMembership

theorem heap_candidate_in_table
    (c : SpecTec.context) (ht : SpecTec.heaptype)
    (h : ht ∈ FiniteValidTypes.heapCandidates c) :
    CandidateHeapMatch.InTable c ht := by
  simp only [FiniteValidTypes.heapCandidates, List.mem_append,
    List.mem_map, List.mem_range] at h
  rcases h with hbase | ⟨p, hbound, rfl⟩
  · exact CandidateHeapMatch.InTable.base ht hbase
  · cases hget : c.TYPES[p]? with
    | none =>
        simp [hbound] at hget
    | some dt =>
        exact CandidateHeapMatch.InTable.static p dt hget

theorem valid_candidate_in_table
    (c : SpecTec.context) (t : SpecTec.valtype)
    (h : t ∈ FiniteValidTypes.validCandidates c) :
    CandidateValMatch.InTableVal c t := by
  intro ht hsource
  cases t with
  | NumT a =>
      simp [ReadyMatchReachability.sourceValHeaptypes] at hsource
  | VecT a =>
      simp [ReadyMatchReachability.sourceValHeaptypes] at hsource
  | BotT =>
      simp [ReadyMatchReachability.sourceValHeaptypes] at hsource
  | RefT ref =>
      cases ref with
      | «% %» null heap =>
          have heq : ht = heap := by
            simpa [ReadyMatchReachability.sourceValHeaptypes] using hsource
          subst ht
          simp only [FiniteValidTypes.validCandidates,
            List.mem_append] at h
          rcases h with hprim | href
          · simp at hprim
          · exact heap_candidate_in_table c heap
              ((FiniteValidTypes.refCandidates_spec c null heap).mp href)

theorem table_definition_in_table
    (c : SpecTec.context) (dt : SpecTec.deftype)
    (h : dt ∈ c.TYPES) (null : SpecTec.null) :
    CandidateValMatch.InTableVal c
      (.RefT (.«% %» null (.DefHT dt))) := by
  obtain ⟨p, hget⟩ := List.mem_iff_getElem?.mp h
  intro ht hsource
  have heq : ht = SpecTec.heaptype.DefHT dt := by
    simpa [ReadyMatchReachability.sourceValHeaptypes] using hsource
  subst ht
  exact CandidateHeapMatch.InTable.definition p dt hget

end properties.wasm_module_ok.CandidateValMembership
