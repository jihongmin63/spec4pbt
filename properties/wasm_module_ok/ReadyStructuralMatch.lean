import properties.wasm_module_ok.ReadyMatchReachablePairs
import properties.wasm_module_ok.ReadyMatchReversePairs
import properties.wasm_module_ok.MatchStrtypeLocal

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyStructuralMatch

theorem static_structural_match_total
    (c : SpecTec.context) (y : SpecTec.typeidx)
    (sourceFin : SpecTec.final) (sourceHts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (dt : SpecTec.deftype)
    (subStart subFinish n : Nat)
    (hsub : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_ok c
          (.SubT sourceFin sourceHts strt)⟩)
      subStart (.success (.of ())) subFinish)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[y]? = some dt) :
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
      properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
        some (.SubT fin hts strtU) ∧
      ∃ result : Bool,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Bool,
            SpecTec.Call.«$match_strtype» c.TYPES strt strtU⟩)
          n (.success (.of result)) n := by
  classical
  obtain ⟨fin, hts, strtU, hunroll, hforward⟩ :=
    ReadyMatchReachablePairs.static_structural_heap_pairs_total
      c y sourceFin sourceHts strt dt subStart subFinish
      hsub hnested hready hlookup
  obtain ⟨finR, htsR, strtR, hunrollR, hreverse⟩ :=
    ReadyMatchReversePairs.static_structural_reverse_heap_pairs_total
      c y sourceFin sourceHts strt dt subStart subFinish
      hsub hnested hready hlookup
  rw [hunroll] at hunrollR
  cases hunrollR
  let relevant : SpecTec.heaptype → SpecTec.heaptype → Prop := fun h1 h2 =>
    (h1 ∈ ReadyMatchReachability.sourceHeaptypes strt ∧
      h2 ∈ ReadyMatchReachability.sourceHeaptypes strtU) ∨
    (h1 ∈ ReadyMatchReachability.sourceHeaptypes strtU ∧
      h2 ∈ ReadyMatchReachability.sourceHeaptypes strt)
  have htotal : ∀ h1 h2, relevant h1 h2 →
      ∃ result : Bool,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Bool,
            SpecTec.Call.«$match_heaptype» c.TYPES h1 h2⟩)
          n (.success (.of result)) n := by
    intro h1 h2 hp
    rcases hp with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact hforward h1 hs h2 ht n
    · exact hreverse h1 ht h2 hs n
  let heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool :=
    fun h1 h2 =>
      if hp : relevant h1 h2 then Classical.choose (htotal h1 h2 hp)
      else false
  have hpair : ∀ h1 h2, relevant h1 h2 →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» c.TYPES h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n := by
    intro h1 h2 hp
    simpa [heapMatch, dif_pos hp] using
      (Classical.choose_spec (htotal h1 h2 hp))
  refine ⟨fin, hts, strtU, hunroll,
    MatchStrtypeConditional.strMatch heapMatch strt strtU, ?_⟩
  apply MatchStrtypeLocal.match_strtype_total_of_local_heap_at
  · intro h1 h2 hs ht
    exact hpair h1 h2 (Or.inl ⟨hs, ht⟩)
  · intro h2 h1 ht hs
    exact hpair h2 h1 (Or.inr ⟨ht, hs⟩)

end properties.wasm_module_ok.ReadyStructuralMatch
