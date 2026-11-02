import properties.wasm_module_ok.ReadyMatchReachablePairs
import properties.wasm_module_ok.MatchReadyDefFixed

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyMatchReversePairs

theorem ready_reverse_pair_total
    (c : SpecTec.context) (source target : SpecTec.heaptype)
    (n : Nat) (hready : CandidateTypeReady.Ready c)
    (hsource : source ∈ HeaptypeValidation.baseHeaptypes ∨
      ∃ (q : Nat) (dt : SpecTec.deftype),
        source = .DefHT dt ∧ c.TYPES[q]? = some dt)
    (htarget : target ∈ HeaptypeValidation.baseHeaptypes ∨
      ∃ (p : Nat) (dt : SpecTec.deftype),
        target = .VarHT (.StatX p) ∧ c.TYPES[p]? = some dt) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES source target⟩)
        n (.success (.of r)) n := by
  rcases hsource with hbase | ⟨q, dtQ, rfl, hQ⟩
  · rcases htarget with htargetBase | ⟨p, dtP, rfl, hP⟩
    · exact MatchSpecialBaseTotal.match_base_base_total
        c.TYPES source target n hbase htargetBase
    · exact MatchBaseReadyDef.match_base_statx_total
        c p n dtP source hready hP hbase
  · rcases htarget with htargetBase | ⟨p, dtP, rfl, hP⟩
    · exact MatchReadyDefFixed.ready_def_all_base_total
        c q n dtQ target hready hQ htargetBase
    · have hq : q < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hQ).1
      have hp : p < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hP).1
      exact ⟨ValidatedMatchIndexFuel.matchIndex c q p,
        ReadyMatchHeaptypeVar.ready_match_heaptype_def_statx_total
          c q p n dtQ dtP hready hq hp hQ hP⟩

theorem static_structural_reverse_heap_pairs_total
    (c : SpecTec.context) (y : SpecTec.typeidx)
    (sourceFin : SpecTec.final) (sourceHts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (dt : SpecTec.deftype)
    (subStart subFinish : Nat)
    (hsub : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_ok c
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
      ∀ targetHt,
        targetHt ∈ ReadyMatchReachability.sourceHeaptypes strtU →
      ∀ sourceHt,
        sourceHt ∈ ReadyMatchReachability.sourceHeaptypes strt →
      ∀ n, ∃ r : Bool,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
            c.TYPES targetHt sourceHt⟩)
          n (.success (.of r)) n := by
  obtain ⟨fin, hts, strtU, hunroll, hsource, htarget⟩ :=
    SubtypeStaticMatchTrace.static_pair_classes_before_match
      c y sourceFin sourceHts strt dt subStart subFinish
      hsub hnested hlookup
  refine ⟨fin, hts, strtU, hunroll, ?_⟩
  intro targetHt htargetMem sourceHt hsourceMem n
  apply ready_reverse_pair_total c targetHt sourceHt n hready
  · rcases htarget targetHt htargetMem with hbase |
      ⟨dtQ, q, hindex, heq⟩
    · exact Or.inl hbase
    · exact Or.inr ⟨q, dtQ, heq,
        (ReadyMatchHeaptypeIndex.indexOfDeftype_sound
          c.TYPES dtQ q hindex).2.1⟩
  · rcases hsource sourceHt hsourceMem with hbase | ⟨p, dtP, hP, heq⟩
    · exact Or.inl hbase
    · exact Or.inr ⟨p, dtP, heq, hP⟩

end properties.wasm_module_ok.ReadyMatchReversePairs
