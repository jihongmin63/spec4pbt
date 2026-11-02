import properties.wasm_module_ok.MatchBaseReadyDef
import properties.wasm_module_ok.ReadyMatchHeaptypeVar
import properties.wasm_module_ok.SubtypeStaticMatchTrace

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyMatchReachablePairs

theorem ready_reachable_pair_total
    (c : SpecTec.context) (source target : SpecTec.heaptype)
    (n : Nat) (hready : CandidateTypeReady.Ready c)
    (hsource : source ∈ HeaptypeValidation.baseHeaptypes ∨
      ∃ (p : Nat) (dt : SpecTec.deftype),
        source = .VarHT (.StatX p) ∧ c.TYPES[p]? = some dt)
    (htarget : target ∈ HeaptypeValidation.baseHeaptypes ∨
      (∃ (q : Nat) (dt : SpecTec.deftype),
        target = .VarHT (.StatX q) ∧ c.TYPES[q]? = some dt) ∨
      (∃ (q : Nat) (dt : SpecTec.deftype),
        target = .DefHT dt ∧ c.TYPES[q]? = some dt)) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES source target⟩)
        n (.success (.of r)) n := by
  rcases hsource with hbase | ⟨p, dtP, rfl, hP⟩
  · rcases htarget with htargetBase |
      ⟨q, dtQ, rfl, hQ⟩ | ⟨q, dtQ, rfl, hQ⟩
    · exact MatchSpecialBaseTotal.match_base_base_total
        c.TYPES source target n hbase htargetBase
    · exact MatchBaseReadyDef.match_base_statx_total
        c q n dtQ source hready hQ hbase
    · exact MatchBaseReadyDef.match_base_def_total
        c q n dtQ source hready hQ hbase
  · rcases htarget with htargetBase |
      ⟨q, dtQ, rfl, hQ⟩ | ⟨q, dtQ, rfl, hQ⟩
    · exact MatchBaseReadyDef.match_statx_base_total
        c p n dtP target hready hP htargetBase
    · have hp : p < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hP).1
      have hq : q < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hQ).1
      exact ⟨ValidatedMatchIndexFuel.matchIndex c p q,
        ReadyMatchHeaptypeVar.ready_match_heaptype_statx_statx_total
          c p q n dtP dtQ hready hp hq hP hQ⟩
    · have hp : p < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hP).1
      have hq : q < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hQ).1
      exact ⟨ValidatedMatchIndexFuel.matchIndex c p q,
        ReadyMatchHeaptypeVar.ready_match_heaptype_statx_def_total
          c p q n dtP dtQ hready hp hq hP hQ⟩

theorem static_structural_heap_pairs_total
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
      ∀ sourceHt, sourceHt ∈ ReadyMatchReachability.sourceHeaptypes strt →
      ∀ targetHt, targetHt ∈ ReadyMatchReachability.sourceHeaptypes strtU →
      ∀ n, ∃ r : Bool,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
            c.TYPES sourceHt targetHt⟩)
          n (.success (.of r)) n := by
  obtain ⟨fin, hts, strtU, hunroll, hsource, htarget⟩ :=
    SubtypeStaticMatchTrace.static_pair_classes_before_match
      c y sourceFin sourceHts strt dt subStart subFinish
      hsub hnested hlookup
  refine ⟨fin, hts, strtU, hunroll, ?_⟩
  intro sourceHt hsourceMem targetHt htargetMem n
  apply ready_reachable_pair_total c sourceHt targetHt n hready
  · rcases hsource sourceHt hsourceMem with hbase | ⟨p, dtP, hP, heq⟩
    · exact Or.inl hbase
    · exact Or.inr ⟨p, dtP, heq, hP⟩
  · rcases htarget targetHt htargetMem with hbase |
      ⟨dtQ, q, hindex, heq⟩
    · exact Or.inl hbase
    · exact Or.inr (Or.inr ⟨q, dtQ, heq,
        (ReadyMatchHeaptypeIndex.indexOfDeftype_sound
          c.TYPES dtQ q hindex).2.1⟩)

end properties.wasm_module_ok.ReadyMatchReachablePairs
