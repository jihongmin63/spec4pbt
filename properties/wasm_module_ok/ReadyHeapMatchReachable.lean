import properties.wasm_module_ok.ReadyHeapMatch
import properties.wasm_module_ok.ReadyMatchReversePairs
import properties.wasm_module_ok.MatchStrtypeLocal

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyHeapMatchReachable

private theorem package_result
    (c : SpecTec.context) (source target : SpecTec.heaptype)
    (n : Nat) (r : Bool)
    (hsupport : ReadyHeapMatch.readyHeapMatch c source target = some r)
    (heval : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES source target⟩)
      n (.success (.of ((ReadyHeapMatch.readyHeapMatch c source target).getD false))) n) :
    ∃ value : Bool,
      ReadyHeapMatch.readyHeapMatch c source target = some value ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES source target⟩)
        n (.success (.of value)) n := by
  exact ⟨r, hsupport, by simpa [hsupport] using heval⟩

/-- The forward nested structural pair classes have an exact executable
result, rather than merely an existential evaluator result. -/
theorem ready_reachable_pair_result
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
      ReadyHeapMatch.readyHeapMatch c source target = some r ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES source target⟩)
        n (.success (.of r)) n := by
  rcases hsource with hbase | ⟨p, dtP, rfl, hP⟩
  · rcases htarget with htargetBase |
      ⟨q, dtQ, rfl, hQ⟩ | ⟨q, dtQ, rfl, hQ⟩
    · exact package_result c source target n
        (ReadyHeapMatchBase.baseMatch source target)
        (ReadyHeapMatch.readyHeapMatch_base_base c source target hbase htargetBase)
        (ReadyHeapMatch.readyHeapMatch_base_base_eval c source target n hbase htargetBase)
    · exact package_result c source (.VarHT (.StatX q)) n
        ((ReadyHeapMatch.baseIndexedMatch source dtQ).getD false)
        (ReadyHeapMatch.readyHeapMatch_base_statx c q dtQ source hQ hbase)
        (ReadyHeapMatch.readyHeapMatch_base_statx_eval
          c q n dtQ source hready hQ hbase)
    · exact package_result c source (.DefHT dtQ) n
        ((ReadyHeapMatch.baseIndexedMatch source dtQ).getD false)
        (ReadyHeapMatch.readyHeapMatch_base_def c q dtQ source hQ hbase)
        (ReadyHeapMatch.readyHeapMatch_base_def_eval
          c q n dtQ source hready hQ hbase)
  · rcases htarget with htargetBase |
      ⟨q, dtQ, rfl, hQ⟩ | ⟨q, dtQ, rfl, hQ⟩
    · exact package_result c (.VarHT (.StatX p)) target n
        (ReadyHeapMatchDefBase.readyDefBaseMatch dtP target)
        (ReadyHeapMatch.readyHeapMatch_statx_base c p dtP target hP htargetBase)
        (ReadyHeapMatch.readyHeapMatch_statx_base_eval
          c p n dtP target hready hP htargetBase)
    · have hp : p < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hP).1
      have hq : q < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hQ).1
      exact package_result c (.VarHT (.StatX p)) (.VarHT (.StatX q)) n
        (ValidatedMatchIndexFuel.matchIndex c p q)
        (ReadyHeapMatch.readyHeapMatch_statx_statx c p q)
        (ReadyHeapMatch.readyHeapMatch_statx_statx_eval
          c p q n dtP dtQ hready hp hq hP hQ)
    · have hp : p < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hP).1
      have hq : q < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hQ).1
      exact package_result c (.VarHT (.StatX p)) (.DefHT dtQ) n
        (ValidatedMatchIndexFuel.matchIndex c p q)
        (ReadyHeapMatch.readyHeapMatch_statx_def
          c p q n dtP dtQ hready hp hq hP hQ)
        (ReadyHeapMatch.readyHeapMatch_statx_def_eval
          c p q n dtP dtQ hready hp hq hP hQ)

/-- The reverse nested structural pair classes use the same pure Boolean. -/
theorem ready_reverse_pair_result
    (c : SpecTec.context) (source target : SpecTec.heaptype)
    (n : Nat) (hready : CandidateTypeReady.Ready c)
    (hsource : source ∈ HeaptypeValidation.baseHeaptypes ∨
      ∃ (q : Nat) (dt : SpecTec.deftype),
        source = .DefHT dt ∧ c.TYPES[q]? = some dt)
    (htarget : target ∈ HeaptypeValidation.baseHeaptypes ∨
      ∃ (p : Nat) (dt : SpecTec.deftype),
        target = .VarHT (.StatX p) ∧ c.TYPES[p]? = some dt) :
    ∃ r : Bool,
      ReadyHeapMatch.readyHeapMatch c source target = some r ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES source target⟩)
        n (.success (.of r)) n := by
  rcases hsource with hbase | ⟨q, dtQ, rfl, hQ⟩
  · rcases htarget with htargetBase | ⟨p, dtP, rfl, hP⟩
    · exact package_result c source target n
        (ReadyHeapMatchBase.baseMatch source target)
        (ReadyHeapMatch.readyHeapMatch_base_base c source target hbase htargetBase)
        (ReadyHeapMatch.readyHeapMatch_base_base_eval c source target n hbase htargetBase)
    · exact package_result c source (.VarHT (.StatX p)) n
        ((ReadyHeapMatch.baseIndexedMatch source dtP).getD false)
        (ReadyHeapMatch.readyHeapMatch_base_statx c p dtP source hP hbase)
        (ReadyHeapMatch.readyHeapMatch_base_statx_eval
          c p n dtP source hready hP hbase)
  · rcases htarget with htargetBase | ⟨p, dtP, rfl, hP⟩
    · exact package_result c (.DefHT dtQ) target n
        (ReadyHeapMatchDefBase.readyDefBaseMatch dtQ target)
        (ReadyHeapMatch.readyHeapMatch_def_base c q dtQ target hQ htargetBase)
        (ReadyHeapMatch.readyHeapMatch_def_base_eval
          c q n dtQ target hready hQ htargetBase)
    · have hq : q < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hQ).1
      have hp : p < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hP).1
      exact package_result c (.DefHT dtQ) (.VarHT (.StatX p)) n
        (ValidatedMatchIndexFuel.matchIndex c q p)
        (ReadyHeapMatch.readyHeapMatch_def_statx
          c q p n dtQ dtP hready hq hp hQ hP)
        (ReadyHeapMatch.readyHeapMatch_def_statx_eval
          c q p n dtQ dtP hready hq hp hQ hP)

/-- A prevalidated subtype and a nested-ready type table determine the exact
translated structural match result through the safe heap classifier. -/
theorem static_structural_match_result
    (c : SpecTec.context) (y : SpecTec.typeidx)
    (sourceFin : SpecTec.final) (sourceHts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (dt : SpecTec.deftype)
    (subStart subFinish n : Nat)
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
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_strtype» c.TYPES strt strtU⟩)
        n (.success (.of
          (MatchStrtypeConditional.strMatch
            (fun h1 h2 => (ReadyHeapMatch.readyHeapMatch c h1 h2).getD false)
            strt strtU))) n := by
  obtain ⟨fin, hts, strtU, hunroll, hsource, htarget⟩ :=
    SubtypeStaticMatchTrace.static_pair_classes_before_match
      c y sourceFin sourceHts strt dt subStart subFinish
      hsub hnested hlookup
  let heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool :=
    fun h1 h2 => (ReadyHeapMatch.readyHeapMatch c h1 h2).getD false
  have hsourceClass : ∀ ht,
      ht ∈ ReadyMatchReachability.sourceHeaptypes strt →
      ht ∈ HeaptypeValidation.baseHeaptypes ∨
        ∃ (p : Nat) (dtP : SpecTec.deftype),
          ht = .VarHT (.StatX p) ∧ c.TYPES[p]? = some dtP := by
    intro ht hmem
    rcases hsource ht hmem with hbase | ⟨p, dtP, hP, heq⟩
    · exact Or.inl hbase
    · exact Or.inr ⟨p, dtP, heq, hP⟩
  have htargetClass : ∀ ht,
      ht ∈ ReadyMatchReachability.sourceHeaptypes strtU →
      ht ∈ HeaptypeValidation.baseHeaptypes ∨
        ∃ (q : Nat) (dtQ : SpecTec.deftype),
          ht = .DefHT dtQ ∧ c.TYPES[q]? = some dtQ := by
    intro ht hmem
    rcases htarget ht hmem with hbase | ⟨dtQ, q, hindex, heq⟩
    · exact Or.inl hbase
    · exact Or.inr ⟨q, dtQ, heq,
        (ReadyMatchHeaptypeIndex.indexOfDeftype_sound
          c.TYPES dtQ q hindex).2.1⟩
  refine ⟨fin, hts, strtU, hunroll, ?_⟩
  apply MatchStrtypeLocal.match_strtype_total_of_local_heap_at
    c.TYPES heapMatch strt strtU n
  · intro h1 h2 hmem1 hmem2
    have htargetForward :
        h2 ∈ HeaptypeValidation.baseHeaptypes ∨
          (∃ (q : Nat) (dtQ : SpecTec.deftype),
            h2 = .VarHT (.StatX q) ∧ c.TYPES[q]? = some dtQ) ∨
          (∃ (q : Nat) (dtQ : SpecTec.deftype),
            h2 = .DefHT dtQ ∧ c.TYPES[q]? = some dtQ) := by
      rcases htargetClass h2 hmem2 with hbase | hdef
      · exact Or.inl hbase
      · exact Or.inr (Or.inr hdef)
    obtain ⟨r, hresult, heval⟩ :=
      ready_reachable_pair_result c h1 h2 n hready
        (hsourceClass h1 hmem1) htargetForward
    simpa [heapMatch, hresult] using heval
  · intro h2 h1 hmem2 hmem1
    obtain ⟨r, hresult, heval⟩ :=
      ready_reverse_pair_result c h2 h1 n hready
        (htargetClass h2 hmem2) (hsourceClass h1 hmem1)
    simpa [heapMatch, hresult] using heval

end properties.wasm_module_ok.ReadyHeapMatchReachable
