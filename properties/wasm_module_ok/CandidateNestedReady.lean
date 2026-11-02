import properties.wasm_module_ok.ValidatedNestedReferences
import properties.wasm_module_ok.CandidateRectypeTable

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateNestedReady

open properties.wasm_module_not_ok.Rejection

def nestedIndexed (c : SpecTec.context) (ht : SpecTec.heaptype) : Bool :=
  if ht ∈ HeaptypeValidation.baseHeaptypes then true
  else
    match ht with
    | .DefHT dt => (ReadyMatchHeaptypeIndex.indexOfDeftype c.TYPES dt).isSome
    | _ => false

theorem nestedIndexed_true_iff
    (c : SpecTec.context) (ht : SpecTec.heaptype) :
    nestedIndexed c ht = true ↔
      ht ∈ HeaptypeValidation.baseHeaptypes ∨
        ∃ k : Nat, ∃ dt : SpecTec.deftype,
          c.TYPES[k]? = some dt ∧ ht = .DefHT dt := by
  by_cases hbase : ht ∈ HeaptypeValidation.baseHeaptypes
  · simp [nestedIndexed, hbase]
  · cases ht <;> simp [nestedIndexed, HeaptypeValidation.baseHeaptypes]
    case DefHT dt =>
      constructor
      · intro h
        cases hsearch : ReadyMatchHeaptypeIndex.indexOfDeftype c.TYPES dt with
        | none => simp [hsearch] at h
        | some k =>
            obtain ⟨_, hlookup, _⟩ :=
              ReadyMatchHeaptypeIndex.indexOfDeftype_sound c.TYPES dt k hsearch
            exact ⟨k, hlookup⟩
      · rintro ⟨k, hlookup⟩
        obtain ⟨j, hsearch⟩ :=
          ReadyMatchHeaptypeIndex.indexOfDeftype_complete c.TYPES dt
            (List.mem_iff_getElem?.mpr ⟨k, hlookup⟩)
        simp [hsearch]

def nestedEntryReady (c : SpecTec.context) (p : Nat) : Bool :=
  match c.TYPES[p]? with
  | none => false
  | some dt =>
      match unrollDeftypeResult dt with
      | none => false
      | some (.SubT _ _ strt) =>
          (ReadyMatchReachability.sourceHeaptypes strt).all
            (nestedIndexed c)

def nestedTableReady (c : SpecTec.context) : Bool :=
  (List.range c.TYPES.length).all (nestedEntryReady c)

theorem nestedTableReady_true_iff
    (c : SpecTec.context) :
    nestedTableReady c = true ↔
      ∀ p : Nat, p < c.TYPES.length →
        ∃ dt : SpecTec.deftype,
        ∃ fin : SpecTec.final,
        ∃ hts : List SpecTec.heaptype,
        ∃ strt : SpecTec.strtype,
          c.TYPES[p]? = some dt ∧
          unrollDeftypeResult dt = some (.SubT fin hts strt) ∧
          ∀ ht, ht ∈ ReadyMatchReachability.sourceHeaptypes strt →
            ht ∈ HeaptypeValidation.baseHeaptypes ∨
              ∃ k : Nat, ∃ dtK : SpecTec.deftype,
                c.TYPES[k]? = some dtK ∧ ht = .DefHT dtK := by
  constructor
  · intro htable p hp
    have hentry : nestedEntryReady c p = true :=
      (List.all_eq_true.mp htable) p (List.mem_range.mpr hp)
    obtain ⟨dt, hlookup⟩ :
        ∃ dt : SpecTec.deftype, c.TYPES[p]? = some dt := by
      exact ⟨c.TYPES[p], List.getElem?_eq_getElem hp⟩
    simp only [nestedEntryReady, hlookup] at hentry
    cases hunroll : unrollDeftypeResult dt with
    | none => simp [hunroll] at hentry
    | some st =>
        cases st with
        | SubT fin hts strt =>
            refine ⟨dt, fin, hts, strt, hlookup, hunroll, ?_⟩
            intro ht hmem
            have hall :
                (ReadyMatchReachability.sourceHeaptypes strt).all
                  (nestedIndexed c) = true := by
              simpa [hunroll] using hentry
            exact (nestedIndexed_true_iff c ht).mp
              ((List.all_eq_true.mp hall) ht hmem)
  · intro hpositions
    apply List.all_eq_true.mpr
    intro p hmem
    have hp : p < c.TYPES.length := List.mem_range.mp hmem
    obtain ⟨dt, fin, hts, strt, hlookup, hunroll, hrefs⟩ :=
      hpositions p hp
    simp only [nestedEntryReady, hlookup, hunroll]
    apply List.all_eq_true.mpr
    intro ht hmemHt
    exact (nestedIndexed_true_iff c ht).mpr (hrefs ht hmemHt)

theorem candidate_nested_searchable
    (c : SpecTec.context) (p : Nat)
    (hready : nestedTableReady c = true)
    (hp : p < c.TYPES.length) :
    ∃ dt : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strt : SpecTec.strtype,
      c.TYPES[p]? = some dt ∧
      unrollDeftypeResult dt = some (.SubT fin hts strt) ∧
      ∀ ht, ht ∈ ReadyMatchReachability.sourceHeaptypes strt →
        ht ∈ HeaptypeValidation.baseHeaptypes ∨
          ∃ dtK : SpecTec.deftype, ∃ k : Nat,
            ReadyMatchHeaptypeIndex.indexOfDeftype c.TYPES dtK = some k ∧
            ht = .DefHT dtK := by
  obtain ⟨dt, fin, hts, strt, hlookup, hunroll, hcases⟩ :=
    (nestedTableReady_true_iff c).mp hready p hp
  refine ⟨dt, fin, hts, strt, hlookup, hunroll, ?_⟩
  intro ht hmem
  rcases hcases ht hmem with hbase | ⟨k, dtK, hget, hht⟩
  · exact Or.inl hbase
  · obtain ⟨first, hfound⟩ :=
      ReadyMatchHeaptypeIndex.indexOfDeftype_complete c.TYPES dtK
        (List.mem_iff_getElem?.mpr ⟨k, hget⟩)
    exact Or.inr ⟨dtK, first, hfound, hht⟩

theorem rectype_success_nestedTableReady
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    nestedTableReady result = true := by
  apply (nestedTableReady_true_iff result).2
  intro p hp
  exact ValidatedNestedReferences.validated_type_unrolled_nested_references
    result p
    (ValidatedTypeChain.ValidatedTypes.append
      c result sts start finish hc hrect) hp

theorem rectype_success_candidate_nested_ready
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    ∃ candidate,
      CandidateRectypeTable.candidateContext c sts = some candidate ∧
      nestedTableReady candidate = true := by
  exact ⟨result,
    CandidateRectypeTable.rectype_success_candidateContext
      c result sts start finish hrect,
    rectype_success_nestedTableReady c result sts start finish hc hrect⟩

end properties.wasm_module_ok.CandidateNestedReady
