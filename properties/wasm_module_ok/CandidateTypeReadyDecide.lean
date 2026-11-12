import properties.wasm_module_ok.CandidateTypeReady

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateTypeReadyDecide

open properties.wasm_module_not_ok.Rejection

def headReady (c : SpecTec.context) (p : Nat) :
    SpecTec.heaptype → Bool
  | .DefHT dtK =>
      (List.range p).any fun k => decide (c.TYPES[k]? = some dtK)
  | _ => false

def entryReady (c : SpecTec.context) (p : Nat) : Bool :=
  match c.TYPES[p]? with
  | none => false
  | some dt =>
      decide (substDeftypeResult dt c.TYPES = some dt) &&
        match unrollDeftypeResult dt with
        | none => false
        | some (.SubT _ hts _) => hts.all (headReady c p)

/-- A finite pure check; it does not evaluate translated matching calls. -/
def tableReady (c : SpecTec.context) : Bool :=
  (List.range c.TYPES.length).all (entryReady c)

private theorem headReady_true_iff
    (c : SpecTec.context) (p : Nat) (ht : SpecTec.heaptype) :
    headReady c p ht = true ↔
      ∃ k : Nat, ∃ dtK : SpecTec.deftype,
        k < p ∧ c.TYPES[k]? = some dtK ∧ ht = .DefHT dtK := by
  cases ht <;>
    simp [headReady, List.any_eq_true, List.mem_range, decide_eq_true_eq]

theorem tableReady_true_iff_ready
    (c : SpecTec.context) :
    tableReady c = true ↔ CandidateTypeReady.Ready c := by
  constructor
  · intro htable
    have hentry : ∀ p, p < c.TYPES.length → entryReady c p = true := by
      intro p hp
      exact (List.all_eq_true.mp htable) p (List.mem_range.mpr hp)
    constructor
    · intro p dt hlookup
      have hp : p < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hlookup).choose
      have h := hentry p hp
      simp only [entryReady, hlookup, Bool.and_eq_true] at h
      exact of_decide_eq_true h.1
    · intro p hp
      let dt : SpecTec.deftype := c.TYPES[p]
      have hlookup : c.TYPES[p]? = some dt :=
        List.getElem?_eq_getElem hp
      have h := hentry p hp
      simp only [entryReady, hlookup, Bool.and_eq_true] at h
      cases hunroll : unrollDeftypeResult dt with
      | none =>
          simp [hunroll] at h
      | some st =>
          cases st with
          | SubT fin hts strt =>
              have hall : hts.all (headReady c p) = true := by
                simpa [hunroll] using h.2
              refine ⟨dt, fin, hts, strt, hlookup, hunroll, ?_⟩
              intro j hj
              have hget : hts[j]? = some hts[j] :=
                List.getElem?_eq_getElem hj
              have hmem : hts[j] ∈ hts :=
                List.mem_iff_getElem?.mpr ⟨j, hget⟩
              obtain ⟨k, dtK, hkp, hlookupK, hht⟩ :=
                (headReady_true_iff c p hts[j]).mp
                  ((List.all_eq_true.mp hall) hts[j] hmem)
              refine ⟨k, dtK, hkp, hlookupK, ?_⟩
              simpa [hht] using hget
  · intro hready
    apply List.all_eq_true.mpr
    intro p hmem
    have hp : p < c.TYPES.length := List.mem_range.mp hmem
    obtain ⟨dt, fin, hts, strt, hlookup, hunroll, hedges⟩ :=
      hready.unrolledPredecessors p hp
    have hsubst := hready.substitution p dt hlookup
    simp only [entryReady, hlookup, hsubst, decide_true,
      Bool.true_and, hunroll]
    apply List.all_eq_true.mpr
    intro ht hmemHt
    obtain ⟨j, hget⟩ := List.mem_iff_getElem?.mp hmemHt
    have hj : j < hts.length :=
      (List.getElem?_eq_some_iff.mp hget).choose
    obtain ⟨k, dtK, hkp, hlookupK, hgetK⟩ := hedges j hj
    have hht : ht = .DefHT dtK :=
      Option.some.inj (hget.symm.trans hgetK)
    exact (headReady_true_iff c p ht).2
      ⟨k, dtK, hkp, hlookupK, hht⟩

end properties.wasm_module_ok.CandidateTypeReadyDecide
