import properties.wasm_module_ok.CandidateTypeReady
import properties.wasm_module_ok.SubstPrefixDeftype

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateTypeReadyExtension

open properties.wasm_module_not_ok.Rejection

/-- A ready prefix stays ready after appending new type entries, provided
the new entries satisfy the same fixed-substitution and predecessor conditions
in the full table. -/
theorem ready_append
    (c : SpecTec.context) (tail : List SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hnewSub : ∀ (p : Nat) (dt : SpecTec.deftype),
      c.TYPES.length ≤ p →
      (c.TYPES ++ tail)[p]? = some dt →
      substDeftypeResult dt (c.TYPES ++ tail) = some dt)
    (hnewEdges : ∀ p, c.TYPES.length ≤ p →
      p < (c.TYPES ++ tail).length →
      ∃ dt : SpecTec.deftype,
      ∃ fin : SpecTec.final,
      ∃ hts : List SpecTec.heaptype,
      ∃ strt : SpecTec.strtype,
        (c.TYPES ++ tail)[p]? = some dt ∧
        unrollDeftypeResult dt = some (.SubT fin hts strt) ∧
        ∀ j, j < hts.length →
          ∃ k : Nat, ∃ dtK : SpecTec.deftype,
            k < p ∧ (c.TYPES ++ tail)[k]? = some dtK ∧
            hts[j]? = some (.DefHT dtK)) :
    CandidateTypeReady.Ready
      {c with TYPES := c.TYPES ++ tail} := by
  constructor
  · intro p dt hlookup
    by_cases hp : p < c.TYPES.length
    · have hlookupOld : c.TYPES[p]? = some dt := by
        simpa [List.getElem?_append_left hp] using hlookup
      exact SubstPrefixDeftype.substDeftypeResult_prefix
        dt c.TYPES tail dt (hready.substitution p dt hlookupOld)
    · exact hnewSub p dt (by omega) hlookup
  · intro p hpFull
    by_cases hp : p < c.TYPES.length
    · obtain ⟨dt, fin, hts, strt, hlookup, hunroll, hedges⟩ :=
        hready.unrolledPredecessors p hp
      refine ⟨dt, fin, hts, strt, ?_, hunroll, ?_⟩
      · simpa [List.getElem?_append_left hp] using hlookup
      · intro j hj
        obtain ⟨k, dtK, hkp, hlookupK, hget⟩ := hedges j hj
        refine ⟨k, dtK, hkp, ?_, hget⟩
        have hk : k < c.TYPES.length := by omega
        simpa [List.getElem?_append_left hk] using hlookupK
    · exact hnewEdges p (by omega) hpFull

end properties.wasm_module_ok.CandidateTypeReadyExtension
