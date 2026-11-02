import properties.wasm_module_ok.SubstSubtypeListPosition

set_option autoImplicit false

namespace properties.wasm_module_ok.SubtypeResultShape

open properties.wasm_module_not_ok.Rejection

theorem substSubtypeResult_supertype_shape
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (dts : List SpecTec.deftype)
    (st' : SpecTec.subtype)
    (h : substSubtypeResult (.SubT fin hts strt) dts = some st') :
    ∃ hts' : List SpecTec.heaptype,
      ∃ strt' : SpecTec.strtype,
        st' = .SubT fin hts' strt' ∧
        substHeaptypeListResult hts dts = some hts' := by
  cases hhts : substHeaptypeListResult hts dts with
  | none =>
      simp [substSubtypeResult, hhts] at h
  | some hts' =>
      cases hstrt : substStrtypeResult strt dts with
      | none =>
          simp [substSubtypeResult, hhts, hstrt] at h
      | some strt' =>
          simp [substSubtypeResult, hhts, hstrt] at h
          cases h
          exact ⟨hts', strt', rfl, rfl⟩

theorem substSubtypeResult_supertype_position
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (dts : List SpecTec.deftype)
    (st' : SpecTec.subtype) (j : Nat)
    (h : substSubtypeResult (.SubT fin hts strt) dts = some st')
    (hj : j < hts.length) :
    ∃ hts' : List SpecTec.heaptype,
      ∃ strt' : SpecTec.strtype,
      ∃ ht ht' : SpecTec.heaptype,
        st' = .SubT fin hts' strt' ∧
        hts[j]? = some ht ∧ hts'[j]? = some ht' ∧
        substHeaptypeResult ht dts = some ht' := by
  obtain ⟨hts', strt', hshape, hhts⟩ :=
    substSubtypeResult_supertype_shape fin hts strt dts st' h
  obtain ⟨ht, ht', hget, hget', hsubst⟩ :=
    properties.wasm_module_ok.SubstHeaptypeListPosition.substHeaptypeListResult_position
      hts dts hts' j hhts hj
  exact ⟨hts', strt', ht, ht', hshape, hget, hget', hsubst⟩

end properties.wasm_module_ok.SubtypeResultShape
