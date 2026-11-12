import properties.wasm_module_ok.ValidatedMatchDeftypeInduction

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstPrefixTypevar

open properties.wasm_module_not_ok.Rejection

theorem substOfResult_prefix
    (tv : SpecTec.typevar)
    (pref tail : List SpecTec.deftype)
    (result : SpecTec.heaptype)
    (h : substOfResult tv pref = some result) :
    substOfResult tv (pref ++ tail) = some result := by
  cases tv with
  | RecX n =>
      simp [substOfResult] at h ⊢
      exact h
  | StatX n =>
      cases hget : pref[n]? with
      | none =>
          simp [substOfResult, hget] at h
      | some dt =>
          have hn : n < pref.length :=
            (List.getElem?_eq_some_iff.mp hget).choose
          simp [substOfResult, hget] at h
          cases h
          simpa [substOfResult, List.getElem?_append_left hn, hget]

end properties.wasm_module_ok.SubstPrefixTypevar
