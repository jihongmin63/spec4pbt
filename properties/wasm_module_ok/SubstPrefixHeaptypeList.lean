import properties.wasm_module_ok.SubstPrefixHeaptype

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstPrefixHeaptypeList

open properties.wasm_module_not_ok.Rejection

theorem substHeaptypeListResult_prefix
    (hts : List SpecTec.heaptype)
    (pref tail : List SpecTec.deftype)
    (result : List SpecTec.heaptype)
    (h : substHeaptypeListResult hts pref = some result) :
    substHeaptypeListResult hts (pref ++ tail) = some result := by
  induction hts generalizing result with
  | nil =>
      simpa [substHeaptypeListResult] using h
  | cons ht hts ih =>
      cases hhead : substHeaptypeResult ht pref with
      | none =>
          simp [substHeaptypeListResult, hhead] at h
      | some ht' =>
          cases hrest : substHeaptypeListResult hts pref with
          | none =>
              simp [substHeaptypeListResult, hhead, hrest] at h
          | some rest' =>
              have hresult : result = ht' :: rest' := by
                simpa [substHeaptypeListResult, hhead, hrest] using h.symm
              subst result
              simp [substHeaptypeListResult,
                SubstPrefixHeaptype.substHeaptypeResult_prefix ht pref tail ht' hhead,
                ih rest' hrest]

end properties.wasm_module_ok.SubstPrefixHeaptypeList
