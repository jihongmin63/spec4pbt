import properties.wasm_module_ok.SubstOutputHeaptype

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstOutputHeaptypeList

open properties.wasm_module_not_ok.Rejection

theorem substHeaptypeListResult_output_fixed
    (hts : List SpecTec.heaptype) (pref dts : List SpecTec.deftype)
    (result : List SpecTec.heaptype)
    (h : substHeaptypeListResult hts pref = some result) :
    substHeaptypeListResult result dts = some result := by
  induction hts generalizing result with
  | nil =>
      have hr : result = [] := by
        simpa [substHeaptypeListResult] using h.symm
      subst result
      rfl
  | cons ht hts ih =>
      cases hhead : substHeaptypeResult ht pref with
      | none => simp [substHeaptypeListResult, hhead] at h
      | some ht' =>
          cases hrest : substHeaptypeListResult hts pref with
          | none => simp [substHeaptypeListResult, hhead, hrest] at h
          | some hts' =>
              have hr : result = ht' :: hts' := by
                simpa [substHeaptypeListResult, hhead, hrest] using h.symm
              subst result
              simp [substHeaptypeListResult,
                SubstOutputHeaptype.substHeaptypeResult_output_fixed
                  ht pref dts ht' hhead,
                ih hts' hrest]

end properties.wasm_module_ok.SubstOutputHeaptypeList
