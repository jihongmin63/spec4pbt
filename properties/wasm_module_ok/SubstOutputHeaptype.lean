import properties.wasm_module_ok.SubstPrefixCall

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstOutputHeaptype

open properties.wasm_module_not_ok.Rejection

theorem substHeaptypeResult_output_fixed
    (ht : SpecTec.heaptype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.heaptype)
    (h : substHeaptypeResult ht pref = some result) :
    substHeaptypeResult result dts = some result := by
  cases ht <;> try (
    simp only [substHeaptypeResult] at h
    injection h with heq
    subst result
    rfl)
  rename_i tv
  cases tv with
  | RecX n =>
      have hr : result = .VarHT (.RecX n) := by
        simpa [substHeaptypeResult, substOfResult] using h.symm
      subst result
      simp [substHeaptypeResult, substOfResult]
  | StatX n =>
      cases hget : pref[n]? with
      | none => simp [substHeaptypeResult, substOfResult, hget] at h
      | some dt =>
          have hr : result = .DefHT dt := by
            simpa [substHeaptypeResult, substOfResult, hget] using h.symm
          subst result
          simp [substHeaptypeResult]

end properties.wasm_module_ok.SubstOutputHeaptype
