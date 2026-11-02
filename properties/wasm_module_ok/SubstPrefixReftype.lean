import properties.wasm_module_ok.SubstPrefixHeaptypeList

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstPrefixReftype

open properties.wasm_module_not_ok.Rejection

theorem substReftypeResult_prefix
    (rt : SpecTec.reftype)
    (pref tail : List SpecTec.deftype)
    (result : SpecTec.reftype)
    (h : substReftypeResult rt pref = some result) :
    substReftypeResult rt (pref ++ tail) = some result := by
  cases rt with
  | «% %» null ht =>
      cases hht : substHeaptypeResult ht pref with
      | none =>
          simp [substReftypeResult, hht] at h
      | some ht' =>
          have hr : result = SpecTec.reftype.«% %» null ht' := by
            simpa [substReftypeResult, hht] using h.symm
          subst result
          simp [substReftypeResult,
            SubstPrefixHeaptype.substHeaptypeResult_prefix ht pref tail ht' hht]

end properties.wasm_module_ok.SubstPrefixReftype
