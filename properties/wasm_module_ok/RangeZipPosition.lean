import properties.wasm_module_ok.DescendingSupertypeResult

set_option autoImplicit false

namespace properties.wasm_module_ok.RangeZipPosition

theorem range_zip_source_position
    (sts : List SpecTec.subtype) (i : Nat) (st : SpecTec.subtype)
    (hi : i < sts.length) (hget : sts[i]? = some st) :
    (i, st) ∈ List.zip (List.range sts.length) sts := by
  apply List.mem_iff_getElem?.2
  refine ⟨i, (List.getElem?_zip_eq_some).2 ?_⟩
  exact ⟨List.getElem?_range hi, hget⟩

end properties.wasm_module_ok.RangeZipPosition
