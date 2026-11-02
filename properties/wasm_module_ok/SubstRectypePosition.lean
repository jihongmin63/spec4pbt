import properties.wasm_module_ok.RollSubtypePosition

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstRectypePosition

open properties.wasm_module_not_ok.Rejection

theorem substRectypeResult_subtypes
    (sts : List SpecTec.subtype) (dts : List SpecTec.deftype)
    (rect' : SpecTec.rectype)
    (h : substRectypeResult (.RecT sts) dts = some rect') :
    ∃ sts' : List SpecTec.subtype,
      rect' = .RecT sts' ∧
      substSubtypeListResult sts dts = some sts' := by
  cases hsts : substSubtypeListResult sts dts with
  | none =>
      simp [substRectypeResult, hsts] at h
  | some sts' =>
      simp [substRectypeResult, hsts] at h
      cases h
      exact ⟨sts', rfl, rfl⟩

end properties.wasm_module_ok.SubstRectypePosition
