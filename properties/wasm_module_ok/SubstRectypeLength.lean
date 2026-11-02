import properties.wasm_module_ok.RectypeAppendedShape

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstRectypeLength

open properties.wasm_module_not_ok.Rejection

theorem substSubtypeListResult_length
    (sts : List SpecTec.subtype) (dts : List SpecTec.deftype)
    (sts' : List SpecTec.subtype)
    (h : substSubtypeListResult sts dts = some sts') :
    sts'.length = sts.length := by
  induction sts generalizing sts' with
  | nil =>
      simp [substSubtypeListResult] at h
      cases h
      rfl
  | cons st tl ih =>
      cases hst : substSubtypeResult st dts with
      | none =>
          simp [substSubtypeListResult, hst] at h
      | some st' =>
          cases htl : substSubtypeListResult tl dts with
          | none =>
              simp [substSubtypeListResult, hst, htl] at h
          | some tl' =>
              simp [substSubtypeListResult, hst, htl] at h
              cases h
              simp [ih tl' htl]

theorem substRectypeResult_length
    (sts : List SpecTec.subtype) (dts : List SpecTec.deftype)
    (rect' : SpecTec.rectype)
    (h : substRectypeResult (.RecT sts) dts = some rect') :
    ∃ sts' : List SpecTec.subtype,
      rect' = .RecT sts' ∧ sts'.length = sts.length := by
  cases hsts : substSubtypeListResult sts dts with
  | none =>
      simp [substRectypeResult, hsts] at h
  | some sts' =>
      simp [substRectypeResult, hsts] at h
      cases h
      exact ⟨sts', rfl, substSubtypeListResult_length sts dts sts' hsts⟩

theorem rectype_ok_appended_inner_length
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish) :
    ∃ dts : List SpecTec.deftype,
      c' = {c with TYPES := c.TYPES ++ dts} ∧
      ∀ i, i < sts.length →
        ∃ sts' : List SpecTec.subtype,
          dts[i]? = some (.DefT (.RecT sts') i) ∧
          sts'.length = sts.length := by
  obtain ⟨dts, hc, hpos⟩ :=
    properties.wasm_module_ok.RectypeAppendedShape.rectype_ok_appended_position_shape
      c c' sts start finish h
  refine ⟨dts, hc, ?_⟩
  intro i hi
  obtain ⟨rect', hget, hresult⟩ := hpos i hi
  obtain ⟨sts', hrect, hlen⟩ := substRectypeResult_length
    (rollSubtypes sts c.TYPES.length (sts.length + c.TYPES.length))
    c.TYPES rect' hresult
  subst rect'
  refine ⟨sts', hget, ?_⟩
  simpa [rollSubtypes] using hlen

end properties.wasm_module_ok.SubstRectypeLength
