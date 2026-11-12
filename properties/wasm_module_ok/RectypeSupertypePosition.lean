import properties.wasm_module_ok.SubstRectypePosition

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeSupertypePosition

open properties.wasm_module_not_ok.Rejection

theorem rectype_subst_supertype_position
    (sts : List SpecTec.subtype) (dts : List SpecTec.deftype)
    (rect' : SpecTec.rectype) (x y i j : Nat)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (hresult : substRectypeResult (.RecT (rollSubtypes sts x y)) dts = some rect')
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hj : j < hts.length) :
    ∃ sts' : List SpecTec.subtype,
      ∃ hts' : List SpecTec.heaptype,
      ∃ strt' : SpecTec.strtype,
      ∃ ht ht' : SpecTec.heaptype,
        rect' = .RecT sts' ∧
        sts'[i]? = some (.SubT fin hts' strt') ∧
        (rollHeaptypes hts x y)[j]? = some ht ∧
        hts'[j]? = some ht' ∧
        substHeaptypeResult ht dts = some ht' := by
  obtain ⟨sts', hrect, hsub⟩ :=
    properties.wasm_module_ok.SubstRectypePosition.substRectypeResult_subtypes
      (rollSubtypes sts x y) dts rect' hresult
  have hrolled :=
    properties.wasm_module_ok.RollSubtypePosition.rollSubtypes_get?_source
      sts x y i fin hts strt hsource
  have hirolled : i < (rollSubtypes sts x y).length := by
    simpa [rollSubtypes] using hi
  have hjrolled : j < (rollHeaptypes hts x y).length := by
    simpa [rollHeaptypes] using hj
  obtain ⟨hts', strt', ht, ht', hget, hht, hht', hsubst⟩ :=
    properties.wasm_module_ok.SubtypeListSupertypePosition.substSubtypeListResult_supertype_position
      (rollSubtypes sts x y) sts' dts i j fin
      (rollHeaptypes hts x y) (rollStrtype strt x y)
      hsub hirolled hrolled hjrolled
  exact ⟨sts', hts', strt', ht, ht', hrect, hget, hht, hht', hsubst⟩

end properties.wasm_module_ok.RectypeSupertypePosition
