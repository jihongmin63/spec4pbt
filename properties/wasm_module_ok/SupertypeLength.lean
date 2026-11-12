import properties.wasm_module_ok.RectypeLocalLookup

set_option autoImplicit false

namespace properties.wasm_module_ok.SupertypeLength

open properties.wasm_module_not_ok.Rejection

theorem substHeaptypeListResult_length
    (hts : List SpecTec.heaptype) (dts : List SpecTec.deftype)
    (hts' : List SpecTec.heaptype)
    (h : substHeaptypeListResult hts dts = some hts') :
    hts'.length = hts.length := by
  induction hts generalizing hts' with
  | nil =>
      simp [substHeaptypeListResult] at h
      cases h
      rfl
  | cons ht tl ih =>
      cases hhead : substHeaptypeResult ht dts with
      | none =>
          simp [substHeaptypeListResult, hhead] at h
      | some ht' =>
          cases htail : substHeaptypeListResult tl dts with
          | none =>
              simp [substHeaptypeListResult, hhead, htail] at h
          | some tl' =>
              simp [substHeaptypeListResult, hhead, htail] at h
              cases h
              simp [ih tl' htail]

theorem substSubtypeResult_supers_length
    (fin fin' : SpecTec.final)
    (hts hts' : List SpecTec.heaptype)
    (strt strt' : SpecTec.strtype)
    (dts : List SpecTec.deftype)
    (h : substSubtypeResult (.SubT fin hts strt) dts =
      some (.SubT fin' hts' strt')) :
    hts'.length = hts.length := by
  cases hsupers : substHeaptypeListResult hts dts with
  | none =>
      simp [substSubtypeResult, hsupers] at h
  | some supers =>
      cases hstrt : substStrtypeResult strt dts with
      | none =>
          simp [substSubtypeResult, hsupers, hstrt] at h
      | some strtResult =>
          have hsub :
              SpecTec.subtype.SubT fin supers strtResult =
                .SubT fin' hts' strt' := by
            exact Option.some.inj
              (by simpa [substSubtypeResult, hsupers, hstrt] using h)
          have hsupersEq : supers = hts' := by
            injection hsub with _ hsupersEq _
          rw [← hsupersEq]
          exact substHeaptypeListResult_length hts dts supers hsupers

end properties.wasm_module_ok.SupertypeLength
