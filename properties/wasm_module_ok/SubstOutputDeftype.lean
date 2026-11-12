import properties.wasm_module_ok.SubstOutputStrtype

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstOutputDeftype

open properties.wasm_module_not_ok.Rejection

theorem substSubtypeResult_output_fixed
    (st : SpecTec.subtype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.subtype)
    (h : substSubtypeResult st pref = some result) :
    substSubtypeResult result dts = some result := by
  cases st with
  | SubT fin hts strt =>
      cases hh : substHeaptypeListResult hts pref with
      | none => simp [substSubtypeResult, hh] at h
      | some hts' =>
          cases hs : substStrtypeResult strt pref with
          | none => simp [substSubtypeResult, hh, hs] at h
          | some strt' =>
              have hr : result = SpecTec.subtype.SubT fin hts' strt' := by
                simpa [substSubtypeResult, hh, hs] using h.symm
              subst result
              simp [substSubtypeResult,
                SubstOutputHeaptypeList.substHeaptypeListResult_output_fixed
                  hts pref dts hts' hh,
                SubstOutputStrtype.substStrtypeResult_output_fixed
                  strt pref dts strt' hs]

theorem substSubtypeListResult_output_fixed
    (sts : List SpecTec.subtype) (pref dts : List SpecTec.deftype)
    (result : List SpecTec.subtype)
    (h : substSubtypeListResult sts pref = some result) :
    substSubtypeListResult result dts = some result := by
  induction sts generalizing result with
  | nil =>
      have hr : result = [] := by
        simpa [substSubtypeListResult] using h.symm
      subst result
      rfl
  | cons st sts ih =>
      cases hhead : substSubtypeResult st pref with
      | none => simp [substSubtypeListResult, hhead] at h
      | some st' =>
          cases hrest : substSubtypeListResult sts pref with
          | none => simp [substSubtypeListResult, hhead, hrest] at h
          | some sts' =>
              have hr : result = st' :: sts' := by
                simpa [substSubtypeListResult, hhead, hrest] using h.symm
              subst result
              simp [substSubtypeListResult,
                substSubtypeResult_output_fixed st pref dts st' hhead,
                ih sts' hrest]

theorem substRectypeResult_output_fixed
    (rt : SpecTec.rectype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.rectype)
    (h : substRectypeResult rt pref = some result) :
    substRectypeResult result dts = some result := by
  cases rt with
  | RecT sts =>
      cases hs : substSubtypeListResult sts pref with
      | none => simp [substRectypeResult, hs] at h
      | some sts' =>
          have hr : result = SpecTec.rectype.RecT sts' := by
            simpa [substRectypeResult, hs] using h.symm
          subst result
          simp [substRectypeResult,
            substSubtypeListResult_output_fixed sts pref dts sts' hs]

theorem substDeftypeResult_output_fixed
    (dt : SpecTec.deftype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.deftype)
    (h : substDeftypeResult dt pref = some result) :
    substDeftypeResult result dts = some result := by
  cases dt with
  | DefT rt n =>
      cases hr : substRectypeResult rt pref with
      | none => simp [substDeftypeResult, hr] at h
      | some rt' =>
          have hresult : result = SpecTec.deftype.DefT rt' n := by
            simpa [substDeftypeResult, hr] using h.symm
          subst result
          simp [substDeftypeResult,
            substRectypeResult_output_fixed rt pref dts rt' hr]

end properties.wasm_module_ok.SubstOutputDeftype
