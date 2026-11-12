import properties.wasm_module_ok.SubstPrefixStrtype

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstPrefixDeftype

open properties.wasm_module_not_ok.Rejection

theorem substSubtypeResult_prefix
    (st : SpecTec.subtype) (pref tail : List SpecTec.deftype)
    (result : SpecTec.subtype)
    (h : substSubtypeResult st pref = some result) :
    substSubtypeResult st (pref ++ tail) = some result := by
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
                SubstPrefixHeaptypeList.substHeaptypeListResult_prefix
                  hts pref tail hts' hh,
                SubstPrefixStrtype.substStrtypeResult_prefix
                  strt pref tail strt' hs]

theorem substSubtypeListResult_prefix
    (sts : List SpecTec.subtype) (pref tail : List SpecTec.deftype)
    (result : List SpecTec.subtype)
    (h : substSubtypeListResult sts pref = some result) :
    substSubtypeListResult sts (pref ++ tail) = some result := by
  induction sts generalizing result with
  | nil => simpa [substSubtypeListResult] using h
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
                substSubtypeResult_prefix st pref tail st' hhead,
                ih sts' hrest]

theorem substRectypeResult_prefix
    (rt : SpecTec.rectype) (pref tail : List SpecTec.deftype)
    (result : SpecTec.rectype)
    (h : substRectypeResult rt pref = some result) :
    substRectypeResult rt (pref ++ tail) = some result := by
  cases rt with
  | RecT sts =>
      cases hs : substSubtypeListResult sts pref with
      | none => simp [substRectypeResult, hs] at h
      | some sts' =>
          have hr : result = SpecTec.rectype.RecT sts' := by
            simpa [substRectypeResult, hs] using h.symm
          subst result
          simp [substRectypeResult,
            substSubtypeListResult_prefix sts pref tail sts' hs]

theorem substDeftypeResult_prefix
    (dt : SpecTec.deftype) (pref tail : List SpecTec.deftype)
    (result : SpecTec.deftype)
    (h : substDeftypeResult dt pref = some result) :
    substDeftypeResult dt (pref ++ tail) = some result := by
  cases dt with
  | DefT rt n =>
      cases hr : substRectypeResult rt pref with
      | none => simp [substDeftypeResult, hr] at h
      | some rt' =>
          have hresult : result = SpecTec.deftype.DefT rt' n := by
            simpa [substDeftypeResult, hr] using h.symm
          subst result
          simp [substDeftypeResult,
            substRectypeResult_prefix rt pref tail rt' hr]

end properties.wasm_module_ok.SubstPrefixDeftype
